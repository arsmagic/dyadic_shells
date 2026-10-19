#!/usr/bin/env python3
"""
(k, z)-scan v2: shifted-centre, weighted difference-of-squares screen over an
ARBITRARY public set of offsets, with an adaptive odd-prime QR sieve.
Requires Python 3.8+ and numpy (--selftest / --bench additionally use sympy).

Model.  Public anchor 2^r.  For small weights k = a*b and offsets z from a public
set Z, test whether  D = (2^r + z)^2 - k*n  is a perfect square t^2.
If a*p + b*q = 2*(2^r + z) then D = ((a*p - b*q)/2)^2 and gcd(2^r + z -/+ t, n)
reveals p and q (Lehman/Hart-type identity with a dyadic anchor).

Offset sets
    window(zbits)      z in [-2^zbits, 2^zbits)                      (v1 behaviour)
    sparse(w, h)       all z = 2^e1 + ... + 2^eh, 0 <= e1<...<eh < w   (C(w,h) offsets),
                       any w up to 65535; generated lazily in blocks (no C(w,h) array in memory)

Sieve.  For a prime l not dividing k*n, the fraction of centres A mod l for which
A^2 - k*n is a square (or 0) mod l is EXACTLY
        f_l = 1/2 + chi_l(k*n) / (2*l),      chi_l = Legendre symbol.
(Count the solutions of a^2 - y^2 = kn: there are l-1 of them.)  Primes with
chi = -1 filter strongest, so the sieve picks them first ("adaptive").  The
2-adic part is a single table mod 64 and does not improve with more bits.

Soundness: every reported factor d satisfies 1 < d < n and n % d == 0.
A negative result is NOT a proof of anything: it only says nothing was found in Z.
"""
import argparse, sys, time
from itertools import combinations
from math import gcd, isqrt
import numpy as np

ODD_PRIMES = [p for p in range(3, 400) if all(p % d for d in range(2, int(p ** .5) + 1))]


# ---------------------------------------------------------------- offset sets
def window_offsets(zbits):
    """Contiguous window z in [-2^zbits, 2^zbits), represented lazily as ('range', lo, hi)."""
    return ('range', -(1 << zbits), 1 << zbits)


def sparse_combos(w, h):
    """Dense uint16 array (C(w,h), h) of exponent tuples.  Only for small C(w,h);
    use SparseFamily for large families."""
    assert w <= 65535
    from math import comb
    c = comb(w, h)
    flat = np.fromiter((e for t in combinations(range(w), h) for e in t), dtype=np.uint16, count=c * h)
    return flat.reshape(c, h)


class SparseFamily:
    """All offsets z = 2^e1 + ... + 2^eh with 0 <= e1 < ... < eh < w, produced lazily.

    The last `tail` exponents come from a precomputed array T of tail-subsets sorted
    lexicographically; the leading h - tail exponents are enumerated in Python.  For a
    head ending in exponent m the admissible tails are exactly the suffix of T whose
    first element exceeds m, found by one table lookup.  Memory is O(|T| + chunk).
    """

    def __init__(self, w, h, tail=None):
        from math import comb
        assert 1 <= h <= w <= 65535
        self.w, self.h = w, h
        self.M = comb(w, h)
        self.tail = min(h, 2) if tail is None else min(h, tail)
        t = self.tail
        self.T = sparse_combos(w, t) if t == h or comb(w, t) <= 20_000_000 else None
        if self.T is None:
            raise ValueError("tail array too large; lower `tail`")
        first = self.T[:, 0].astype(np.int64)
        # start[m] = first row of T whose first exponent is > m
        self.start = np.searchsorted(first, np.arange(-1, w), side='right').astype(np.int64)

    def chunks(self, rows=1_500_000):
        h, t, T, w = self.h, self.tail, self.T, self.w
        if t == h:
            for s0 in range(0, len(T), rows):
                yield T[s0:s0 + rows]
            return
        head_len = h - t
        buf, count = [], 0
        for head in combinations(range(w), head_len):
            lo = self.start[head[-1] + 1]          # tails with first exponent > head[-1]
            n_tail = len(T) - lo
            if n_tail <= 0:
                continue
            blk = np.empty((n_tail, h), dtype=np.uint16)
            blk[:, :head_len] = np.asarray(head, dtype=np.uint16)
            blk[:, head_len:] = T[lo:]
            buf.append(blk); count += n_tail
            if count >= rows:
                yield np.concatenate(buf); buf, count = [], 0
        if buf:
            yield np.concatenate(buf)


# ---------------------------------------------------------------- sieve helpers
def _sq_mask(m):
    sq = np.zeros(m, dtype=bool)
    sq[(np.arange(m, dtype=np.int64) ** 2) % m] = True
    return sq


def _table(m, kn, sq):
    a = np.arange(m, dtype=np.int64)
    return sq[(a * a - (kn % m)) % m]


def choose_moduli(n, k, n_primes, adaptive):
    kn = k * n
    cand = []
    for l in ODD_PRIMES:
        if kn % l == 0:
            continue
        chi = 1 if pow(kn % l, (l - 1) // 2, l) == 1 else -1
        cand.append((l, (l + chi) / (2.0 * l)))
    if adaptive:
        cand.sort(key=lambda t: t[1])
    return cand[:n_primes]          # list of (prime, exact pass fraction)


# ---------------------------------------------------------------- core scan
def scan_set(n, offsets, ks=(1,), anchors=None, n_primes=14, adaptive=True, chunk=1_500_000, trace=False,
             signs=(1,), base_fn=None):
    """offsets: ('sparse', SparseFamily) or ('list', [ints]).  Returns (hits, stats).
    Candidate centres are A = B + sg*z with B = 2^r (or base_fn(r) if given), sg in `signs`.
    signs=(1,-1) scans both 2^r + z and 2^r - z (needed for centres just below a power of two)."""
    assert n > 3 and n % 2 == 1
    rmin = (n.bit_length() + 1) // 2
    if anchors is None:
        anchors = [rmin]
    kind = offsets[0]
    if kind == 'sparse':
        if isinstance(offsets[1], SparseFamily):
            fam = offsets[1]
        else:                                   # legacy: ('sparse', dense_combos, w)
            fam = None
            combos_dense, w = offsets[1], offsets[2]
        if fam is not None:
            M, wmax = fam.M, fam.w
            assert base_fn is not None or wmax <= max(anchors), "window must fit below the anchor (w <= r)"
        else:
            M, wmax = combos_dense.shape[0], w
    elif kind == 'range':
        lo, hi = offsets[1], offsets[2]
        M = hi - lo
        wmax = max(abs(lo), abs(hi)).bit_length() + 1
    else:
        zs = offsets[1]
        M = len(zs)
        wmax = max(abs(z).bit_length() for z in zs) + 1
    sq64 = _sq_mask(64)
    hits, seen = [], set()
    st = dict(M=M, candidates=0, exact_tests=0, seconds=0.0, trace=None, predicted=None)
    t0 = time.time()
    for r in anchors:
      base_val = base_fn(r) if base_fn is not None else (1 << r)
      for sg in signs:
        for k in ks:
            kn = k * n
            mods = choose_moduli(n, k, n_primes, adaptive)
            tabs = [(64, _table(64, kn, sq64))] + [(l, _table(l, kn, _sq_mask(l))) for l, _ in mods]
            pw = {m: np.array([pow(2, e, m) for e in range(max(wmax, 8))], dtype=np.int64) for m, _ in tabs}
            if kind == 'list':
                zarr = {m: np.array([z % m for z in zs], dtype=np.int64) for m, _ in tabs}
            tr = np.zeros(len(tabs) + 1, dtype=np.int64)
            if kind == 'sparse':
                if fam is not None:
                    blocks = fam.chunks(chunk)
                else:
                    blocks = (combos_dense[s0:s0 + chunk] for s0 in range(0, M, chunk))
            else:
                blocks = ((s0, min(M, s0 + chunk)) for s0 in range(0, M, chunk))
            for blk in blocks:
                if kind == 'sparse':
                    n_rows = blk.shape[0]
                else:
                    s0, s1 = blk
                    n_rows = s1 - s0
                idx = np.arange(n_rows, dtype=np.int64)
                tr[0] += n_rows
                for j, (m, tbl) in enumerate(tabs):
                    base = base_val % m
                    if kind == 'sparse':
                        zres = pw[m][blk[idx]].sum(axis=1) % m
                    elif kind == 'range':
                        zres = (lo + s0 + idx) % m
                    else:
                        zres = zarr[m][s0 + idx]
                    keep = tbl[(base + sg * zres) % m]
                    idx = idx[keep]
                    tr[j + 1] += len(idx)
                    if len(idx) == 0:
                        break
                for i in idx:
                    if kind == 'sparse':
                        z = sum(1 << int(e) for e in blk[i])
                    elif kind == 'range':
                        z = lo + s0 + int(i)
                    else:
                        z = zs[s0 + int(i)]
                    z = sg * z
                    A = base_val + z
                    D = A * A - kn
                    st['exact_tests'] += 1
                    if D < 0:
                        continue
                    t = isqrt(D)
                    if t * t != D:
                        continue
                    for d in (gcd(A - t, n), gcd(A + t, n)):
                        if 1 < d < n and d not in seen:
                            seen.add(d)
                            hits.append(dict(r=r, k=k, z=z, p=min(d, n // d), q=max(d, n // d)))
            st['candidates'] += M
            if trace and st['trace'] is None:
                st['trace'] = tr.tolist()
                f = [0.25 if False else None]
                st['predicted'] = [M]
                # 2-adic stage has no closed form here: use the observed fraction, then exact f_l per prime
                obs64 = tr[1] / max(tr[0], 1)
                cur = M * obs64
                st['predicted'].append(cur)
                for l, fl in mods:
                    cur *= fl
                    st['predicted'].append(cur)
    st['seconds'] = time.time() - t0
    return hits, st


def scan(n, kmax=30, zbits=16, rspan=3, n_primes=14):
    """v1-compatible wrapper: contiguous window, all k <= kmax, rspan anchors."""
    rmin = (n.bit_length() + 1) // 2
    return scan_set(n, window_offsets(zbits), ks=range(1, kmax + 1),
                    anchors=range(rmin, rmin + rspan), n_primes=n_primes)


# ---------------------------------------------------------------- CLI
def _selftest():
    import random
    from sympy import isprime, randprime
    random.seed(11)

    def make(bits, a, b, z):
        r = bits // 2
        A = (1 << r) + z
        assert (b == 1 or A % b) and (a == 1 or A % a)
        while True:
            p = randprime(1 << (r - 3), 1 << (r - 1))
            num = 2 * A - a * p
            if num <= 0 or num % b:
                continue
            q = num // b
            if q > 2 and isprime(q) and p != q:
                return p * q, p, q
    print("Self-test (window offsets): a*p + b*q = 2*(2^r + z), 48-bit moduli")
    for (a, b, z) in [(1, 1, 0), (1, 1, 5), (1, 1, -3000), (1, 3, 0), (3, 5, 1233), (3, 5, -777)]:
        ok = 0
        for _ in range(6):
            n, p, q = make(48, a, b, z)
            h, _ = scan(n, kmax=30, zbits=13, rspan=3)
            ok += any({x['p'], x['q']} == {min(p, q), max(p, q)} for x in h)
        print(f"  a={a} b={b} z={z:>6}: recovered {ok}/6")
    print("Self-test (sparse offsets C(40,3)): z of weight 3 in 40 bits, 96-bit moduli")
    combos = SparseFamily(40, 3)
    ok = 0
    for _ in range(6):
        r = 48
        es = random.sample(range(40), 3)
        z = sum(1 << e for e in es)
        A = (1 << r) + z
        while True:
            p = randprime(1 << (r - 3), 1 << (r - 1)); q = 2 * A - p
            if isprime(q) and p != q:
                break
        h, _ = scan_set(p * q, ('sparse', combos), ks=(1,), anchors=[r])
        ok += any({x['p'], x['q']} == {min(p, q), max(p, q)} for x in h)
    print(f"  recovered {ok}/6")
    print("Self-test (w > 255): z of weight 3 inside a 300-bit window, 640-bit moduli")
    fam = SparseFamily(300, 3)
    ok = 0
    for _ in range(3):
        r = 320
        es = random.sample(range(300), 3)
        z = sum(1 << e for e in es)
        A = (1 << r) + z
        while True:
            p = random.getrandbits(r - 1) | (1 << (r - 2)) | 1; q = 2 * A - p
            if isprime(p) and isprime(q):
                break
        h, _ = scan_set(p * q, ('sparse', fam), ks=(1,), anchors=[r])
        ok += any({x['p'], x['q']} == {min(p, q), max(p, q)} for x in h)
    print(f"  recovered {ok}/3")


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('n', nargs='?', type=int)
    ap.add_argument('--kmax', type=int, default=1)
    ap.add_argument('--zbits', type=int, default=0, help='window offsets |z| < 2^zbits (0 = disabled)')
    ap.add_argument('--sparse', nargs=2, type=int, metavar=('W', 'H'), help='all offsets of weight H in W bits')
    ap.add_argument('--anchors', type=int, nargs='*', help='explicit list of r (default: r_min)')
    ap.add_argument('--primes', type=int, default=14)
    ap.add_argument('--no-adaptive', action='store_true')
    ap.add_argument('--selftest', action='store_true')
    a = ap.parse_args()
    if a.selftest:
        _selftest(); return 0
    if a.n is None or not (a.sparse or a.zbits):
        ap.print_help(); return 2
    off = ('sparse', SparseFamily(*a.sparse)) if a.sparse else window_offsets(a.zbits)
    hits, st = scan_set(a.n, off, ks=range(1, a.kmax + 1), anchors=a.anchors, n_primes=a.primes,
                        adaptive=not a.no_adaptive)
    print(f"|Z|={st['M']:,}  candidates={st['candidates']:,}  exact tests={st['exact_tests']}  time={st['seconds']:.2f}s")
    for h in hits:
        print(f"FACTOR FOUND  r={h['r']} k={h['k']} z={h['z']}  p={h['p']}  q={h['q']}")
    if not hits:
        print("No factor found inside the stated set (this is not a proof of anything).")
    return 0 if hits else 1


if __name__ == '__main__':
    sys.exit(main())
