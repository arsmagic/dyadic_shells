#!/usr/bin/env python3
"""
Benchmarks for dyadic_kz_scan.py (the tables of the draft article).
Requires numpy, sympy, gmpy2.   Usage:
    python3 dyadic_kz_bench.py nullmodel [--quick]   # exact sieve null model, adaptive vs plain primes
    python3 dyadic_kz_bench.py scaling   [--quick]   # 1024-bit planted moduli, families C(w,h)
    python3 dyadic_kz_bench.py primes    [--quick]   # exact tests vs number of sieve primes
    python3 dyadic_kz_bench.py bigw      [--quick]   # windows wider than 255 bits (up to 2048-bit n)
    python3 dyadic_kz_bench.py twoadic               # 2-adic saturation constants by N mod 8
Numbers are statistical: with a different seed/CPU they will differ in the last digits.
"""
import sys, math, random, time, statistics as S
import numpy as np
import gmpy2
sys.path.insert(0, __file__.rsplit('/', 1)[0] if '/' in __file__ else '.')
from dyadic_kz_scan import scan_set, SparseFamily, ODD_PRIMES


def rand_prime(bits, rng):
    return int(gmpy2.next_prime(rng.getrandbits(bits - 1) | (1 << (bits - 2)) | 1))


def semiprime(bits, rng):
    return rand_prime(bits // 2, rng) * rand_prime(bits // 2, rng)


def planted(r, w, h, rng):
    """n = p*q with centre A = 2^r + z, z of weight h inside a w-bit window."""
    z = sum(1 << e for e in rng.sample(range(w), h))
    A = (1 << r) + z
    while True:
        p = rand_prime(r, rng)
        q = 2 * A - p
        if gmpy2.is_prime(q) and p != q:
            return p * q, p, q


def ok(hits, p, q):
    return any({x['p'], x['q']} == {min(p, q), max(p, q)} for x in hits)


def nullmodel(quick):
    rng = random.Random(2026); N = 20 if quick else 60
    fam = SparseFamily(64, 3)
    print(f"Random 128-bit n, C(64,3)={fam.M}, 64-table + 12 odd primes, N={N}")
    for name, ad in (('plain', False), ('adaptive', True)):
        o, p = [], []
        for _ in range(N):
            n = semiprime(128, rng)
            h, st = scan_set(n, ('sparse', fam), ks=(1,), anchors=[64], n_primes=12, adaptive=ad, trace=True)
            assert not h
            o.append(st['trace'][-1]); p.append(st['predicted'][-1])
        print(f"  {name:>8}: observed={S.mean(o):.3f} predicted={S.mean(p):.3f} ratio={S.mean(o)/S.mean(p):.3f}")


def scaling(quick):
    rng = random.Random(77)
    fams = [(64, 3), (128, 3), (64, 4)] + ([] if quick else [(96, 4), (128, 4)])
    print("1024-bit planted moduli, centre 2^512+z, 14 odd primes")
    for (w, h) in fams:
        n, p, q = planted(512, w, h, rng)
        fam = SparseFamily(w, h)
        hits, st = scan_set(n, ('sparse', fam), ks=(1,), anchors=[512], n_primes=14)
        print(f"  w={w:>3} h={h} |Z|={fam.M:>11,} kappa={math.log2(fam.M):5.2f} exact={st['exact_tests']:>4} "
              f"scan={st['seconds']:.2f}s found={ok(hits, p, q)}")


def primes(quick):
    rng = random.Random(9); w, h = (96, 4) if quick else (128, 4)
    fam = SparseFamily(w, h); inst = [planted(512, w, h, rng) for _ in range(4 if quick else 8)]
    print(f"planted 1024-bit, |Z|={fam.M:,} (kappa={math.log2(fam.M):.2f}): exact tests vs number of odd primes")
    for npr in (8, 14, 20, 26, 32):
        ex, fd = [], 0
        for n, p, q in inst:
            hits, st = scan_set(n, ('sparse', fam), ks=(1,), anchors=[512], n_primes=npr)
            ex.append(st['exact_tests']); fd += ok(hits, p, q)
        print(f"  primes={npr:>2}: recovered {fd}/{len(inst)}, mean exact tests={S.mean(ex):.1f}")


def bigw(quick):
    rng = random.Random(3)
    cases = [(512, 300, 3, 34)] + ([] if quick else [(512, 500, 3, 36), (1024, 1000, 3, 44), (512, 300, 4, 42)])
    for (r, w, h, npr) in cases:
        n, p, q = planted(r, w, h, rng); fam = SparseFamily(w, h)
        hits, st = scan_set(n, ('sparse', fam), ks=(1,), anchors=[r], n_primes=npr)
        print(f"  n={n.bit_length()} bits r={r} w={w} h={h} |Z|={fam.M:,} kappa={math.log2(fam.M):.2f} "
              f"primes={npr}: found={ok(hits, p, q)} exact={st['exact_tests']} {st['seconds']:.1f}s")


def twoadic():
    def frac(N, m):
        M = 1 << m; a = np.arange(M, dtype=np.int64)
        sq = np.zeros(M, dtype=bool); sq[(a * a) % M] = True
        return sq[(a * a - N) % M].mean()
    print("fraction of A mod 2^m with A^2 - N a square mod 2^m")
    for N in (3, 5, 7, 9, 1001):
        print(f"  N={N:>4} (mod 8 = {N % 8}): " + "  ".join(f"m={m}:{frac(N, m):.5f}" for m in (4, 6, 8, 12, 16)))


if __name__ == '__main__':
    cmd = sys.argv[1] if len(sys.argv) > 1 else ''
    q = '--quick' in sys.argv
    f = dict(nullmodel=nullmodel, scaling=scaling, primes=primes, bigw=bigw).get(cmd)
    if cmd == 'twoadic':
        twoadic()
    elif f:
        f(q)
    else:
        print(__doc__)
