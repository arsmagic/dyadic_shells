#!/usr/bin/env python3
"""Multi-anchor audit: centres A = base + z with |z| < 2^ZBITS, base in
   (i)  c * 2^m  (c odd, c < 256: a run of leading bits followed by zeros; c = 1 gives 2^m),
   (ii) b^r      (b in a short list of small integer bases other than powers of two).
Anchors are restricted to the interval that can contain the centre of a modulus n,
[0.99*sqrt(n), 1.01*2^ceil(bitlen(n)/2)].

Usage: multi_anchor_audit.py keys.json out.json [--controls N] [--limit N] [--zbits 15]
"""
import sys, os, json, time, random, math, hashlib, collections
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gmpy2
from math import isqrt
from dyadic_kz_scan import scan_set

B_LIST = (3, 5, 6, 7, 10, 11, 12, 13, 14, 15, 17, 19, 20, 23, 29, 31)
ZBITS = 15
NPR = 16


def anchors_for(n):
    L = n.bit_length(); k = (L + 1) // 2
    lo = isqrt(n) * 99 // 100; hi = (1 << k) * 101 // 100
    out = {}
    for c in range(1, 256, 2):
        t = c.bit_length()
        for m in range(max(0, k - t - 1), k - t + 3):
            a = c << m
            if lo <= a <= hi:
                out[a] = ('c', c)
    for b in B_LIST:
        a = 1
        while a < lo: a *= b
        while a <= hi:
            out.setdefault(a, ('b', b)); a *= b
    return out


def battery(n, zbits=ZBITS):
    hits, ex, cand, secs = [], 0, 0, 0.0
    for a, lab in anchors_for(n).items():
        h, st = scan_set(n, ('range', -(1 << zbits), 1 << zbits), ks=(1,), anchors=[0],
                         n_primes=NPR, base_fn=lambda r, a=a: a)
        ex += st['exact_tests']; cand += st['candidates']; secs += st['seconds']
        for x in h:
            hits.append(dict(anchor=lab, z=x['z']))
    return hits, ex, cand, secs


def rp(bits, rng): return int(gmpy2.next_prime(rng.getrandbits(bits - 1) | (1 << (bits - 2)) | 1))
SP = [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47]


def planted(L, kind, rng, zbits=ZBITS):
    k = L // 2
    while True:
        if kind == 'c':
            c = rng.randrange(1, 256, 2); t = c.bit_length(); a = c << (k - t)
            if a * 10 < 7 * (1 << k): continue
            lab = ('c', c)
        else:
            b = rng.choice(B_LIST); a = 1
            while a * 10 < 7 * (1 << k): a *= b
            if a > (1 << k): continue
            lab = ('b', b)
        z = rng.randrange(-(1 << zbits) + 1, 1 << zbits); A = a + z
        for _ in range(200000):
            p = int(gmpy2.next_prime(rng.randrange(A * 55 // 100, A * 9 // 10) | 1)); q = 2 * A - p
            if any(q % s == 0 for s in SP): continue
            if gmpy2.is_prime(q) and p != q:
                return p * q, lab


if __name__ == '__main__':
    recs = json.load(open(sys.argv[1])); out_path = sys.argv[2]
    nctl = int(sys.argv[sys.argv.index('--controls') + 1]) if '--controls' in sys.argv else 0
    limit = int(sys.argv[sys.argv.index('--limit') + 1]) if '--limit' in sys.argv else None
    mods = sorted({int(r['n'], 16) for r in recs})
    real = [n for n in mods if n.bit_length() >= 1000 and n % 2 == 1][:limit]
    rng = random.Random(20261005)
    items = [(n, 'real', None) for n in real]
    for i in range(nctl):
        kind = 'c' if i % 3 != 2 else 'b'; L = 1024 if i % 2 == 0 else 2048
        n, lab = planted(L, kind, rng); items.append((n, 'control:' + kind, lab))
    rng.shuffle(items)
    res = dict(real=len(real), anchors_total=0, candidates=0, exact_tests=0, real_hits=[], controls=[], seconds=0.0)
    t0 = time.time(); n_anch = collections.Counter()
    for j, (n, label, lab) in enumerate(items):
        hits, ex, cand, secs = battery(n)
        na = len(anchors_for(n))
        if label == 'real':
            res['anchors_total'] += na; res['candidates'] += cand; res['exact_tests'] += ex
            if hits: res['real_hits'].append(dict(bits=n.bit_length(), digest=hashlib.sha256(str(n).encode()).hexdigest()[:12], hits=hits))
        else:
            res['controls'].append(dict(kind=label, bits=n.bit_length(), planted=list(lab), detected=bool(hits),
                                        found_label=[list(h['anchor']) for h in hits]))
        if j % 100 == 0:
            print(f"[{j}/{len(items)}] {time.time()-t0:.0f}s real_hits={len(res['real_hits'])} "
                  f"controls={sum(c['detected'] for c in res['controls'])}/{len(res['controls'])}", flush=True)
            json.dump(res, open(out_path, 'w'))
    res['seconds'] = time.time() - t0
    json.dump(res, open(out_path, 'w'))
    print('DONE', json.dumps({k: v for k, v in res.items() if k not in ('controls',)}), flush=True)
