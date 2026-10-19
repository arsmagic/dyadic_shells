#!/usr/bin/env python3
"""Corpus audit with a PRE-SPECIFIED battery (fixed before looking at the data).
Usage: audit.py keys.json out.json [--controls N1024 N2048] [--limit N]
"""
import sys, json, time, random, math, hashlib, collections, os
import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import gmpy2
from math import isqrt
from dyadic_kz_scan import scan_set, SparseFamily, window_offsets

# ---------------- pre-specified battery ----------------
FAM_S1 = SparseFamily(128, 3)    # 341,376 offsets
FAM_S2 = SparseFamily(64, 4)     # 635,376 offsets
ODD_K = (1, 3, 5, 7, 9, 11, 13, 15)
NPR = 24
def battery(n):
    """Pre-specified battery.  Anchors: for each weight k, r_k = ceil(log2(k*n)/2) and the next two
    integers (window family); r and r+1 for the sparse families and Fermat baseline.
    returns list of (name, hits, stats)"""
    rmin = (n.bit_length() + 1) // 2
    res = []
    hits, tot = [], dict(M=0, candidates=0, exact_tests=0, seconds=0.0)
    for k in ODD_K:
        r0 = ((k * n).bit_length() + 1) // 2
        h, st = scan_set(n, window_offsets(16), ks=(k,), anchors=[r0, r0 + 1, r0 + 2], n_primes=NPR)
        hits += h
        for key in ('candidates', 'exact_tests', 'seconds'): tot[key] += st[key]
    res.append(('W16xK8', hits, tot))
    h, st = scan_set(n, ('sparse', FAM_S1), ks=(1,), anchors=[rmin, rmin + 1], signs=(1, -1), n_primes=NPR)
    res.append(('S(128,3)', h, st))
    h, st = scan_set(n, ('sparse', FAM_S2), ks=(1,), anchors=[rmin, rmin + 1], signs=(1, -1), n_primes=NPR)
    res.append(('S(64,4)', h, st))
    h, st = scan_set(n, ('range', 0, 1 << 20), ks=(1,), anchors=[0], n_primes=NPR, base_fn=lambda r: isqrt(n - 1) + 1)
    res.append(('Fermat2^20', h, st))
    return res

# ---------------- batch GCD ----------------
def batch_gcd(ns):
    ns = [gmpy2.mpz(x) for x in ns]
    tree = [ns]
    while len(tree[-1]) > 1:
        lv = tree[-1]
        tree.append([lv[i] * lv[i + 1] if i + 1 < len(lv) else lv[i] for i in range(0, len(lv), 2)])
    rem = [tree[-1][0]]
    for lv in reversed(tree[:-1]):
        rem = [rem[i // 2] % (x * x) for i, x in enumerate(lv)]
    return [int(gmpy2.gcd(r // x, x)) for r, x in zip(rem, ns)]

# ---------------- planted controls ----------------
def rp(bits, rng): return int(gmpy2.next_prime(rng.getrandbits(bits - 1) | (1 << (bits - 2)) | 1))
def planted_control(bits, kind, rng):
    r = bits // 2
    if kind == 'W':          # centre 2^r + z, |z| < 2^16, weights (a,b) odd, k=ab<=15
        a, b = rng.choice([(1, 1), (1, 3), (3, 1), (3, 5), (1, 5), (5, 3), (1, 7), (7, 1)])
        while True:                               # need gcd(a, A) = gcd(b, A) = 1 or no solution exists
            z = rng.randrange(-(1 << 16) + 1, 1 << 16)
            if (a == 1 or ((1 << r) + z) % a) and (b == 1 or ((1 << r) + z) % b):
                break
        sign = 0
    elif kind == 'S3':       # sparse (128,3), either side of 2^r
        a = b = 1; z = sum(1 << e for e in rng.sample(range(128), 3)); sign = rng.choice([1, -1])
    elif kind == 'S4':
        a = b = 1; z = sum(1 << e for e in rng.sample(range(64), 4)); sign = rng.choice([1, -1])
    elif kind == 'F':        # close primes
        p = rp(bits // 2, rng); q = int(gmpy2.next_prime(p + rng.getrandbits(18)))
        return p * q, p, q
    A = (1 << r) + (z if kind == 'W' else sign * z)
    while True:
        p = rp(r, rng)                      # r-1 or r bit prime
        num = 2 * A - a * p
        if num <= 0 or num % b: continue
        q = num // b
        if q > 2 and gmpy2.is_prime(q) and p != q and a * p % q and b * q % p:
            return p * q, p, q

if __name__ == '__main__':
    keys_path, out_path = sys.argv[1], sys.argv[2]
    n1024 = n2048 = 0; limit = None
    if '--controls' in sys.argv:
        i = sys.argv.index('--controls'); n1024, n2048 = int(sys.argv[i + 1]), int(sys.argv[i + 2])
    if '--limit' in sys.argv:
        limit = int(sys.argv[sys.argv.index('--limit') + 1])
    recs = json.load(open(keys_path))
    mods = {}
    for r in recs:
        n = int(r['n'], 16); mods.setdefault(n, []).append(r['id'])
    real = [n for n in mods if n.bit_length() >= 1000 and n % 2 == 1]
    size_hist = collections.Counter(n.bit_length() for n in mods)
    print(f"records={len(recs)} distinct moduli={len(mods)} RSA(>=1000 bit, odd)={len(real)}", flush=True)
    # reuse across ids
    reused = sum(1 for n, ids in mods.items() if len(set(ids)) > 1)
    # batch GCD on distinct moduli
    t = time.time(); g = batch_gcd(real)
    shared = [n for n, d in zip(real, g) if d != 1]
    print(f"batch GCD over {len(real)} moduli: {len(shared)} with a shared factor ({time.time()-t:.1f}s)", flush=True)
    rng = random.Random(20261004)
    items = [(n, 'real', None) for n in real[:limit]]
    for kind in ('W', 'S3', 'S4', 'F'):
        for bits, cnt in ((1024, n1024), (2048, n2048)):
            for _ in range(cnt // 4 + (1 if kind == 'W' and cnt % 4 else 0)):
                n, p, q = planted_control(bits, kind, rng)
                items.append((n, 'control:' + kind, (p, q)))
    rng.shuffle(items)
    out = dict(records=len(recs), distinct=len(mods), rsa=len(real), reused_across_ids=reused,
               size_hist=dict(size_hist), batch_gcd_shared=len(shared), real_hits=[], controls=[], timing={},
               candidates=0, exact_tests=0, scanned_real=0)
    t0 = time.time(); tm = collections.defaultdict(float)
    for j, (n, label, pq) in enumerate(items):
        res = battery(n)
        found = []
        for name, hits, st in res:
            tm[name] += st['seconds']
            out['candidates'] += st['candidates'] if label == 'real' else 0
            out['exact_tests'] += st['exact_tests'] if label == 'real' else 0
            for h in hits:
                assert 1 < h['p'] < n and n % h['p'] == 0
                found.append((name, h['k'], h['z']))
        if label == 'real':
            out['scanned_real'] += 1
            if found:
                out['real_hits'].append(dict(bits=n.bit_length(), battery=sorted({f[0] for f in found}),
                                             digest=hashlib.sha256(str(n).encode()).hexdigest()[:12]))
        else:
            out['controls'].append(dict(kind=label, bits=n.bit_length(), detected=bool(found),
                                        by=sorted({f[0] for f in found})))
        if j % 100 == 0:
            print(f"[{j}/{len(items)}] {time.time()-t0:.0f}s real_hits={len(out['real_hits'])} "
                  f"controls_detected={sum(c['detected'] for c in out['controls'])}/{len(out['controls'])}", flush=True)
            out['timing'] = dict(tm); json.dump(out, open(out_path, 'w'))
    out['timing'] = dict(tm); out['seconds'] = time.time() - t0
    json.dump(out, open(out_path, 'w'))
    print('DONE', json.dumps({k: v for k, v in out.items() if k not in ('size_hist', 'controls')}), flush=True)
