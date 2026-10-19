#!/usr/bin/env python3
"""Patterned-prime audit: does the modulus have a prime factor of the form
      p = c*2^m + u   (c odd, 1 <= c < 256, u in [0, 2^UBITS), p has exactly k = bitlen(n)/2 bits)  or
      p = 2^k - u     (u in [1, 2^UBITS)),
i.e. a prime that starts a run of leading bits followed by zeros (or ones) and then a small offset?
Such primes arise when an incremental prime search starts from a fixed, non-random point
(for instance after a failed random-number call).  Test: n mod p == 0, for all primes p of this form.

Usage: patterned_primes_audit.py keys.json out.json [--ubits 16] [--controls N]
"""
import sys, json, time, random, collections, hashlib, os, pickle
import gmpy2

UBITS = int(sys.argv[sys.argv.index('--ubits') + 1]) if '--ubits' in sys.argv else 16


def pattern_primes(k, ubits=UBITS):
    """All primes c*2^m+u (c odd < 256, bitlen(c)+m = k) and 2^k-u, as gmpy2.mpz."""
    out = []
    for c in range(1, 256, 2):
        m = k - c.bit_length()
        if m < 8: continue
        start = gmpy2.mpz(c) << m
        p = gmpy2.next_prime(start - 1) if c > 1 else gmpy2.next_prime(start)   # c=1 is 2^(k-1): top bit only
        lim = start + (1 << ubits)
        while p < lim:
            out.append((p, ('c', c, int(p - start)))); p = gmpy2.next_prime(p)
    top = gmpy2.mpz(1) << k
    p = gmpy2.prev_prime(top)
    while top - p < (1 << ubits):
        out.append((p, ('top', 1, int(top - p)))); p = gmpy2.prev_prime(p)
    return out


if __name__ == '__main__':
    recs = json.load(open(sys.argv[1])); out_path = sys.argv[2]
    nctl = int(sys.argv[sys.argv.index('--controls') + 1]) if '--controls' in sys.argv else 0
    mods = sorted({int(r['n'], 16) for r in recs})
    real = [n for n in mods if n.bit_length() >= 1000 and n % 2 == 1]
    sizes = collections.Counter(n.bit_length() for n in real)
    lists = {}; t0 = time.time()
    for L in sorted(sizes):
        if L % 2 == 0 and L <= 4096 and sizes[L] >= 3 or L in (2048, 3072, 4096, 1024):
            cache = f'pp_cache_L{L}_u{UBITS}.pkl'
            if os.path.exists(cache):
                lists[L] = [(gmpy2.mpz(p), lab) for p, lab in pickle.load(open(cache, 'rb'))]
            else:
                lists[L] = pattern_primes(L // 2)
                pickle.dump([(int(p), lab) for p, lab in lists[L]], open(cache, 'wb'))
            print(f"L={L}: {len(lists[L])} patterned primes of {L//2} bits ({time.time()-t0:.0f}s)", flush=True)
    res = dict(sizes={str(k): v for k, v in sizes.items()}, tested={}, n_candidates={str(L): len(v) for L, v in lists.items()},
               real_hits=[], controls=[])
    mz = gmpy2.mpz
    for n in real:
        L = n.bit_length()
        if L not in lists: continue
        res['tested'][str(L)] = res['tested'].get(str(L), 0) + 1
        nz = mz(n)
        for p, lab in lists[L]:
            if nz % p == 0:
                res['real_hits'].append(dict(bits=L, digest=hashlib.sha256(str(n).encode()).hexdigest()[:12], pattern=lab))
    # planted controls: n = pattern prime * random prime of equal size
    rng = random.Random(7)
    for i in range(nctl):
        L = rng.choice(sorted(lists)); k = L // 2
        p, lab = rng.choice(lists[L])
        while True:
            q = gmpy2.next_prime(rng.getrandbits(k - 1) | (1 << (k - 1)) | 1)
            if q != p: break
        n = int(p * q)
        found = [l for pp, l in lists[L] if mz(n) % pp == 0]
        res['controls'].append(dict(bits=n.bit_length(), planted=list(lab), detected=bool(found)))
    res['seconds'] = time.time() - t0
    json.dump(res, open(out_path, 'w'))
    print(json.dumps({k: v for k, v in res.items() if k != 'controls'}), flush=True)
    print("controls detected:", sum(c['detected'] for c in res['controls']), "/", len(res['controls']))
