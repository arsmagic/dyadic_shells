import sys, random, time, math
sys.path.insert(0, '/home/claude/fpm')
import gmpy2
from fpmitm import FPMITM
seed = int(sys.argv[1]); hs = [int(x) for x in sys.argv[2].split(',')]; jmax = int(sys.argv[3]); full = sys.argv[4] == 'full'
rng = random.Random(seed)
def planted(r, w, h):
    es = sorted(rng.sample(range(w), h)); z = sum(1 << e for e in es); A = (1 << r) + z
    while True:
        p = int(gmpy2.next_prime(rng.randrange(A*55//100, A*9//10) | 1)); q = 2*A - p
        if gmpy2.is_prime(q) and p != q: return p*q, p, q, es
r, w = 512, 300
for h in hs:
    n, p, q, es = planted(r, w, h)
    m = FPMITM(n, r, w, h, tol_bits=int(sys.argv[5]) if len(sys.argv) > 5 else 36, seed=seed)
    nM_planted = sum(1 for e in es if e >= m.wU)
    print(f"h={h}: kappa={math.log2(math.comb(w,h)):.1f}  enumeration at 5e7/s would take {math.comb(w,h)/5e7:.2e} s;  planted: {nM_planted} exponent(s) in M zone [{m.wU},{w})", flush=True)
    t0 = time.time()
    import os
    res = m.search(jmax=jmax, verbose=True, stop_on_hit=not full, jmin=int(os.environ.get('JMIN', 0)))
    ok = any(r_[1] in (p, q) for r_ in res)
    print(f"   -> found={ok}  time {time.time()-t0:.1f}s  lookups={m.stats['lookups']:.2e}  matches={m.stats['matches']}  verified={m.stats['verified']}  coverage={m.stats.get('coverage', float('nan')):.4f}", flush=True)
