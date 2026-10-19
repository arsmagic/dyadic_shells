import sys, random, time, math
sys.path.insert(0, '/home/claude/fpm')
import gmpy2
from fpmitm import FPMITM
rng = random.Random(9)
def planted(r, w, h):
    es = sorted(rng.sample(range(w), h)); z = sum(1 << e for e in es); A = (1 << r) + z
    sp = [3,5,7,11,13,17,19,23,29,31,37,41,43,47]
    while True:
        p = int(gmpy2.next_prime(rng.randrange(A*55//100, A*9//10) | 1)); q = 2*A - p
        if any(q % s == 0 for s in sp): continue
        if gmpy2.is_prime(q) and p != q: return p*q, p, q, es
r, w = 1024, 600
for h in (4, 5):
    n, p, q, es = planted(r, w, h)
    m = FPMITM(n, r, w, h, tol_bits=36, seed=4)
    print(f"2048-bit n, w={w}, h={h}: kappa={math.log2(math.comb(w,h)):.1f}; enumeration at 5e7/s: {math.comb(w,h)/5e7:.2e} s; lattice range ~0.234*2048={0.234*2048:.0f} < w; U zone [0,{m.wU}), M zone [{m.wU},{w}) ({m.nM} positions)", flush=True)
    t0 = time.time(); res = m.search(jmax=3, verbose=True, stop_on_hit=False)
    ok = any(x[1] in (p, q) for x in res)
    print(f"   -> found={ok}; planted {es}; found {res[0][0] if res else None}; time {time.time()-t0:.1f}s; coverage {m.stats['coverage']:.3f}; lookups {m.stats['lookups']:.2e}; false verifications {m.stats['verified']-len(res)}", flush=True)
