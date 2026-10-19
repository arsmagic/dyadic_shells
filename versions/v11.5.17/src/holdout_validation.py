import sys, random, time, math
sys.path.insert(0, '/home/claude/auditor')
import gmpy2
import auditor as A
from fpmitm import FPMITM
rng = random.Random(77)
def planted(r, w, h):
    es = sorted(rng.sample(range(w), h)); z = sum(1 << e for e in es); A_ = (1 << r) + z
    sp = [3,5,7,11,13,17,19,23,29,31,37,41,43,47]
    while True:
        p = int(gmpy2.next_prime(rng.randrange(A_*55//100, A_*9//10) | 1)); q = 2*A_ - p
        if any(q % s == 0 for s in sp): continue
        if gmpy2.is_prime(q) and p != q: return p*q, p, q, es
print("HELD-OUT validation of the FP-MITM cost model (constants fitted earlier on other runs)")
print(f"{'case':<34}{'pred s':>8}{'meas s':>8}{'ratio':>7}{'pred cov':>10}{'meas cov':>10}  found")
for (L, w, h, jm) in [(1024, 280, 6, 4), (2048, 560, 5, 3), (1024, 320, 6, 3)]:
    r = L // 2
    n, p, q, es = planted(r, w, h)
    ok, tp, cp = A.est_fpmitm(L, w, h, jm)
    m = FPMITM(n, r, w, h, tol_bits=36, seed=5)
    t0 = time.time(); res = m.search(jmax=jm, stop_on_hit=False); ta = time.time() - t0
    print(f"{f'{L}-bit w={w} h={h} jmax={jm}':<34}{tp:>8.1f}{ta:>8.1f}{tp/ta:>7.2f}{cp:>10.3f}{m.stats['coverage']:>10.3f}  {any(x[1] in (p, q) for x in res)}", flush=True)
