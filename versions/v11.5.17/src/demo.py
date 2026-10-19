import sys, random, time, math
sys.path.insert(0, '/home/claude/auditor')
import gmpy2
import auditor as A
rng = random.Random(2026)
SP = [3,5,7,11,13,17,19,23,29,31,37,41,43,47]
def make(r, zval):
    Ac = (1 << r) + zval
    while True:
        p = int(gmpy2.next_prime(rng.randrange(Ac*55//100, Ac*9//10) | 1)); q = 2*Ac - p
        if any(q % s == 0 for s in SP): continue
        if gmpy2.is_prime(q) and p != q: return p*q, min(p, q), max(p, q)
def sparse(w, h): return sum(1 << e for e in rng.sample(range(w), h))
L, r = 1024, 512
hyps = [A.Hyp("dense window |z|<2^200", 'dense', w=200, prior=0.25),
        A.Hyp("sparse C(64,4)", 'sparse', w=64, h=4, prior=0.15),
        A.Hyp("sparse C(300,4)", 'sparse', w=300, h=4, prior=0.15),
        A.Hyp("sparse C(300,6)", 'sparse', w=300, h=6, prior=0.15, jmax=4),
        A.Hyp("sparse C(300,8)", 'sparse', w=300, h=8, prior=0.10, jmax=3),
        A.Hyp("Fermat 2^20 steps", 'fermat', steps=1 << 20, prior=0.10)]
cases = [("A: dense defect |z|<2^200", rng.randrange(-(1 << 200) + 1, 1 << 200)),
         ("B: sparse defect C(300,6)", sparse(300, 6)),
         ("C: sparse defect C(64,4)", sparse(64, 4)),
         ("D: no defect (random-type modulus, z of full size)", rng.randrange(1 << 300, 1 << 480))]
budget = float(sys.argv[1]) if len(sys.argv) > 1 else None
for title, z in cases:
    n, p, q = make(r, z)
    print("\n=== " + title, flush=True)
    res, tp, ta = A.audit(n, hyps, budget=budget)
    ok = res is not None and res[2] in (p, q)
    print(f"  RESULT: {'recovered via ' + res[0] + ' (' + res[1] + ')' if ok else ('WRONG FACTOR' if res else 'no defect found within the plan')}; total predicted {tp:.1f} s, actual {ta:.1f} s", flush=True)
