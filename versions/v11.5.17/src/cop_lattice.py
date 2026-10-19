import sys, time, random, math
import gmpy2
from math import isqrt
from fpylll import IntegerMatrix, LLL
import sympy

def poly_mul_lin(coeffs, c0):
    """multiply polynomial (list low->high) by (x + c0)"""
    out = [0]*(len(coeffs)+1)
    for i, a in enumerate(coeffs):
        out[i] += a*c0
        out[i+1] += a
    return out

def coppersmith_divisor(N, p0, X, m, t):
    """find integer x0, |x0| < X with gcd(N, p0 + x0) = p ≈ N^(1/2), using polynomials N^(m-i) f^i (i<m) and x^i f^m (i<t)."""
    d = m + t
    fpow = [[1]]                     # f^i
    for i in range(1, m+1): fpow.append(poly_mul_lin(fpow[-1], p0))
    rows = []
    for i in range(m):
        c = [a * N**(m-i) for a in fpow[i]]
        rows.append(c + [0]*(d-len(c)))
    for i in range(t):
        c = [0]*i + fpow[m]
        rows.append(c + [0]*(d-len(c)))
    M = IntegerMatrix.from_matrix([[rows[r][k] * X**k for k in range(d)] for r in range(d)])
    LLL.reduction(M)
    for r in range(min(3, d)):
        v = [M[r, k] for k in range(d)]
        coeffs = []
        ok = True
        for k in range(d):
            if v[k] % X**k != 0: ok = False; break
            coeffs.append(v[k] // X**k)
        if not ok or all(c == 0 for c in coeffs): continue
        x = sympy.Symbol('x')
        P = sympy.Poly(list(reversed(coeffs)), x)
        for fac, _ in P.factor_list()[1]:
            if fac.degree() == 1:
                a, b = fac.all_coeffs()
                if b % a == 0:
                    x0 = -b // a
                    g = math.gcd(N, p0 + int(x0))
                    if 1 < g < N: return int(x0), g
    return None

def rp(bits, rng): return int(gmpy2.next_prime(rng.getrandbits(bits-1) | (1 << (bits-2)) | 1))

def planted_centre(r, zbits, rng, sparse=None):
    while True:
        z = rng.randrange(-(1 << zbits) + 1, 1 << zbits)
        A = (1 << r) + z
        for _ in range(100000):
            p = int(gmpy2.next_prime(rng.randrange(A*55//100, A*9//10) | 1)); q = 2*A - p
            if gmpy2.is_prime(q) and p != q: return p*q, min(p,q), max(p,q), A, z

if __name__ == '__main__':
    rng = random.Random(11)
    r = 512
    print("Coppersmith/Howgrave-Graham baseline: planted centre 2^512 + z (|z| < 2^w), 1024-bit n; p' = A' - sqrt(A'^2 - n) from the anchor A' = 2^512")
    for (m, t) in [(8, 8), (12, 12)]:
        for zbits in (150, 190, 215, 230, 240):
            res = []; tm = []
            for _ in range(3):
                N, p, q, A, z = planted_centre(r, zbits, rng)
                Ap = 1 << r
                p0 = Ap - isqrt(Ap*Ap - N) if Ap*Ap > N else None
                err = abs(p - p0)
                X = int(err * 3 // 2) + 1 if False else 1 << (max(err.bit_length() + 1, 1))   # bound known to the attacker: use the true error scale 2^ceil(log2 err)+1 bits
                t0 = time.time()
                out = coppersmith_divisor(N, p0, X, m, t)
                tm.append(time.time() - t0); res.append(out is not None and out[1] in (p, q))
            print(f"  m=t={m:>2} dim={m+t:>2}  |z|<2^{zbits}: recovered {sum(res)}/3, mean time {sum(tm)/3:5.1f}s, error of p' ~ 2^{err.bit_length()}")
            sys.stdout.flush()
