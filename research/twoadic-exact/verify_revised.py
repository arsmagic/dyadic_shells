#!/usr/bin/env python3
"""Finite-range tests for the manuscript
"Exact two-adic counts for Fermat-type quadratic sieves and the hyperbolic sieve".

These are tests over the finite ranges printed below; they are not proofs.
Run:  python3 verify_revised.py      (pure Python 3, no dependencies)

Notation
  C(N, m)    = #{A mod 2^m : A^2 - N is a square mod 2^m}
  L(N, e, k) = #{k u + v mod 2^e : u v = N mod 2^e}          (Hittmeir's hyperbolic sieve set)
  s(n)       = number of squares modulo 2^n
  E(k)       = #{t mod 2^k : t even, t(t+1) is a square mod 2^k}
"""
import hashlib, sys
from math import gcd

def squares(M):
    S = bytearray(M)
    for y in range(M):
        S[(y * y) % M] = 1
    return S

def C(N, m):
    M = 1 << m; S = squares(M)
    return sum(S[(A * A - N) % M] for A in range(M))

def L(N, e, k):
    M = 1 << e
    return len({(k * u + N * pow(u, -1, M)) % M for u in range(1, M, 2)})

def C_formula(N, m):
    """Theorem 1 of the manuscript."""
    if m <= 2:
        return 2
    r = N % 8
    if r in (3, 7):
        return 2 ** (m - 2)
    if r == 5:
        return 4 if m <= 4 else 2 ** (m - 3)
    if m <= 4:                                   # r == 1
        return 4
    return (2 ** (m - 3) + (16 if m % 2 == 0 else 20)) // 3

def s_formula(n):
    """Number of squares mod 2^n: s(0) = 1, s(n) = (2^n + 9 - (-1)^n)/6 for n >= 1 (Stangl 1996)."""
    return 1 if n == 0 else (2 ** n + 9 - (-1) ** n) // 6

def E_direct(k):
    M = 1 << k; S = squares(M)
    return sum(S[(t * (t + 1)) % M] for t in range(0, M, 2))

failures = 0
def report(name, ok, total, extra=""):
    global failures
    failures += (ok != total)
    print(f"{name}: {ok}/{total} {extra}".rstrip())

src = open(__file__, "rb").read()
print("verify_revised.py sha256:", hashlib.sha256(src).hexdigest())
print("Python", sys.version.split()[0])
print()

# T1. Theorem 1, odd N in [-259, 259], 1 <= m <= 14 (negative N included)
tot = ok = 0
for m in range(1, 15):
    for N in range(-259, 260, 2):
        tot += 1; ok += (C(N, m) == C_formula(N, m))
report("T1  Theorem 1 closed forms, odd N in [-259,259], m=1..14", ok, tot)

# T2. Corollary: pi_m(N) > 1/24 on the same range (exact rational comparison 24*C > 2^m)
tot = ok = 0
for m in range(1, 15):
    for N in range(-259, 260, 2):
        tot += 1; ok += (24 * C(N, m) > 2 ** m)
report("T2  24*C_m(N) > 2^m, same range", ok, tot)

# T3. Reduction to N mod 8 (Proposition 8): C(N,m) == C(N mod 8 representative, m)
tot = ok = 0
for m in range(1, 15):
    for N in range(-259, 260, 2):
        tot += 1; ok += (C(N, m) == C(N % 8, m))
report("T3  C_m(N) = C_m(N mod 8), same range", ok, tot)

# T4. Independent small cases: E(k) by direct enumeration vs s(k-2), k = 1..7
print("T4  E_k by direct enumeration (k=1..7):", [E_direct(k) for k in range(1, 8)])
tot = ok = 0
for k in range(2, 8):
    tot += 1; ok += (E_direct(k) == s_formula(k - 2))
report("    E_k = s(k-2) for k=2..7", ok, tot)
tot = ok = 0
for m in range(3, 15):
    tot += 1; ok += (C(1, m) == 4 * E_direct(m - 2))
report("    C_m(1) = 4 E_(m-2) for m=3..14", ok, tot)

# T5. Count of squares mod 2^n (Stangl): direct vs formula, n = 0..16
tot = ok = 0
for n in range(0, 17):
    tot += 1; ok += (sum(squares(1 << n)) == s_formula(n))
report("T5  s(n) direct = (2^n+9-(-1)^n)/6, n=0..16", ok, tot)

# T6. Theorem 2: |L(N,2^e,k)| = C_e(kN)/2, odd N in [-129,129], k in {1,3,...,15}, e = 1..11
tot = ok = 0
for e in range(1, 12):
    for N in range(-129, 130, 2):
        for k in range(1, 16, 2):
            tot += 1; ok += (2 * L(N, e, k) == C(k * N, e))
report("T6  |L_(N,2^e,k)| = C_e(kN)/2, e=1..11", ok, tot)

# T7. Recursion of Theorem 2 for N = k mod 8: exponent (e mod 2) vs (e+1 mod 2), e = 5..12
pairs = [(1, 1), (9, 1), (3, 3), (11, 3), (5, 5), (13, 5), (7, 7), (15, 7), (17, 1)]
tot = okc = okp = 0
for N, k in pairs:
    for e in range(5, 13):
        a, b = L(N, e, k), L(N, e + 1, k); tot += 1
        okc += (b == 2 * (a - 2 ** (e % 2))); okp += (b == 2 * (a - 2 ** ((e + 1) % 2)))
report("T7  recursion, exponent e mod 2", okc, tot)
print(f"    recursion, exponent (e+1) mod 2 (as printed in arXiv v1): {okp}/{tot}")
print("    explicit values |L_(1,2^e,1)|, e=5..8:", [L(1, e, 1) for e in range(5, 9)],
      "-> L6=2(L5-2)=4, L7=2(L6-1)=6, L8=2(L7-2)=8")

# T8. Hittmeir 2023 Example 4.7 values (arXiv v1, p. 10)
NEX = 17344343992304993085649094809
vals = [L(NEX % 2 ** e, e, 1) for e in range(4, 11)]
print("T8  Example 4.7, |L_(N,2^e,1)| for e=4..10:", vals, "(printed: [2, 4, 4, 6, 8, 14, 24])")
failures += (vals != [2, 4, 4, 6, 8, 14, 24])

# T9. Odd prime powers (Hittmeir Thm 3.5, chi = +1): exponent e mod 2 vs (e+1) mod 2
def Lodd(N, M, k):
    return len({(k * u + N * pow(u, -1, M)) % M for u in range(1, M) if gcd(u, M) == 1})
tot = okc = okp = 0
for r in (3, 5, 7, 11, 13):
    for N in range(1, 40):
        for k in (1, 2, 3):
            if gcd(N * k, r) != 1 or pow(N * pow(k, -1, r), (r - 1) // 2, r) != 1:
                continue
            e = 1
            while r ** (e + 1) <= 30000:
                a, b = Lodd(N, r ** e, k), Lodd(N, r ** (e + 1), k); tot += 1
                okc += (b == a * r - 2 ** (e % 2) * (r - 1))
                okp += (b == a * r - 2 ** ((e + 1) % 2) * (r - 1))
                e += 1
report("T9  odd prime powers r<=13, r^(e+1)<=30000, exponent e mod 2", okc, tot)
print(f"    same steps, exponent (e+1) mod 2 (as printed in arXiv v1): {okp}/{tot}")
print("    r=7, N=2, k=1: |L_(N,7^e,1)|, e=1..3:", [Lodd(2, 7 ** e, 1) for e in (1, 2, 3)], "(printed: 4, 16, 106)")

# T10. Proposition (valuation-one multiplier): count = l^e - l^(e-1), e >= 2
def Codd(K, M):
    S = squares(M)
    return sum(S[(A * A - K) % M] for A in range(M))
tot = ok = 0
for l in (3, 5, 7):
    for n in range(1, 30):
        if n % l == 0:
            continue
        for e in range(2, 7):
            if l ** e > 200000:
                break
            tot += 1; ok += (Codd(l * n, l ** e) == l ** e - l ** (e - 1))
report("T10 v_l(K)=1: count = l^e - l^(e-1), l in {3,5,7}, n<30, e>=2, l^e<=200000", ok, tot)

# T11. Example for l^2 | K (no general formula claimed)
print("T11 example l=3, K=9: proportions e=1..6:",
      [round(Codd(9, 3 ** e) / 3 ** e, 4) for e in range(1, 7)])

print()
print("ALL TESTS PASSED" if failures == 0 else f"FAILURES: {failures}")
