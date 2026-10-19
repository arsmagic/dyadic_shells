#!/usr/bin/env python3
"""
FP-MITM: fractional-part meet-in-the-middle search for a sparse centre offset z.

Setting: n = p*q, centre A = 2^r + z with z = 2^e1 + ... + 2^eh (distinct exponents < w).
The smaller prime is the real number p = F(z) = A - sqrt(A^2 - n) and must be an INTEGER.
Taylor expansion at z = 0:  F(z) = (A0 - B0) - k0*z + c2*z^2 + O(z^3),
    k0 = A0/B0 - 1,  c2 = n / (2*B0^3),  A0 = 2^r,  B0 = sqrt(A0^2 - n).
Expanded over the exponents,  F(z) = F(0) + sum_i phi(e_i) + sum_{i<j} psi(e_i,e_j),
    phi(e) = -k0*2^e + c2*4^e,  psi(e,e') = 2*c2*2^(e+e').
The pair term is below the tolerance 2^-tol whenever e+e' < -log2(2*c2) - tol, so exponents in the
'U zone' [0, wU) are uncoupled with everything, and their contribution is purely additive modulo 1.
Integrality of F(z) is then an additive equality modulo 1 -> hashable -> meet in the middle.
Exponents in the remaining 'M zone' [wU, w) are enumerated (with their pair terms).
All matches are verified exactly (square test + gcd).
"""
import sys, time, math, random
from itertools import combinations
from math import isqrt, comb, gcd
import numpy as np

M64 = (1 << 64) - 1


def combos_array(k, m):
    """all k-subsets of range(m) as int32 array (comb(m,k), k)"""
    if k == 0:
        return np.zeros((1, 0), dtype=np.int32)
    c = comb(m, k)
    flat = np.fromiter((x for t in combinations(range(m), k) for x in t), dtype=np.int32, count=c * k)
    return flat.reshape(c, k)


def match(S, Q, tol):
    """S sorted uint64, Q uint64 queries -> (qi, si) with circular |S[si]-Q[qi]| <= tol (nearest two neighbours)"""
    if len(S) == 0 or len(Q) == 0:
        return np.zeros(0, np.int64), np.zeros(0, np.int64)
    idx = np.searchsorted(S, Q)
    n = len(S)
    qs, ss = [], []
    for off in (-1, 0):
        si = (idx + off) % n
        d = (S[si] - Q).view(np.int64)
        ok = np.flatnonzero((d >= -tol) & (d <= tol))
        qs.append(ok); ss.append(si[ok])
    return np.concatenate(qs), np.concatenate(ss)


# cost constants (seconds): per list element built, per M-zone row and per one in the row, per lookup
C_BUILD, C_ROWJ, C_LOOK = 9e-7, 6e-8, 7e-8


def plan_y(wU, nMj, a, coverage=0.99, mem_cap=1.2 * 10**7):
    """Plan the inner meet in the middle for `a` ones in the U zone and `nMj` M-zone rows.

    A random partition puts k1 of the a ones into the first half U1 (|U1| = wU//2) and a-k1 into U2.  For a split (k1, a-k1)
    we build two lists (subsets of weight k1 in U1, weight a-k1 in U2); the SMALLER list is enumerated against every M-zone row and
    looked up in the sorted LARGER list, so the cost is C_BUILD*(L1+L2) + C_LOOK*nMj*min(L1,L2).  Balanced splits are not optimal when
    there is an extra list (the M zone): unbalanced splits are far cheaper.  A set of splits per partition and a number R of random
    partitions are chosen to reach the coverage target at minimal cost.  Returns (cost, R, splits, coverage) or None.
    """
    h1, h2 = wU // 2, wU - wU // 2
    opts = []
    for k1 in range(a + 1):
        k2 = a - k1
        if k1 > h1 or k2 > h2:
            continue
        L1, L2 = comb(h1, k1), comb(h2, k2)
        if max(L1, L2) > mem_cap:
            continue
        prob = comb(a, k1) * comb(wU - a, h1 - k1) / comb(wU, h1)      # exact probability of this split for a random partition
        c = C_BUILD * (L1 + L2) + C_LOOK * nMj * min(L1, L2)
        if prob > 0:
            opts.append((c / prob, k1, prob, c))
    opts.sort()
    best, P, csum, chosen = None, 0.0, 0.0, []
    for ratio, k1, prob, c in opts:
        chosen.append((k1, a - k1)); P += prob; csum += c
        R = 1 if P >= 1 - 1e-12 else max(1, math.ceil(math.log(1 - coverage) / math.log(1 - P)))
        cov = 1 - (1 - P) ** R if P < 1 - 1e-12 else 1.0
        total = R * csum
        if best is None or total < best[0]:
            best = (total, R, list(chosen), cov)
    return best


class FPMITM:
    def __init__(self, n, r, w, h, tol_bits=30, wU=None, seed=1):
        self.n, self.r, self.w, self.h, self.tol_bits = n, r, w, h, tol_bits
        self.rng = random.Random(seed)
        PREC = 2 * w + 192
        self.PREC = PREC
        A0 = 1 << r
        D0 = A0 * A0 - n
        assert D0 > 0, "anchor must exceed sqrt(n)"
        B0f = isqrt(D0 << (2 * PREC))
        self.K0 = ((A0 << (2 * PREC)) // B0f) - (1 << PREC)
        self.C2 = (n << (4 * PREC)) // (2 * B0f ** 3)
        self.F0 = (-B0f) % (1 << PREC)
        log2c2 = self.C2.bit_length() - PREC           # c2 ~ 2^log2c2 (negative)
        self.log2c2 = log2c2
        assert 3 * w < 2 * r - tol_bits - 6, "cubic Taylor term not negligible for this (r, w)"
        if wU is None:
            wU = max(0, int(-log2c2) - tol_bits - 5 - w)
        self.wU = min(wU, w)
        self.nM = w - self.wU
        top = lambda x: (x % (1 << PREC)) >> (PREC - 64)
        K0, C2 = self.K0, self.C2
        self.F0t = np.uint64(top(self.F0))
        self.dU = np.array([top(-(K0 << e)) for e in range(self.wU)], dtype=np.uint64)
        eM = list(range(self.wU, w))
        self.phiM = np.array([top(-(K0 << e) + (C2 << (2 * e))) for e in eM], dtype=np.uint64)
        psi = np.zeros((self.nM, self.nM), dtype=np.uint64)
        for i, ei in enumerate(eM):
            for j in range(i + 1, self.nM):
                psi[i, j] = top((2 * C2) << (ei + eM[j]))
        self.psiM = psi
        self.tol = 1 << (64 - tol_bits)
        self.stats = dict(lookups=0, matches=0, verified=0, seconds=0.0)
        self.found = []

    # ---- helpers
    def TM(self, CM):
        """fractional part (uint64) of F at the M-zone subsets CM (rows of indices into the M zone)"""
        N, j = CM.shape
        T = np.full(N, self.F0t, dtype=np.uint64)
        for a in range(j):
            T += self.phiM[CM[:, a]]
        for a in range(j):
            for b in range(a + 1, j):
                T += self.psiM[CM[:, a], CM[:, b]]
        return T

    def verify(self, exps):
        z = sum(1 << e for e in exps)
        A = (1 << self.r) + z
        D = A * A - self.n
        self.stats['verified'] += 1
        if D < 0:
            return False
        t = isqrt(D)
        if t * t != D:
            return False
        for d in (gcd(A - t, self.n), gcd(A + t, self.n)):
            if 1 < d < self.n:
                self.found.append((sorted(exps), min(d, self.n // d)))
                return True
        return False

    def _plan(self, j, a, coverage):
        """cost-based choice between full enumeration of the U-zone subsets (X) and an inner meet in the middle (Y)"""
        nMj = comb(self.nM, j); nUa = comb(self.wU, a)
        costX = nUa * C_BUILD if nUa <= 3.5 * 10**7 else float('inf')
        py = plan_y(self.wU, nMj, a, coverage)
        costY = py[0] if py else float('inf')
        return ('X' if costX <= costY else 'Y'), costX, costY

    # ---- the search
    def search(self, jmax=None, xcap=3 * 10**7, coverage=0.99, chunk=2_000_000, stop_on_hit=True, verbose=False, jmin=0):
        t0 = time.time()
        h, wU, nM = self.h, self.wU, self.nM
        jmax = h if jmax is None else min(jmax, h, nM)
        total = comb(self.w, h)
        covered = 0.0
        for j in range(jmin, jmax + 1):
            a = h - j
            if a > wU:
                continue
            nMj = comb(nM, j)
            wj = comb(nM, j) * comb(wU, a)
            tj = time.time()
            if a == 0:
                for s0 in range(0, nMj, chunk):
                    pass
                cm_all = combos_array(j, nM) if nMj <= 5 * 10**7 else None
                T = self.TM(cm_all)
                ok = np.flatnonzero(((T).view(np.int64) >= -self.tol) & ((T).view(np.int64) <= self.tol))
                self.stats['lookups'] += len(T)
                for i in ok:
                    self.stats['matches'] += 1
                    self.verify([self.wU + int(x) for x in cm_all[i]])
                cov = 1.0
            elif self._plan(j, a, coverage)[0] == 'X':
                SU_c = combos_array(a, wU)
                sums = self.dU[SU_c].sum(axis=1, dtype=np.uint64) if a > 0 else None
                order = np.argsort(sums); S = sums[order]
                cm_all = combos_array(j, nM)
                for s0 in range(0, len(cm_all), chunk):
                    cm = cm_all[s0:s0 + chunk]
                    T = self.TM(cm) if j > 0 else np.full(1, self.F0t, dtype=np.uint64)
                    Q = np.uint64(0) - T
                    qi, si = match(S, Q, self.tol)
                    self.stats['lookups'] += len(Q); self.stats['matches'] += len(qi)
                    for q_, s_ in zip(qi, si):
                        exps = [self.wU + int(x) for x in cm[q_]] + [int(x) for x in SU_c[order[s_]]]
                        if self.verify(exps) and stop_on_hit:
                            self.stats['seconds'] = time.time() - t0; return self.found
                cov = 1.0
            else:
                # MITM inside the U zone, repeated random partitions until the coverage target is met
                _, R, pairs, cov = plan_y(wU, nMj, a, coverage)
                cm_all = combos_array(j, nM)
                for rep in range(R):
                    perm = list(range(wU)); self.rng.shuffle(perm)
                    U1, U2 = perm[:wU // 2], perm[wU // 2:]
                    for (k1, k2) in pairs:
                        C1, C2_ = combos_array(k1, len(U1)), combos_array(k2, len(U2))
                        e1 = np.array(U1, dtype=np.int32); e2 = np.array(U2, dtype=np.int32)
                        s1 = self.dU[e1[C1]].sum(axis=1, dtype=np.uint64) if k1 else np.zeros(1, np.uint64)
                        s2 = self.dU[e2[C2_]].sum(axis=1, dtype=np.uint64) if k2 else np.zeros(1, np.uint64)
                        if len(s1) > len(s2):          # keep the larger list as the sorted side
                            s1, s2, C1, C2_, e1, e2 = s2, s1, C2_, C1, e2, e1
                        o2 = np.argsort(s2); S2 = s2[o2]
                        rows = max(1, 20_000_000 // max(1, len(s1)))
                        for m0 in range(0, len(cm_all), rows):
                            cm = cm_all[m0:m0 + rows]
                            T = self.TM(cm) if j > 0 else np.full(1, self.F0t, dtype=np.uint64)
                            Q = (np.uint64(0) - T)[:, None] - s1[None, :]
                            qi, si = match(S2, Q.ravel(), self.tol)
                            self.stats['lookups'] += Q.size; self.stats['matches'] += len(qi)
                            for q_, s_ in zip(qi, si):
                                mi, i1 = divmod(int(q_), len(s1))
                                exps = ([self.wU + int(x) for x in cm[mi]] if j > 0 else []) \
                                       + [int(e1[x]) for x in C1[i1]] + [int(e2[x]) for x in C2_[o2[s_]]]
                                if self.verify(exps) and stop_on_hit:
                                    self.stats['seconds'] = time.time() - t0; return self.found
            covered += wj * cov
            if verbose:
                print(f"   j={j} a={a}: |M-subsets|={nMj:,}  family share={wj/total:.4f}  coverage={cov:.2f}  ({time.time()-tj:.1f}s)", flush=True)
        self.stats['seconds'] = time.time() - t0
        self.stats['coverage'] = covered / total
        return self.found
