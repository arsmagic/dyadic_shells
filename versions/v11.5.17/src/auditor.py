#!/usr/bin/env python3
"""
Cost-model auditor for structured RSA moduli.

Given a modulus n and a list of hypotheses (families of possible defects) with prior weights, the auditor
  1. decides for every hypothesis which exact/verified method is applicable and estimates its running time,
  2. orders the hypotheses by Smith's rule  (prior * coverage / cost, descending), which minimises the expected
     time to the first detection among independent tests, and
  3. executes the plan and reports predicted versus measured time and the share of every family that was covered.

Methods (all report a factor only after an exact square test / gcd):
  lattice  : Coppersmith / Howgrave-Graham on the approximation p' = A' - sqrt(A'^2 - n); polynomial time, dense window
             |z| < 2^w with w + 4 <= gamma * bitlen(n), gamma = 0.234 (measured with m = t = 12).
  scan     : exhaustive scan of the offset family with the exact quadratic-residue sieve (dyadic_kz_scan.py).
  fpmitm   : fractional-part meet in the middle for sparse offsets (fpmitm.py); coverage < 1 (jmax zone limit).
  fermat   : sieved Fermat search from ceil(sqrt n).
"""
import sys, os, time, math
from dataclasses import dataclass, field
from math import comb, isqrt
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))

GAMMA = 0.234                 # lattice reach, fraction of bitlen(n), m = t = 12 (measured at 1024 bits)
SCAN_RATE = 5.0e7             # offsets per second (implicit sparse scanner, measured 4.9e7-5.7e7)
RANGE_RATE = 5.0e7            # contiguous windows / Fermat steps per second (measured 5.4e7)
from fpmitm import plan_y, C_BUILD, C_ROWJ as C_ROW, C_LOOK   # FP-MITM cost constants live in fpmitm.py (fitted on 6 runs of the earlier balanced planner)
LATTICE_SEC_1024 = 2.0        # m = t = 12 at 1024 bits (0.6-3.0 s measured); extrapolated ~ (L/1024)^3


@dataclass
class Hyp:
    name: str
    kind: str                  # 'dense' | 'sparse' | 'fermat'
    w: int = 0                 # window / exponent range
    h: int = 0                 # weight (sparse)
    prior: float = 0.1
    jmax: int = 4              # FP-MITM: largest number of ones in the M zone
    steps: int = 1 << 20       # fermat
    methods: list = field(default_factory=list)   # filled by plan()


# ----------------------------------------------------------------------------- cost models
def est_lattice(L, w):
    ok = (w + 4) <= GAMMA * L
    return ok, LATTICE_SEC_1024 * (L / 1024.0) ** 3, 1.0


def est_scan(L, w, h, anchors=1, signs=1):
    return True, comb(w, h) * anchors * signs / SCAN_RATE + 0.02, 1.0


def fpm_geometry(L, w, tol_bits=36):
    r = L // 2
    log2c2 = -(r - 7)
    wU = max(0, int(-log2c2) - tol_bits - 5 - w)
    return wU, w - wU


def est_fpmitm(L, w, h, jmax=4, tol_bits=36, coverage=0.99):
    r = L // 2
    if not (3 * w < 2 * r - tol_bits - 6):
        return False, float('inf'), 0.0
    wU, nM = fpm_geometry(L, w, tol_bits)
    if wU <= 0:
        return False, float('inf'), 0.0
    t, cov_w, total = 0.0, 0.0, comb(w, h)
    for j in range(0, min(jmax, h, nM) + 1):
        a = h - j
        if a > wU:
            continue
        nMj, nUa = comb(nM, j), comb(wU, a)
        costX = nUa * C_BUILD if nUa <= 3.5 * 10**7 else float('inf')
        py = plan_y(wU, nMj, a, coverage)
        costY = py[0] if py else float('inf')
        if costX <= costY:
            t += costX + nMj * C_ROW * max(j, 1); cov = 1.0
        else:
            t += costY + nMj * C_ROW * max(j, 1); cov = py[3]
        cov_w += nMj * nUa * cov
    return True, t, cov_w / total


def est_fermat(L, steps):
    return True, steps / RANGE_RATE + 0.02, 1.0


def plan(L, hyps, budget=None):
    """choose a method per hypothesis, order by Smith's rule"""
    rows = []
    for H in hyps:
        opts = []
        if H.kind == 'dense':
            ok, t, c = est_lattice(L, H.w)
            if ok: opts.append(('lattice', t, c))
        elif H.kind == 'sparse':
            ok, t, c = est_lattice(L, H.w)                 # a sparse set is also inside the dense window
            if ok: opts.append(('lattice', t, c))
            ok, t, c = est_scan(L, H.w, H.h, anchors=1, signs=1)
            opts.append(('scan', t, c))
            ok, t, c = est_fpmitm(L, H.w, H.h, H.jmax)
            if ok: opts.append(('fpmitm', t, c))
        elif H.kind == 'fermat':
            ok, t, c = est_fermat(L, H.steps); opts.append(('fermat', t, c))
        # per hypothesis: maximise coverage per second, but never accept coverage < 0.5 if an exhaustive option is affordable
        best = max(opts, key=lambda o: (o[2] / o[1]) if o[1] > 0 else 0) if opts else None
        exh = [o for o in opts if o[2] >= 0.99]
        if exh:
            e = min(exh, key=lambda o: o[1])
            if best is None or e[1] <= 20 * best[1]:          # an exhaustive method within 20x of the fastest heuristic one
                best = e
        rows.append((H, best, opts))
    order = sorted([r for r in rows if r[1]], key=lambda r: -(r[0].prior * r[1][2] / max(r[1][1], 1e-9)))
    if budget is not None:
        acc, kept = 0.0, []
        for r in order:
            if acc + r[1][1] <= budget: kept.append(r); acc += r[1][1]
        order = kept
    return order, [r for r in rows if not r[1]]


# ----------------------------------------------------------------------------- execution
def run_method(n, H, method):
    L = n.bit_length(); r = (L + 1) // 2
    t0 = time.time(); found = None
    if method == 'lattice':
        from cop_lattice import coppersmith_divisor
        A0 = 1 << r; p0 = A0 - isqrt(A0 * A0 - n)
        X = 1 << (H.w + 4)
        mt = 8 if H.w + 4 <= 0.225 * L else 12
        out = coppersmith_divisor(n, p0, X, mt, mt)
        found = out[1] if out else None
    elif method == 'scan':
        from dyadic_kz_scan import scan_set, SparseFamily
        hits, _ = scan_set(n, ('sparse', SparseFamily(H.w, H.h)), ks=(1,), anchors=[r],
                           n_primes=int(1.2 * math.log2(comb(H.w, H.h))) + 4)
        found = hits[0]['p'] if hits else None
    elif method == 'fpmitm':
        from fpmitm import FPMITM
        m = FPMITM(n, r, H.w, H.h, tol_bits=36)
        res = m.search(jmax=H.jmax, stop_on_hit=False)
        found = res[0][1] if res else None
    elif method == 'fermat':
        from dyadic_kz_scan import scan_set
        hits, _ = scan_set(n, ('range', 0, H.steps), ks=(1,), anchors=[0], n_primes=16,
                           base_fn=lambda rr: isqrt(n - 1) + 1)
        found = hits[0]['p'] if hits else None
    return found, time.time() - t0


def audit(n, hyps, budget=None, verbose=True):
    L = n.bit_length()
    order, skipped = plan(L, hyps, budget)
    if verbose:
        print(f"modulus: {L} bits;  plan (Smith order = prior*coverage/cost):")
        for H, (m, t, c), opts in order:
            alts = ", ".join(f"{o[0]}:{o[1]:.3g}s/cov {o[2]:.2f}" for o in opts)
            print(f"  {H.name:<34} prior {H.prior:.2f} -> {m:<7} predicted {t:9.3g} s, coverage {c:.2f}   [options: {alts}]")
        for H, _, opts in skipped:
            print(f"  {H.name:<34} no applicable method (infeasible)")
    total_pred = total_act = 0.0
    result = None
    for H, (m, t, c), opts in order:
        f, act = run_method(n, H, m)
        total_pred += t; total_act += act
        if verbose: print(f"  ran {H.name:<30} {m:<7} predicted {t:8.3g} s  actual {act:8.3g} s  -> {'FACTOR FOUND' if f else 'nothing'}")
        if f:
            result = (H.name, m, f); break
    return result, total_pred, total_act


if __name__ == '__main__':
    print(__doc__)
