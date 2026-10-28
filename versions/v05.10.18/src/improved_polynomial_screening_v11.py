#!/usr/bin/env python3
"""
Dyadic-shell bounded diagnostic screen, v11.

This research prototype implements two public screening layers:

1. The original visible representative line
       F_x = 2^x - n,
   corresponding to lambda = 1.

2. The square-multiplier extension
       F_{x,u} = u^2 * 2^x - n,
   corresponding to lambda = u^2.

The script is intentionally sound but incomplete.  Every reported exact triple
or factor is verified by direct arithmetic.  A negative result does not prove
that no non-trivial dyadic triple exists and does not certify cryptographic
security.
"""

from __future__ import annotations

import argparse
import math
import os
import sys
import traceback
from concurrent.futures import FIRST_COMPLETED, ProcessPoolExecutor, wait
from dataclasses import dataclass
from datetime import datetime
from itertools import combinations
from typing import Dict, Iterable, List, Optional, Sequence, Tuple


# ---------------------------------------------------------------------------
# Basic arithmetic
# ---------------------------------------------------------------------------


def ceil_half_log2(n: int) -> int:
    if n <= 0:
        raise ValueError("n must be positive")
    r = (n.bit_length() + 1) // 2
    while (1 << (2 * r)) <= n:
        r += 1
    while r > 0 and (1 << (2 * (r - 1))) > n:
        r -= 1
    return r


def ceil_even(x: int) -> int:
    return x if x % 2 == 0 else x + 1


def floor_even(x: int) -> int:
    return x if x % 2 == 0 else x - 1


def is_square(n: int) -> Tuple[bool, int]:
    if n < 0:
        return False, 0
    r = math.isqrt(n)
    return r * r == n, r


def inv_mod(a: int, m: int) -> int:
    a %= m
    if math.gcd(a, m) != 1:
        raise ValueError("inverse does not exist")
    return pow(a, -1, m)


def min_even_x_positive(n: int, u: int) -> int:
    """Smallest even x such that u^2 * 2^x > n."""
    if u <= 0:
        raise ValueError("u must be positive")
    u2 = u * u
    x = max(0, (n // u2).bit_length())
    while u2 * (1 << x) <= n:
        x += 1
    return ceil_even(x)


def min_r_crt(n: int, u: int) -> int:
    """Smallest r such that u * 2^r > n."""
    if u <= 0:
        raise ValueError("u must be positive")
    r = max(0, (n // u).bit_length())
    while u * (1 << r) <= n:
        r += 1
    return r


def odd_square_roots_mod_power_two(a: int, x: int) -> List[int]:
    """Return roots of z^2 == a mod 2^x for odd a.

    For x >= 3, an odd a is a square modulo 2^x iff a == 1 mod 8, in which
    case there are four roots.  The lifting below is elementary and deterministic.
    """
    if x <= 0:
        raise ValueError("x must be positive")
    mod = 1 << x
    a %= mod
    if a % 2 == 0:
        raise ValueError("a must be odd")
    if x == 1:
        return [1]
    if x == 2:
        return [1, 3] if a % 4 == 1 else []
    if a % 8 != 1:
        return []

    roots = [1, 3, 5, 7]
    current = 3
    while current < x:
        step = 1 << current
        next_mod = 1 << (current + 1)
        target = a % next_mod
        lifted: List[int] = []
        for r in roots:
            for cand in (r, r + step):
                if (cand * cand - target) % next_mod == 0:
                    lifted.append(cand % next_mod)
        roots = sorted(set(lifted))
        current += 1
    return sorted(set(r % mod for r in roots))


def correction_factor_to_square_class(h: int) -> int:
    h8 = h % 8
    if h8 not in (1, 3, 5, 7):
        raise ValueError("h must be odd")
    # Odd residues modulo 8 are self-inverse.
    return h8


# ---------------------------------------------------------------------------
# Factor extraction
# ---------------------------------------------------------------------------


def trial_division_partial(n: int, bound: int) -> Tuple[Dict[int, int], int]:
    if n < 0:
        n = -n
    if n <= 1 or bound < 2:
        return {}, n
    factors: Dict[int, int] = {}
    m = n
    while m % 2 == 0:
        factors[2] = factors.get(2, 0) + 1
        m //= 2
    p = 3
    while p <= bound and p * p <= m:
        while m % p == 0:
            factors[p] = factors.get(p, 0) + 1
            m //= p
        p += 2
    if 1 < m <= bound:
        factors[m] = factors.get(m, 0) + 1
        m = 1
    return factors, m


def sympy_partial_factor(n: int, limit: Optional[int], full: bool = False) -> Tuple[Dict[int, int], int]:
    if n < 0:
        n = -n
    if n <= 1:
        return {}, n
    try:
        from sympy.ntheory import factorint  # type: ignore
    except Exception as exc:
        if full:
            raise RuntimeError("--full requires SymPy") from exc
        return trial_division_partial(n, int(limit or 10000))

    kwargs = dict(use_trial=True, use_rho=True, use_pm1=True, use_ecm=True)
    if full:
        raw = factorint(n, **kwargs)
    else:
        raw = factorint(n, limit=int(limit or 10000), **kwargs)
    return {int(k): int(v) for k, v in raw.items()}, 1


def bounded_factor_extraction(n: int, bound: int, method: str, full: bool = False) -> Tuple[Dict[int, int], int]:
    if full:
        return sympy_partial_factor(n, None, full=True)
    if method == "trial":
        return trial_division_partial(n, bound)
    if method == "sympy":
        return sympy_partial_factor(n, bound, full=False)
    raise ValueError(f"unknown factor method: {method}")


# ---------------------------------------------------------------------------
# Dataclasses
# ---------------------------------------------------------------------------


@dataclass
class PairTask:
    n: int
    x: int
    u: int
    trial_bound: int
    factor_method: str
    full_factorization: bool
    max_square_divisors: int
    max_h_components: int
    max_h_candidates: int
    max_candidates_per_pair: int
    include_full_residual_h: bool
    max_s_shifts: int


@dataclass
class Candidate:
    x: int
    u: int
    source: str
    s: int
    alpha: int
    beta: int
    h: int
    correction: int
    lambda_square: int
    lambda0: int
    delta: Optional[float]
    rho: Optional[float]
    interval_ok: bool
    exact_ok: bool
    factor_minus: int
    factor_plus: int
    note: str = ""

    def factor_found(self, n: int) -> Optional[int]:
        for g in (self.factor_minus, self.factor_plus):
            if 1 < g < n and n % g == 0:
                return g
        return None


@dataclass
class PairScore:
    x: int
    u: int
    sq_score: float
    forced_primes: Tuple[int, ...]


@dataclass
class ScanResult:
    n: int
    x: int
    u: int
    F_bits: int
    partial_factors: Dict[int, int]
    cofactor_bits: int
    candidates_tested: int
    best_delta: Optional[float]
    best_candidate: Optional[Candidate]
    exact_candidates: List[Candidate]
    factors_found: List[Tuple[int, int]]


# ---------------------------------------------------------------------------
# Candidate generation
# ---------------------------------------------------------------------------


def generate_root_divisors(
    factors: Dict[int, int],
    cofactor: int,
    max_count: int,
    include_square_cofactor: bool = True,
) -> List[int]:
    root_items: List[Tuple[int, int]] = []
    for p, e in sorted(factors.items()):
        if e // 2 > 0:
            root_items.append((p, e // 2))

    if include_square_cofactor and cofactor > 1:
        ok, y = is_square(cofactor)
        if ok:
            root_items.append((y, 1))

    divisors = [1]
    for base, max_exp in root_items:
        new_divs: List[int] = []
        val = 1
        powers = [1]
        for _ in range(max_exp):
            val *= base
            powers.append(val)
        for d in divisors:
            for pw in powers:
                new_divs.append(d * pw)
                if len(new_divs) >= max_count:
                    break
            if len(new_divs) >= max_count:
                break
        divisors = sorted(set(new_divs))[:max_count]
        if len(divisors) >= max_count:
            break
    return sorted(set(divisors))[:max_count]


def generate_h_pool(
    residual: int,
    factors: Dict[int, int],
    cofactor: int,
    max_components: int,
    max_h: int,
    include_full_residual: bool,
) -> List[int]:
    hs = {1}
    components: List[int] = []
    abs_res = abs(residual)

    for p in sorted(factors):
        if p % 2 == 1 and abs_res % p == 0:
            components.append(p)
    if cofactor > 1 and cofactor % 2 == 1 and abs_res % cofactor == 0:
        components.append(cofactor)

    for k in range(1, max_components + 1):
        for combo in combinations(components, k):
            h = 1
            for c in combo:
                h *= c
            if h > 0 and residual % h == 0:
                hs.add(h)
                if len(hs) >= max_h:
                    return sorted(hs)[:max_h]

    if include_full_residual and residual % 2 != 0:
        hs.add(abs(residual))
    return sorted(hs)[:max_h]


def shifted_representatives(s0: int, mod: int, root_bound: int, max_shifts: int) -> Iterable[int]:
    """Yield positive representatives s = s0 + k*mod inside root_bound.

    In the usual polynomial u range and large x, root_bound < mod, so at most
    one representative appears.  The hook is kept for completeness.
    """
    if s0 <= 0:
        return
    if s0 < root_bound:
        yield s0
    if max_shifts <= 0 or root_bound <= mod:
        return
    kmax = min(max_shifts, (root_bound - 1 - s0) // mod)
    for k in range(1, kmax + 1):
        s = s0 + k * mod
        if s < root_bound:
            yield s


def evaluate_candidate(
    n: int,
    x: int,
    u: int,
    s: int,
    alpha: int,
    beta: int,
    h: int,
    correction: int,
    source: str,
    note: str = "",
) -> Candidate:
    mod = 1 << x
    lambda_square = u * u
    assert (s * s + alpha * n) % mod == 0, "candidate congruence failed"
    lambda0 = (s * s * inv_mod(pow(2, x, n), n)) % n

    delta: Optional[float] = None
    rho: Optional[float] = None
    interval_ok = False
    exact_ok = False
    factor_minus = 1
    factor_plus = 1

    if x % 2 == 0:
        root_bound = u * (1 << (x // 2))
        U_xu = (lambda_square * mod - 1) // n
        if alpha > 0 and U_xu > 0:
            delta = math.log2(alpha) - math.log2(U_xu)
            rho = delta / math.log2(n) if n > 1 else None
        interval_ok = (0 < s < root_bound and 1 <= alpha <= U_xu)
        exact_ok = interval_ok and (lambda_square * mod - s * s == alpha * n)
        factor_minus = math.gcd(root_bound - s, n)
        factor_plus = math.gcd(root_bound + s, n)

    return Candidate(
        x=x,
        u=u,
        source=source,
        s=s,
        alpha=alpha,
        beta=beta,
        h=h,
        correction=correction,
        lambda_square=lambda_square,
        lambda0=lambda0,
        delta=delta,
        rho=rho,
        interval_ok=interval_ok,
        exact_ok=exact_ok,
        factor_minus=factor_minus,
        factor_plus=factor_plus,
        note=note,
    )


def generate_candidates_for_pair(
    n: int,
    x: int,
    u: int,
    factors: Dict[int, int],
    cofactor: int,
    max_square_divisors: int,
    max_h_components: int,
    max_h_candidates: int,
    max_candidates: int,
    include_full_residual_h: bool,
    max_s_shifts: int,
) -> List[Candidate]:
    mod = 1 << x
    F = u * u * mod - n
    if F == 0 or F % 2 == 0:
        return []

    root_bound = u * (1 << (x // 2)) if x % 2 == 0 else mod
    a_values = generate_root_divisors(factors, cofactor, max_square_divisors)
    candidates: List[Candidate] = []
    seen = set()

    for a in a_values:
        a2 = a * a
        if F % a2 != 0:
            continue
        residual = F // a2
        h_pool = generate_h_pool(
            residual=residual,
            factors=factors,
            cofactor=cofactor,
            max_components=max_h_components,
            max_h=max_h_candidates,
            include_full_residual=include_full_residual_h,
        )
        for h in h_pool:
            if h <= 0 or h % 2 == 0 or residual % h != 0:
                continue
            beta = residual // h
            if beta % 2 == 0:
                continue
            try:
                c = correction_factor_to_square_class(h)
                square_class = (c * (h % mod)) % mod
                roots = odd_square_roots_mod_power_two(square_class, x)
                alpha = (c * inv_mod(beta % mod, mod)) % mod
            except ValueError:
                continue
            if alpha == 0:
                alpha = mod
            source = "literal-square" if h == 1 and c == 1 and u == 1 else "square-multiplier-correction"
            if h == 1 and c == 1 and u != 1:
                source = "square-multiplier-literal"
            for z in roots:
                s0 = (a * z) % mod
                for s in shifted_representatives(s0, mod, root_bound, max_s_shifts):
                    key = (s, alpha, beta, h, c, source)
                    if key in seen:
                        continue
                    seen.add(key)
                    if (s * s + alpha * n) % mod != 0:
                        continue
                    cand = evaluate_candidate(n, x, u, s, alpha, beta, h, c, source, note=f"a={a}")
                    candidates.append(cand)
                    if len(candidates) >= max_candidates:
                        return candidates
    return candidates


# ---------------------------------------------------------------------------
# Pair ranking and planning
# ---------------------------------------------------------------------------


def parse_prime_list_csv(value: str) -> List[int]:
    if not value or not value.strip():
        return []
    out: List[int] = []
    for part in value.split(','):
        part = part.strip()
        if not part:
            continue
        p = int(part)
        if p <= 2 or p % 2 == 0:
            raise ValueError(f"forcing primes must be odd primes; got {p}")
        for d in range(3, int(math.isqrt(p)) + 1, 2):
            if p % d == 0:
                raise ValueError(f"forcing value {p} is not prime")
        out.append(p)
    return sorted(set(out))


def parse_u_list(value: str) -> List[int]:
    if not value or not value.strip():
        return []
    out = []
    for part in value.split(','):
        part = part.strip()
        if not part:
            continue
        u = int(part)
        if u <= 0:
            raise ValueError("all u values must be positive")
        out.append(u)
    return sorted(set(out))


def pair_small_prime_score(n: int, x: int, u: int, primes: Sequence[int], depth: int) -> PairScore:
    if not primes or depth < 1:
        return PairScore(x=x, u=u, sq_score=0.0, forced_primes=())
    score = 0.0
    forced: List[int] = []
    u2 = u * u
    for ell in primes:
        if n % ell == 0:
            continue
        e = 0
        m = 1
        for j in range(1, depth + 1):
            m *= ell
            if (u2 * pow(2, x, m) - n) % m == 0:
                e = j
            else:
                break
        if e > 0:
            forced.append(ell)
        q = e // 2
        if q:
            score += 2.0 * q * math.log(ell)
    return PairScore(x=x, u=u, sq_score=score, forced_primes=tuple(forced))


def build_u_values(args: argparse.Namespace, n_bits: int) -> List[int]:
    values = set(parse_u_list(args.u_list))
    if args.square_multiplier_scan:
        if args.u_bound < 1:
            raise ValueError("--u-bound must be positive")
        values.update(range(1, args.u_bound + 1))
    else:
        values.add(1)
    if args.u_poly_exp is not None:
        if args.u_poly_exp < 0:
            raise ValueError("--u-poly-exp must be non-negative")
        values.update(range(1, int(n_bits ** args.u_poly_exp) + 1))
    values.add(1)
    return sorted(values)


def build_pair_plan(
    n: int,
    args: argparse.Namespace,
    rank_primes: Sequence[int],
) -> Tuple[int, int, List[Tuple[int, int]], Dict[Tuple[int, int], PairScore]]:
    if n <= 1 or n % 2 == 0:
        raise ValueError("n must be an odd integer > 1")
    r_min = ceil_half_log2(n)
    R = 2 * r_min
    default_stop = 4 * R
    full_range = bool(args.full or args.full_range)

    u_values = build_u_values(args, n.bit_length())
    pair_scores: Dict[Tuple[int, int], PairScore] = {}
    selected: List[Tuple[int, int]] = []

    for u in u_values:
        x_pos = min_even_x_positive(n, u)
        x_crt = 2 * min_r_crt(n, u)

        if args.x_start is not None:
            x_start = ceil_even(args.x_start)
        elif args.include_pre_window:
            x_start = ceil_even(r_min)
        elif args.square_multiplier_scan:
            x_start = x_pos
        else:
            x_start = R if args.range_mode != "legacy" else ceil_even(r_min)

        if full_range:
            x_stop = default_stop
        elif args.x_stop is not None:
            x_stop = floor_even(args.x_stop)
        elif args.x_window is not None:
            if args.x_window <= 0:
                raise ValueError("--x-window must be positive")
            x_stop = x_start + 2 * (args.x_window - 1)
        else:
            if args.range_mode == "core":
                x_stop = x_crt if args.square_multiplier_scan else 2 * R
            else:
                x_stop = default_stop
        x_stop = floor_even(x_stop)
        if x_stop < x_start:
            continue

        base = list(range(x_start, x_stop + 1, 2))
        if not base:
            continue

        if args.square_multiplier_scan:
            core = [x for x in base if x_pos <= x <= min(x_crt, x_stop)]
            tail = [x for x in base if x > x_crt]
        else:
            core = [x for x in base if R <= x <= min(2 * R, x_stop)]
            if args.range_mode == "legacy":
                core = base
            tail = [x for x in base if x > 2 * R]

        for x in base:
            if rank_primes:
                pair_scores[(x, u)] = pair_small_prime_score(n, x, u, rank_primes, args.force_depth)
            else:
                pair_scores[(x, u)] = PairScore(x=x, u=u, sq_score=0.0, forced_primes=())

        if args.range_mode in ("legacy", "factor") and not args.square_multiplier_scan:
            chosen = base
        elif args.force_mode == "hard":
            chosen = [x for x in core if pair_scores[(x, u)].sq_score > 0]
        else:
            chosen = sorted(core)

        tail_ranked = sorted(
            tail,
            key=lambda x: (
                -pair_scores[(x, u)].sq_score,
                args.u_penalty * math.log(max(u, 1)) + args.tail_penalty * max(0, x - x_crt),
                x,
                u,
            ),
        )
        if args.tail_min_score is not None:
            tail_ranked = [x for x in tail_ranked if pair_scores[(x, u)].sq_score >= args.tail_min_score]
        if args.tail_top_per_u is not None:
            tail_ranked = tail_ranked[: args.tail_top_per_u]
        elif args.tail_top is not None and not args.square_multiplier_scan:
            tail_ranked = tail_ranked[: args.tail_top]
        if args.force_mode == "hard":
            tail_ranked = [x for x in tail_ranked if pair_scores[(x, u)].sq_score > 0]
        if args.range_mode != "core":
            chosen.extend(tail_ranked)

        if not args.no_protect_crt:
            if x_start <= x_crt <= x_stop or args.square_multiplier_scan:
                chosen.append(x_crt)
        if not args.no_protect_2R and u == 1:
            chosen.append(2 * R)

        for x in chosen:
            if x >= 0 and x % 2 == 0:
                selected.append((x, u))

    # Remove duplicates, then globally rank optional square-multiplier pairs.
    selected = list(dict.fromkeys(selected))
    if args.global_pair_top is not None:
        selected = sorted(
            selected,
            key=lambda xu: (
                -pair_scores.get(xu, PairScore(xu[0], xu[1], 0.0, ())).sq_score,
                args.u_penalty * math.log(max(xu[1], 1)),
                xu[0],
                xu[1],
            ),
        )[: args.global_pair_top]
    if not selected:
        raise ValueError("no (x,u) pairs selected")
    return r_min, R, selected, pair_scores


# ---------------------------------------------------------------------------
# Scanning
# ---------------------------------------------------------------------------


def scan_pair(task: PairTask) -> Optional[ScanResult]:
    mod = 1 << task.x
    F = task.u * task.u * mod - task.n
    if F == 0:
        return None
    factors, cofactor = bounded_factor_extraction(abs(F), task.trial_bound, task.factor_method, task.full_factorization)
    candidates = generate_candidates_for_pair(
        n=task.n,
        x=task.x,
        u=task.u,
        factors=factors,
        cofactor=cofactor,
        max_square_divisors=task.max_square_divisors,
        max_h_components=task.max_h_components,
        max_h_candidates=task.max_h_candidates,
        max_candidates=task.max_candidates_per_pair,
        include_full_residual_h=task.include_full_residual_h,
        max_s_shifts=task.max_s_shifts,
    )
    exact_candidates = [c for c in candidates if c.exact_ok]
    factor_set = set()
    for c in candidates:
        f = c.factor_found(task.n)
        if f is not None:
            p, q = sorted((f, task.n // f))
            factor_set.add((p, q))
    finite = [c for c in candidates if c.delta is not None]
    best = min(finite, key=lambda c: c.delta) if finite else None
    return ScanResult(
        n=task.n,
        x=task.x,
        u=task.u,
        F_bits=abs(F).bit_length(),
        partial_factors=factors,
        cofactor_bits=cofactor.bit_length() if cofactor > 1 else 0,
        candidates_tested=len(candidates),
        best_delta=best.delta if best else None,
        best_candidate=best,
        exact_candidates=exact_candidates,
        factors_found=sorted(factor_set),
    )


def print_result(result: ScanResult, score: Optional[PairScore] = None) -> None:
    prefix = f"x={result.x}, u={result.u}, lambda=u^2={result.u * result.u}"
    if score is not None:
        prefix += f", score={score.sq_score:.3f}, forced={list(score.forced_primes)}"
    print("-" * 72, flush=True)
    print(prefix, flush=True)
    print(
        f"F bits={result.F_bits}, extracted={result.partial_factors}, cofactor_bits={result.cofactor_bits}",
        flush=True,
    )
    print(
        f"candidates={result.candidates_tested}, exact={len(result.exact_candidates)}, factors={result.factors_found}",
        flush=True,
    )
    if result.best_candidate:
        c = result.best_candidate
        print(
            f"best delta={c.delta:.3f}, rho={c.rho:.3f}, source={c.source}, "
            f"s_bits={c.s.bit_length()}, alpha_bits={c.alpha.bit_length()}, lambda0={c.lambda0}",
            flush=True,
        )
    for c in result.exact_candidates[:5]:
        print(
            f"EXACT: source={c.source}, s={c.s}, alpha={c.alpha}, "
            f"lambda0={c.lambda0}, gcds=({c.factor_minus},{c.factor_plus})",
            flush=True,
        )
    if result.factors_found:
        print(f"FOUND FACTOR(S): {result.factors_found}", flush=True)


def make_task(args: argparse.Namespace, n: int, x: int, u: int, full_factorization: bool) -> PairTask:
    return PairTask(
        n=n,
        x=x,
        u=u,
        trial_bound=args.trial_bound,
        factor_method=args.factor_method,
        full_factorization=full_factorization,
        max_square_divisors=args.max_square_divisors,
        max_h_components=args.max_h_components,
        max_h_candidates=args.max_h_candidates,
        max_candidates_per_pair=args.max_candidates_per_pair,
        include_full_residual_h=not args.no_full_residual_h,
        max_s_shifts=args.max_s_shifts,
    )


def scan_all(args: argparse.Namespace, n: int, pairs: List[Tuple[int, int]], pair_scores: Dict[Tuple[int, int], PairScore]) -> List[ScanResult]:
    full_factorization = bool(args.full and not args.partial_fx and not args.full_range)
    if full_factorization:
        args.factor_method = "sympy"
    stop_on_factor = not args.continue_after_factor
    verbose = not args.quiet
    results: List[ScanResult] = []

    if not args.parallel:
        for x, u in pairs:
            result = scan_pair(make_task(args, n, x, u, full_factorization))
            if result is None:
                continue
            results.append(result)
            if verbose:
                print_result(result, pair_scores.get((x, u)))
            if stop_on_factor and result.factors_found:
                break
        return results

    max_workers = args.workers or (os.cpu_count() or 1)
    if max_workers <= 0:
        raise ValueError("--workers must be positive")
    max_pending = max(1, 2 * max_workers)
    pair_iter = iter(pairs)
    pending = {}
    executor = ProcessPoolExecutor(max_workers=max_workers)
    try:
        def submit_next() -> bool:
            try:
                x, u = next(pair_iter)
            except StopIteration:
                return False
            fut = executor.submit(scan_pair, make_task(args, n, x, u, full_factorization))
            pending[fut] = (x, u)
            return True

        for _ in range(min(max_pending, len(pairs))):
            if not submit_next():
                break

        while pending:
            done, _ = wait(pending, return_when=FIRST_COMPLETED)
            stop_now = False
            for fut in done:
                x, u = pending.pop(fut)
                try:
                    result = fut.result()
                except Exception as exc:
                    raise RuntimeError(f"parallel worker failed at x={x}, u={u}") from exc
                if result is None:
                    continue
                results.append(result)
                if verbose:
                    print_result(result, pair_scores.get((x, u)))
                if stop_on_factor and result.factors_found:
                    stop_now = True
                    break
            if stop_now:
                for fut in pending:
                    fut.cancel()
                executor.shutdown(wait=False, cancel_futures=True)
                return sorted(results, key=lambda r: (r.x, r.u))
            while len(pending) < max_pending:
                if not submit_next():
                    break
    finally:
        executor.shutdown(wait=True, cancel_futures=True)
    return sorted(results, key=lambda r: (r.x, r.u))



# ---------------------------------------------------------------------------
# Optional built-in tee logging
# ---------------------------------------------------------------------------


class TeeStream:
    """Duplicate writes to multiple text streams.

    This is used for the --tee-log option so that the script can write the same
    output to the terminal and to a log file without relying on shell-specific
    commands such as PowerShell Tee-Object or Unix tee.
    """

    def __init__(self, *streams):
        self.streams = streams

    def write(self, data: str) -> int:
        for stream in self.streams:
            stream.write(data)
            stream.flush()
        return len(data)

    def flush(self) -> None:
        for stream in self.streams:
            stream.flush()

    def isatty(self) -> bool:
        return any(getattr(stream, "isatty", lambda: False)() for stream in self.streams)


_LOG_HANDLE = None
_ORIG_STDOUT = sys.__stdout__
_ORIG_STDERR = sys.__stderr__


def install_tee_logging(path: Optional[str], append: bool = False) -> None:
    """Duplicate stdout and stderr to a UTF-8 log file when requested."""
    global _LOG_HANDLE
    if not path:
        return
    log_path = os.path.abspath(path)
    parent = os.path.dirname(log_path)
    if parent:
        os.makedirs(parent, exist_ok=True)
    mode = "a" if append else "w"
    _LOG_HANDLE = open(log_path, mode, encoding="utf-8", buffering=1)
    sys.stdout = TeeStream(_ORIG_STDOUT, _LOG_HANDLE)  # type: ignore[assignment]
    sys.stderr = TeeStream(_ORIG_STDERR, _LOG_HANDLE)  # type: ignore[assignment]
    print(f"Tee logging enabled: {log_path}", flush=True)


def close_tee_logging() -> None:
    global _LOG_HANDLE
    if _LOG_HANDLE is not None:
        handle = _LOG_HANDLE
        # Restore the original streams before closing the log file; otherwise
        # Python may try to flush a TeeStream that points to a closed file during
        # interpreter shutdown.
        sys.stdout = _ORIG_STDOUT  # type: ignore[assignment]
        sys.stderr = _ORIG_STDERR  # type: ignore[assignment]
        try:
            handle.flush()
        finally:
            handle.close()
        _LOG_HANDLE = None

# ---------------------------------------------------------------------------
# Logging and CLI
# ---------------------------------------------------------------------------


def format_timestamp(dt: datetime) -> str:
    return dt.astimezone().isoformat(timespec="seconds")


def format_elapsed(seconds: float) -> str:
    if seconds < 0:
        seconds = 0.0
    millis = int(round((seconds - int(seconds)) * 1000))
    total = int(seconds)
    days, rem = divmod(total, 86400)
    hours, rem = divmod(rem, 3600)
    minutes, secs = divmod(rem, 60)
    if millis == 1000:
        secs += 1
        millis = 0
    return f"{days}d {hours:02d}:{minutes:02d}:{secs:02d}.{millis:03d}"


def parse_int(value: str) -> int:
    value = value.strip().replace("_", "")
    if value.lower().startswith("0x"):
        return int(value, 16)
    return int(value, 10)


def print_header(args: argparse.Namespace, n: int, r_min: int, R: int, pairs: List[Tuple[int, int]], start: datetime) -> None:
    u_values = sorted({u for _, u in pairs})
    xs = [x for x, _ in pairs]
    print("RUN START", flush=True)
    print("=" * 72, flush=True)
    print(f"Start time: {format_timestamp(start)}", flush=True)
    print(f"Input n (decimal): {n}", flush=True)
    print(f"Input n digits: {len(str(n))}", flush=True)
    print(f"Input n bit length: {n.bit_length()}", flush=True)
    print(f"r_min={r_min}, R={R}, protected original x=2R={2 * R}, default x_max=4R={4 * R}", flush=True)
    print(f"Selected pairs: {len(pairs)}; x span={min(xs)}..{max(xs)}; u count={len(u_values)}; u range={min(u_values)}..{max(u_values)}", flush=True)
    print(f"Square multiplier scan: {bool(args.square_multiplier_scan)}", flush=True)
    print(f"Range mode: {args.range_mode}; force_mode={args.force_mode}; protect_crt={not args.no_protect_crt}; protect_2R={not args.no_protect_2R}", flush=True)
    print(f"Rank primes: {args.rank_force_primes}; force_depth={args.force_depth}; tail_top_per_u={args.tail_top_per_u}; global_pair_top={args.global_pair_top}", flush=True)
    print(f"Factor extraction: method={args.factor_method}, trial_bound={args.trial_bound}, full={args.full}, partial_fx={args.partial_fx or args.full_range}", flush=True)
    print(f"Candidate limits: max_square_divisors={args.max_square_divisors}, max_h_components={args.max_h_components}, max_h_candidates={args.max_h_candidates}, max_candidates_per_pair={args.max_candidates_per_pair}", flush=True)
    if args.parallel:
        print(f"Parallel: ProcessPoolExecutor, workers={args.workers or (os.cpu_count() or 1)}", flush=True)
    else:
        print("Parallel: false", flush=True)
    print("=" * 72, flush=True)


def print_footer(start: datetime, status: str) -> None:
    end = datetime.now().astimezone()
    print("\nRUN END", flush=True)
    print("=" * 72, flush=True)
    print(f"End time: {format_timestamp(end)}", flush=True)
    print(f"Elapsed time: {format_elapsed((end - start).total_seconds())}", flush=True)
    print(f"Status: {status}", flush=True)
    print("=" * 72, flush=True)


def print_summary(results: List[ScanResult], n: int, top: int) -> None:
    print("\nSUMMARY", flush=True)
    print("=" * 72, flush=True)
    factors: List[Tuple[int, int, int, int]] = []
    exact: List[Candidate] = []
    best: List[Candidate] = []
    for r in results:
        for p, q in r.factors_found:
            factors.append((r.x, r.u, p, q))
        exact.extend(r.exact_candidates)
        if r.best_candidate is not None:
            best.append(r.best_candidate)

    if factors:
        print("Non-trivial factors found:", flush=True)
        for x, u, p, q in sorted(factors):
            print(f"  x={x}, u={u}: {p} * {q} = {n}", flush=True)
    else:
        print("No non-trivial factor found in this bounded screen.", flush=True)
    print(f"Processed pairs: {len(results)}", flush=True)
    print(f"Total candidates tested: {sum(r.candidates_tested for r in results)}", flush=True)
    print(f"Exact candidates found: {len(exact)}", flush=True)
    for c in exact[:top]:
        print(f"  EXACT x={c.x}, u={c.u}, source={c.source}, s={c.s}, alpha={c.alpha}, gcds=({c.factor_minus},{c.factor_plus})", flush=True)

    best.sort(key=lambda c: c.delta if c.delta is not None else float('inf'))
    print(f"\nTop {min(top, len(best))} best interval defects:", flush=True)
    for c in best[:top]:
        print(
            f"  x={c.x}, u={c.u}, lambda={c.lambda_square}, delta={c.delta:.3f}, "
            f"rho={c.rho:.3f}, source={c.source}, s_bits={c.s.bit_length()}, "
            f"alpha_bits={c.alpha.bit_length()}, lambda0={c.lambda0}, h_mod8={c.h % 8}, c={c.correction}",
            flush=True,
        )


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="Bounded dyadic-shell screen with optional square-multiplier layer.")
    parser.add_argument("--n", required=True, type=parse_int, help="Odd integer n to screen")
    parser.add_argument("--x-start", type=int, default=None, help="First even exponent x. Default depends on range mode and u.")
    parser.add_argument("--x-stop", type=int, default=None, help="Last even exponent x, inclusive")
    parser.add_argument("--x-window", type=int, default=None, help="Number of even x values per layer if x-stop is omitted")
    parser.add_argument("--range-mode", choices=("legacy", "factor", "core", "ranked-core-tail", "square-optimized"), default="square-optimized", help="Exponent selection policy. square-optimized uses u-dependent core and tail when --square-multiplier-scan is set.")
    parser.add_argument("--include-pre-window", action="store_true", help="Include diagnostic pre-window before the natural positive-exactness threshold")
    parser.add_argument("--full", action="store_true", help="Force x-stop to 4R; without --partial-fx this asks SymPy for full factorization of every selected F")
    parser.add_argument("--partial-fx", action="store_true", help="With --full, keep bounded partial factor extraction")
    parser.add_argument("--full-range", action="store_true", help="Force x-stop to 4R while keeping bounded partial factor extraction")

    parser.add_argument("--square-multiplier-scan", action="store_true", help="Enable lambda=u^2 layers using F_{x,u}=u^2*2^x-n")
    parser.add_argument("--u-bound", type=int, default=1, help="Scan u=1..u_bound when --square-multiplier-scan is enabled")
    parser.add_argument("--u-list", default="", help="Comma-separated explicit u values to include")
    parser.add_argument("--u-poly-exp", type=float, default=None, help="Also include u<=bitlength(n)^u_poly_exp; use with caution")
    parser.add_argument("--u-penalty", type=float, default=0.0, help="Ranking penalty coefficient for log(u)")
    parser.add_argument("--tail-penalty", type=float, default=0.0, help="Ranking penalty for distance beyond x_CRT(u)")

    parser.add_argument("--rank-force-primes", default="3,5,7,11,13,17,19", help="Small primes used to score pairs by ell^2 | F_{x,u}. Empty disables.")
    parser.add_argument("--force-depth", type=int, default=2, help="Prime-power depth for pair scoring")
    parser.add_argument("--force-mode", choices=("none", "ranked", "hard"), default="ranked", help="ranked orders/filters tails; hard keeps only positive-score core/tail except protected points")
    parser.add_argument("--tail-min-score", type=float, default=None, help="Keep only tail pairs with score at least this threshold")
    parser.add_argument("--tail-top", type=int, default=None, help="Backward-compatible global tail cap for non-square scans")
    parser.add_argument("--tail-top-per-u", type=int, default=None, help="Keep this many top tail x values for each u")
    parser.add_argument("--global-pair-top", type=int, default=None, help="After building all pairs, keep only this many highest-scoring pairs")
    parser.add_argument("--no-protect-crt", action="store_true", help="Do not force inclusion of x_CRT(u)")
    parser.add_argument("--no-protect-2R", action="store_true", help="Do not force inclusion of the original u=1 checkpoint x=2R")

    parser.add_argument("--trial-bound", type=int, default=10000, help="Budget/limit for bounded factor extraction")
    parser.add_argument("--factor-method", choices=("trial", "sympy"), default="sympy", help="Factor extraction backend")
    parser.add_argument("--max-square-divisors", type=int, default=128, help="Max literal square-root divisors a per pair")
    parser.add_argument("--max-h-components", type=int, default=2, help="Max components multiplied into odd carrier h")
    parser.add_argument("--max-h-candidates", type=int, default=64, help="Max h carriers per a")
    parser.add_argument("--max-candidates-per-pair", type=int, default=2000, help="Max candidates tested per (x,u) pair")
    parser.add_argument("--max-s-shifts", type=int, default=0, help="Extra representatives s=s0+k2^x to try if u2^{x/2}>2^x")
    parser.add_argument("--no-full-residual-h", action="store_true", help="Do not include h=full residual F/a^2")

    parser.add_argument("--continue-after-factor", action="store_true", help="Continue scanning after a non-trivial factor is found")
    parser.add_argument("--quiet", action="store_true", help="Suppress per-pair logs")
    parser.add_argument("--top", type=int, default=10, help="Number of summary near-misses to print")
    parser.add_argument("--tee-log", default=None, help="Write the same stdout/stderr output to this log file and to the terminal")
    parser.add_argument("--tee-append", action="store_true", help="Append to --tee-log instead of overwriting it")
    parser.add_argument("--parallel", action="store_true", help="Use ProcessPoolExecutor for CPU-bound pair scans")
    parser.add_argument("--workers", type=int, default=None, help="Worker processes for --parallel")
    return parser


def main() -> int:
    try:
        sys.stdout.reconfigure(line_buffering=True)
        sys.stderr.reconfigure(line_buffering=True)
    except Exception:
        pass

    parser = build_parser()
    args = parser.parse_args()
    install_tee_logging(args.tee_log, args.tee_append)

    start = datetime.now().astimezone()
    status = "SUCCESS"
    exit_code = 0
    try:
        if args.range_mode == "square-optimized" and not args.square_multiplier_scan:
            args.range_mode = "ranked-core-tail"
        if args.force_mode == "none":
            rank_primes: List[int] = []
        else:
            rank_primes = parse_prime_list_csv(args.rank_force_primes)
        if args.force_depth < 1:
            raise ValueError("--force-depth must be positive")
        if args.workers is not None and args.workers <= 0:
            raise ValueError("--workers must be positive")
        if args.tail_top_per_u is not None and args.tail_top_per_u < 0:
            raise ValueError("--tail-top-per-u must be non-negative")
        if args.global_pair_top is not None and args.global_pair_top <= 0:
            raise ValueError("--global-pair-top must be positive")

        r_min, R, pairs, pair_scores = build_pair_plan(args.n, args, rank_primes)
        print_header(args, args.n, r_min, R, pairs, start)
        results = scan_all(args, args.n, pairs, pair_scores)
        print_summary(results, args.n, args.top)
    except Exception as exc:
        status = f"FAILED: {type(exc).__name__}: {exc}"
        exit_code = 1
        print("\nERROR", flush=True)
        print("=" * 72, flush=True)
        traceback.print_exc()
    finally:
        print_footer(start, status)
        close_tee_logging()
    return exit_code


if __name__ == "__main__":
    sys.exit(main())
