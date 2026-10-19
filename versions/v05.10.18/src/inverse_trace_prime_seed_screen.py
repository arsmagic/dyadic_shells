#!/usr/bin/env python3
"""
Protected-layer inverse-trace prime-seed screen for dyadic shell diagnostics.

Given an odd modulus n, this script fixes the protected layer x=2R by default,
where r_min is the least r with 2^(2r) >= n and R=2*r_min.  It computes

    M = 2^(2R),   a = n^(-1) mod M,

and maps every seed s0 to

    alpha0(s0) = -s0^2 * a mod M,
    lambda0(s0) = (alpha0(s0)*n + s0^2) / M.

The screen records whether lambda0=1, whether lambda0 is a square u^2, and
whether the corresponding gcd(u*2^R +/- s0, n) reveals a non-trivial factor.

This is a bounded diagnostic/statistical screen, not a complete factorization
algorithm.
"""

from __future__ import annotations

import argparse
import csv
import datetime as _dt
import heapq
import json
import math
import os
import sys
from dataclasses import dataclass, asdict
from pathlib import Path
from typing import Dict, Iterable, Iterator, List, Optional, Tuple
from math import gcd, isqrt


# ----------------------------- logging / tee -----------------------------

class Tee:
    def __init__(self, *streams):
        self.streams = streams

    def write(self, data: str) -> int:
        for s in self.streams:
            s.write(data)
            s.flush()
        return len(data)

    def flush(self) -> None:
        for s in self.streams:
            s.flush()


def setup_tee(path: Optional[str], append: bool = False):
    if not path:
        return None
    p = Path(path)
    p.parent.mkdir(parents=True, exist_ok=True)
    f = p.open("a" if append else "w", encoding="utf-8", buffering=1)
    sys.stdout = Tee(sys.__stdout__, f)  # type: ignore[assignment]
    sys.stderr = Tee(sys.__stderr__, f)  # type: ignore[assignment]
    return f


def now_iso() -> str:
    return _dt.datetime.now().astimezone().isoformat(timespec="seconds")


# ------------------------------ utilities -------------------------------

def parse_int(value: str) -> int:
    """Parse decimal/hex integer, allowing underscores and whitespace."""
    s = value.strip().replace("_", "")
    if s.startswith("@"):
        s = Path(s[1:]).read_text(encoding="utf-8").strip().replace("_", "")
    return int(s, 0)


def ceil_half_log2_semiprime_scale(n: int) -> int:
    """Return r_min = min r such that 2^(2r) >= n."""
    if n <= 0:
        raise ValueError("n must be positive")
    # Good initial estimate; adjust exactly.
    r = (n.bit_length() + 1) // 2
    while (1 << (2 * r)) < n:
        r += 1
    while r > 0 and (1 << (2 * (r - 1))) >= n:
        r -= 1
    return r


def simple_sieve_primes(limit: int) -> Iterator[int]:
    if limit < 2:
        return
    sieve = bytearray(b"\x01") * (limit + 1)
    sieve[0:2] = b"\x00\x00"
    for p in range(2, isqrt(limit) + 1):
        if sieve[p]:
            start = p * p
            sieve[start:limit + 1:p] = b"\x00" * (((limit - start) // p) + 1)
    for p in range(2, limit + 1):
        if sieve[p]:
            yield p


def seed_iterator(mode: str, bound: int) -> Iterator[int]:
    if bound < 1:
        return
    if mode in ("primes", "odd-primes"):
        try:
            from sympy import primerange  # type: ignore
            it = (int(p) for p in primerange(2, bound + 1))
        except Exception:
            it = simple_sieve_primes(bound)
        for p in it:
            if mode == "odd-primes" and p == 2:
                continue
            yield p
    elif mode == "integers":
        for s in range(1, bound + 1):
            yield s
    elif mode == "odd-integers":
        for s in range(1, bound + 1, 2):
            yield s
    else:
        raise ValueError(f"unknown seed mode: {mode}")


def is_square(n: int) -> Tuple[bool, int]:
    if n < 0:
        return False, 0
    r = isqrt(n)
    return r * r == n, r


def nearest_square_gap(n: int) -> Tuple[int, int]:
    """Return (gap, nearest_root_floor)."""
    if n <= 0:
        return (abs(n), 0)
    r = isqrt(n)
    g1 = n - r * r
    g2 = (r + 1) * (r + 1) - n
    return (g1 if g1 <= g2 else g2, r)


def fmt_log2_expectation(log2e: float) -> str:
    if math.isinf(log2e):
        return "0"
    return f"2^{log2e:.1f}"


@dataclass
class Hit:
    seed: int
    alpha0: int
    lambda0: int
    u: Optional[int]
    hit_type: str
    gcd_minus: Optional[int] = None
    gcd_plus: Optional[int] = None


@dataclass
class Summary:
    n_bits: int
    r_min: int
    R: int
    x: int
    modulus_bits: int
    seed_mode: str
    seed_bound: int
    seeds_processed: int = 0
    lambda1_hits: int = 0
    alpha_interval_hits: int = 0
    square_lambda_hits: int = 0
    square_lambda_hits_within_u_bound: int = 0
    nontrivial_factor_hits: int = 0
    min_lambda0: Optional[int] = None
    max_lambda0: Optional[int] = None
    min_lambda0_bits: Optional[int] = None
    max_lambda0_bits: Optional[int] = None
    mean_lambda0_bits: float = 0.0
    alpha_mod8: Optional[Dict[str, int]] = None
    lambda_mod8: Optional[Dict[str, int]] = None
    start_time: str = ""
    end_time: str = ""
    runtime_seconds: float = 0.0


# ------------------------------- main scan -------------------------------

def run_scan(args: argparse.Namespace) -> Tuple[Summary, List[Hit], List[Tuple[int, int, int, int]]]:
    n = parse_int(args.n)
    if n <= 1 or n % 2 == 0:
        raise ValueError("n must be an odd integer greater than 1")

    r_min = args.r_min if args.r_min is not None else ceil_half_log2_semiprime_scale(n)
    R = args.R if args.R is not None else 2 * r_min
    x = args.x if args.x is not None else 2 * R
    if x <= 0:
        raise ValueError("x must be positive")
    if (not args.allow_odd_x) and x % 2:
        raise ValueError("x must be even for the default square-multiplier gcd test; pass --allow-odd-x to override")

    M = 1 << x
    inv_n = pow(n % M, -1, M)
    half_x = x // 2
    scale = 1 << half_x

    summary = Summary(
        n_bits=n.bit_length(),
        r_min=r_min,
        R=R,
        x=x,
        modulus_bits=M.bit_length() - 1,
        seed_mode=args.seed_mode,
        seed_bound=args.seed_bound,
        alpha_mod8={str(i): 0 for i in range(8)},
        lambda_mod8={str(i): 0 for i in range(8)},
        start_time=now_iso(),
    )

    print("RUN START", summary.start_time)
    print("PARAMETERS")
    print(f"  n_bits             = {summary.n_bits}")
    print(f"  r_min              = {r_min}")
    print(f"  R                  = {R}")
    print(f"  x                  = {x}")
    print(f"  M_bits             = {summary.modulus_bits}")
    print(f"  seed_mode          = {args.seed_mode}")
    print(f"  seed_bound         = {args.seed_bound}")
    print(f"  u_bound            = {args.u_bound if args.u_bound is not None else 'unbounded for square test'}")
    print(f"  n                  = {n}")
    print()

    hits: List[Hit] = []
    # max-heap using negative gap for retaining smallest gaps: store (-gap, seed, lambda0, root_floor)
    near_heap: List[Tuple[int, int, int, int]] = []

    csv_file = None
    writer = None
    if args.csv:
        p = Path(args.csv)
        p.parent.mkdir(parents=True, exist_ok=True)
        csv_file = p.open("w", newline="", encoding="utf-8")
        writer = csv.writer(csv_file)
        writer.writerow([
            "seed", "alpha0", "lambda0", "lambda0_bits", "lambda0_mod8",
            "is_square_lambda", "u", "u_within_bound", "gcd_minus", "gcd_plus",
            "alpha_interval_hit", "lambda1_hit", "nearest_square_gap"
        ])

    t0 = _dt.datetime.now().astimezone()
    try:
        for s in seed_iterator(args.seed_mode, args.seed_bound):
            if args.max_seeds is not None and summary.seeds_processed >= args.max_seeds:
                break
            summary.seeds_processed += 1

            s2_mod = (s * s) % M
            alpha0 = (-s2_mod * inv_n) % M
            # Since alpha0*n+s^2 can be large, use exact integer s^2 here, not s^2 mod M.
            numerator = alpha0 * n + s * s
            lambda0 = numerator // M
            if numerator % M != 0:
                raise AssertionError("internal divisibility failure")

            lam_bits = lambda0.bit_length()
            summary.min_lambda0 = lambda0 if summary.min_lambda0 is None else min(summary.min_lambda0, lambda0)
            summary.max_lambda0 = lambda0 if summary.max_lambda0 is None else max(summary.max_lambda0, lambda0)
            summary.min_lambda0_bits = lam_bits if summary.min_lambda0_bits is None else min(summary.min_lambda0_bits, lam_bits)
            summary.max_lambda0_bits = lam_bits if summary.max_lambda0_bits is None else max(summary.max_lambda0_bits, lam_bits)
            # streaming mean
            k = summary.seeds_processed
            summary.mean_lambda0_bits += (lam_bits - summary.mean_lambda0_bits) / k
            summary.alpha_mod8[str(alpha0 & 7)] += 1  # type: ignore[index]
            summary.lambda_mod8[str(lambda0 & 7)] += 1  # type: ignore[index]

            # original lambda=1/admissibility checks at x=2R; alpha interval only meaningful if M > s^2
            lambda1_hit = (lambda0 == 1)
            if lambda1_hit:
                summary.lambda1_hits += 1

            alpha_interval_hit = False
            if M > s * s:
                alpha_upper = (M - 1 - s * s) // n
                if 1 <= alpha0 <= alpha_upper:
                    alpha_interval_hit = True
                    summary.alpha_interval_hits += 1

            sq, u = is_square(lambda0)
            u_within = bool(sq and (args.u_bound is None or u <= args.u_bound))
            gminus = gplus = None
            nontrivial = False
            if sq and lambda0 > 0:
                summary.square_lambda_hits += 1
                if u_within:
                    summary.square_lambda_hits_within_u_bound += 1
                    if x % 2 == 0:
                        gminus = gcd(u * scale - s, n)
                        gplus = gcd(u * scale + s, n)
                        nontrivial = (1 < gminus < n) or (1 < gplus < n)
                        if nontrivial:
                            summary.nontrivial_factor_hits += 1

            gap, root_floor = nearest_square_gap(lambda0)
            if args.near_square_top > 0:
                item = (-gap, s, lambda0, root_floor)
                if len(near_heap) < args.near_square_top:
                    heapq.heappush(near_heap, item)
                elif item > near_heap[0]:
                    heapq.heapreplace(near_heap, item)

            hit_type = None
            if lambda1_hit:
                hit_type = "lambda1"
            elif sq:
                hit_type = "square_lambda"
            elif alpha_interval_hit:
                hit_type = "alpha_interval"
            elif nontrivial:
                hit_type = "factor"

            if hit_type is not None or nontrivial:
                h = Hit(
                    seed=s, alpha0=alpha0, lambda0=lambda0,
                    u=(u if sq else None), hit_type=("factor" if nontrivial else hit_type),
                    gcd_minus=gminus, gcd_plus=gplus,
                )
                hits.append(h)
                print("HIT", json.dumps(asdict(h), ensure_ascii=False))

            if writer and (args.csv_all or hit_type is not None or nontrivial):
                writer.writerow([
                    s, alpha0, lambda0, lam_bits, lambda0 & 7,
                    int(sq), (u if sq else ""), int(u_within),
                    (gminus if gminus is not None else ""),
                    (gplus if gplus is not None else ""),
                    int(alpha_interval_hit), int(lambda1_hit), gap,
                ])

            if args.progress_every and summary.seeds_processed % args.progress_every == 0:
                print(f"PROGRESS seeds={summary.seeds_processed} hits={len(hits)} square_hits={summary.square_lambda_hits} factors={summary.nontrivial_factor_hits}")
    finally:
        if csv_file:
            csv_file.close()

    t1 = _dt.datetime.now().astimezone()
    summary.end_time = now_iso()
    summary.runtime_seconds = (t1 - t0).total_seconds()

    # Near heap currently has negative gaps; sort increasing actual gap.
    near = sorted([(-g, s, lam, rf) for (g, s, lam, rf) in near_heap], key=lambda x: x[0])

    print()
    print("SUMMARY")
    for key, value in asdict(summary).items():
        if key in ("min_lambda0", "max_lambda0") and value is not None and len(str(value)) > 120:
            print(f"  {key:32s} = <{len(str(value))} decimal digits>")
        else:
            print(f"  {key:32s} = {value}")

    if summary.seeds_processed:
        log2_count = math.log2(summary.seeds_processed)
        print("HEURISTIC_EXPECTATIONS")
        print(f"  lambda1_hits_expected_log2        ~= {fmt_log2_expectation(log2_count - math.log2(n))}")
        print(f"  unrestricted_square_expected_log2 ~= {fmt_log2_expectation(log2_count - 0.5 * math.log2(n))}")
        if args.u_bound is not None:
            print(f"  u_bounded_square_expected_log2    ~= {fmt_log2_expectation(log2_count + math.log2(args.u_bound) - math.log2(n))}")

    if near:
        print("NEAREST_SQUARE_GAPS")
        for gap, s, lam, root_floor in near:
            print(f"  seed={s} gap={gap} floor_root={root_floor} lambda_bits={lam.bit_length()}")

    print("RUN END", summary.end_time)
    return summary, hits, near


def build_arg_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(
        description="Protected-layer inverse-trace prime-seed dyadic screening."
    )
    p.add_argument("--n", required=True, help="Odd modulus n, decimal/hex, or @file containing the integer")
    p.add_argument("--r-min", type=int, default=None, help="Override r_min; default: min r with 2^(2r) >= n")
    p.add_argument("--R", type=int, default=None, help="Override R; default: 2*r_min")
    p.add_argument("--x", type=int, default=None, help="Override x; default: 2R")
    p.add_argument("--seed-mode", choices=["primes", "odd-primes", "integers", "odd-integers"], default="primes")
    p.add_argument("--seed-bound", type=int, default=1_000_000, help="Inclusive upper bound for seeds")
    p.add_argument("--max-seeds", type=int, default=None, help="Stop after this many generated seeds")
    p.add_argument("--u-bound", type=int, default=None, help="Only gcd-test square lambda hits with u <= this bound")
    p.add_argument("--csv", default=None, help="Write CSV rows for hits, or all rows with --csv-all")
    p.add_argument("--csv-all", action="store_true", help="Write all seed rows to CSV, not only hits")
    p.add_argument("--json-summary", default=None, help="Write summary JSON file")
    p.add_argument("--near-square-top", type=int, default=10, help="Record this many closest non-square lambda0 values")
    p.add_argument("--progress-every", type=int, default=0, help="Print progress every N seeds; 0 disables")
    p.add_argument("--tee-log", default=None, help="Duplicate stdout/stderr to this log file")
    p.add_argument("--tee-append", action="store_true", help="Append to --tee-log instead of overwriting")
    p.add_argument("--allow-odd-x", action="store_true", help="Allow odd x; square-multiplier gcd tests are only applied cleanly at even x")
    return p


def main(argv: Optional[List[str]] = None) -> int:
    parser = build_arg_parser()
    args = parser.parse_args(argv)
    log_handle = setup_tee(args.tee_log, args.tee_append)
    try:
        summary, hits, near = run_scan(args)
        if args.json_summary:
            p = Path(args.json_summary)
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_text(json.dumps({
                "summary": asdict(summary),
                "hits": [asdict(h) for h in hits],
                "nearest_square_gaps": [
                    {"gap": g, "seed": s, "lambda0": lam, "floor_root": rf}
                    for g, s, lam, rf in near
                ],
            }, ensure_ascii=False, indent=2), encoding="utf-8")
        return 0
    except KeyboardInterrupt:
        print("Interrupted by user", file=sys.stderr)
        return 130
    finally:
        if log_handle:
            log_handle.close()


if __name__ == "__main__":
    raise SystemExit(main())
