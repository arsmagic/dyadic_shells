#!/usr/bin/env python3
"""
Exact finite-window sanity check.
Compares validation-mode closed-form count over E_N with brute-force enumeration for small A=b^r.
"""
from __future__ import annotations
import argparse
import random
from pathlib import Path
from typing import Dict, List

from base_shell_lib import (
    e_representatives,
    exact_window_count_for_class,
    brute_force_window_count,
    generate_balanced_semiprime,
    write_csv,
)


def run_case(n: int, p: int, q: int, b: int, r: int, max_bruteforce_A: int) -> Dict[str, object]:
    a = pow(b, r)
    theoretical = sum(exact_window_count_for_class(n, a, int(rep["e"])) for rep in e_representatives(p, q))
    brute = brute_force_window_count(n, a, max_bruteforce_A)
    return {
        "N": str(n), "p": str(p), "q": str(q), "bit_length": n.bit_length(),
        "base": b, "r": r, "A": str(a),
        "theoretical_count": theoretical,
        "brute_force_count": "SKIPPED" if brute is None else brute,
        "passed": "SKIPPED" if brute is None else (theoretical == brute),
    }


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--bits", nargs="+", type=int, default=[32, 40, 48, 56, 64])
    ap.add_argument("--samples", type=int, default=20)
    ap.add_argument("--bases", nargs="+", type=int, default=[2, 3, 5, 7])
    ap.add_argument("--r-max", type=int, default=20)
    ap.add_argument("--seed", type=int, default=20260628)
    ap.add_argument("--max-bruteforce-A", type=int, default=1_000_000)
    ap.add_argument("--out", type=str, default="results/exact_window_sanity.csv")
    args = ap.parse_args()

    rng = random.Random(args.seed)
    rows: List[Dict[str, object]] = []
    for bits in args.bits:
        for _ in range(args.samples):
            n, p, q = generate_balanced_semiprime(bits, rng)
            for b in args.bases:
                if n % b == 0:
                    continue
                for r in range(1, args.r_max + 1):
                    if pow(b, r) > args.max_bruteforce_A:
                        break
                    rows.append(run_case(n, p, q, b, r, args.max_bruteforce_A))

    fieldnames = ["N", "p", "q", "bit_length", "base", "r", "A", "theoretical_count", "brute_force_count", "passed"]
    write_csv(args.out, rows, fieldnames)
    failed = [row for row in rows if row["passed"] is False]
    print(f"Wrote {args.out}. cases={len(rows)}, failed={len(failed)}")
    if failed:
        raise SystemExit("Exact-window sanity check failed; inspect CSV.")

if __name__ == "__main__":
    main()
