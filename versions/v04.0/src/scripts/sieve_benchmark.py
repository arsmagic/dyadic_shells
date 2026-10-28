#!/usr/bin/env python3
"""Benchmark the modular quadratic-residue sieve for shifted-shell scans.

The sieve is a pre-filter: it keeps candidate centers A for which
A^2 - alpha*n is a quadratic residue modulo each small prime in a factor base.
It must *not* require A^2-alpha*n == 0 modulo p; the true center generally
satisfies A0^2-alpha*n = B^2, which is a QR modulo p but not usually zero.
"""

from __future__ import annotations

import argparse
import csv
import math
import random
import time
from pathlib import Path
from typing import Dict, List, Sequence, Tuple

from sympy import primerange

from generate_semiprimes import generate_sparse_center_semiprime, sparse_offsets


def odd_prime_moduli(count: int, *, start: int = 3) -> List[int]:
    primes = []
    for p in primerange(start, 10000):
        if p % 2 == 1:
            primes.append(int(p))
            if len(primes) == count:
                return primes
    raise RuntimeError("increase primerange bound")


def quadratic_residue_sets(moduli: Sequence[int]) -> Dict[int, set]:
    return {m: {pow(x, 2, m) for x in range(m)} for m in moduli}


def candidate_centers(r: int, window_bits: int, weight: int) -> List[int]:
    base = 1 << r
    return [base + z for z in sparse_offsets(window_bits, weight)]


def is_square_nonnegative(x: int) -> bool:
    if x < 0:
        return False
    y = math.isqrt(x)
    return y * y == x


def qr_sieve_survivors(
    n: int,
    centers: Sequence[int],
    moduli: Sequence[int],
    qr: Dict[int, set],
    *,
    alpha: int = 1,
) -> List[int]:
    survivors = []
    for A in centers:
        ok = True
        for m in moduli:
            if ((A * A - alpha * n) % m) not in qr[m]:
                ok = False
                break
        if ok:
            survivors.append(A)
    return survivors


def theoretical_survival_fraction(moduli: Sequence[int]) -> float:
    rho = 1.0
    for m in moduli:
        rho *= (m + 1) / (2 * m)
    return rho


def run_sieve_benchmark(
    *,
    bit_size: int,
    samples: int,
    seed: int,
    window_bits: int,
    weight: int,
    factor_base_size: int,
    out: Path,
    lambda_min: float,
    lambda_max: float,
    max_attempts: int,
) -> None:
    rng = random.Random(seed)
    r = bit_size // 2
    centers = candidate_centers(r, window_bits, weight)
    moduli = odd_prime_moduli(factor_base_size)
    qr = quadratic_residue_sets(moduli)
    rho = theoretical_survival_fraction(moduli)

    out.parent.mkdir(parents=True, exist_ok=True)
    with out.open("w", newline="", encoding="utf-8") as f:
        writer = csv.DictWriter(
            f,
            fieldnames=[
                "sample_index",
                "bit_size",
                "n_bits",
                "r",
                "window_bits",
                "weight",
                "center_set_size",
                "factor_base_size",
                "moduli",
                "theoretical_survival_fraction",
                "theoretical_survivors",
                "empirical_survivors",
                "true_center_survived",
                "exact_square_tests_naive",
                "exact_square_tests_after_sieve",
                "estimated_exact_test_speedup",
                "sieve_elapsed_seconds",
                "naive_square_elapsed_seconds",
                "generation_attempts",
                "fermat_iterations",
            ],
        )
        writer.writeheader()
        for i in range(samples):
            rec = generate_sparse_center_semiprime(
                bit_size,
                window_bits,
                weight,
                rng,
                lambda_min=lambda_min,
                lambda_max=lambda_max,
                max_attempts=max_attempts,
            )

            t0 = time.perf_counter()
            survivors = qr_sieve_survivors(rec.n, centers, moduli, qr)
            sieve_elapsed = time.perf_counter() - t0

            # Naive exact-square scan timing is included as a small-scale baseline.
            t1 = time.perf_counter()
            naive_hits = 0
            for A in centers:
                if is_square_nonnegative(A * A - rec.n):
                    naive_hits += 1
            naive_elapsed = time.perf_counter() - t1

            true_survived = rec.A in survivors
            empirical_survivors = len(survivors)
            speedup = len(centers) / max(1, empirical_survivors)

            writer.writerow(
                {
                    "sample_index": i,
                    "bit_size": bit_size,
                    "n_bits": rec.n.bit_length(),
                    "r": r,
                    "window_bits": window_bits,
                    "weight": weight,
                    "center_set_size": len(centers),
                    "factor_base_size": len(moduli),
                    "moduli": " ".join(map(str, moduli)),
                    "theoretical_survival_fraction": rho,
                    "theoretical_survivors": rho * len(centers),
                    "empirical_survivors": empirical_survivors,
                    "true_center_survived": bool(true_survived),
                    "exact_square_tests_naive": len(centers),
                    "exact_square_tests_after_sieve": empirical_survivors,
                    "estimated_exact_test_speedup": speedup,
                    "sieve_elapsed_seconds": f"{sieve_elapsed:.6f}",
                    "naive_square_elapsed_seconds": f"{naive_elapsed:.6f}",
                    "generation_attempts": rec.attempts,
                    "fermat_iterations": rec.fermat_iterations,
                }
            )
            print(
                f"[{bit_size}] sieve {i+1}/{samples}: survivors={empirical_survivors}, "
                f"speedup~{speedup:.1f}x, true_survived={true_survived}"
            )


def main() -> None:
    parser = argparse.ArgumentParser(description="Benchmark the QR sieve for shifted-shell scans.")
    parser.add_argument("--bit-size", type=int, default=128)
    parser.add_argument("--samples", type=int, default=100)
    parser.add_argument("--seed", type=int, default=20260701)
    parser.add_argument("--window-bits", type=int, default=20)
    parser.add_argument("--weight", type=int, default=3)
    parser.add_argument("--factor-base-size", type=int, default=12)
    parser.add_argument("--out", type=Path, default=Path("results/sieve_128.csv"))
    parser.add_argument("--lambda-min", type=float, default=0.30)
    parser.add_argument("--lambda-max", type=float, default=0.75)
    parser.add_argument("--max-attempts", type=int, default=20000)
    args = parser.parse_args()
    run_sieve_benchmark(**vars(args))


if __name__ == "__main__":
    main()
