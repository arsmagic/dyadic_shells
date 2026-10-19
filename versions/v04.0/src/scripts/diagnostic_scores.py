#!/usr/bin/env python3
"""Compute public modular diagnostic scores for center-compressible semiprimes.

The diagnostic follows the per-candidate version recommended for v0.4:
for each candidate center A in a public set, compute

    T_A(n; M) = sum_m 1[(A^2 - alpha*n) mod m is a quadratic residue].

For alpha=1 and a true center A0=(p+q)/2 in the candidate set, T_A0 equals
|M|. Random false centers receive a full score with probability approximately
prod_m |QR(m)|/m, yielding a simple family-wise false-positive bound.
"""

from __future__ import annotations

import argparse
import csv
import math
import random
import time
from pathlib import Path
from typing import Dict, Iterable, List, Sequence, Tuple

from sympy import primerange

from generate_semiprimes import (
    generate_random_balanced_semiprime,
    generate_sparse_center_semiprime,
    sparse_offsets,
)


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


def score_center(n: int, A: int, moduli: Sequence[int], qr: Dict[int, set], *, alpha: int = 1) -> int:
    return sum(1 for m in moduli if ((A * A - alpha * n) % m) in qr[m])


def score_profile(
    n: int,
    centers: Sequence[int],
    moduli: Sequence[int],
    qr: Dict[int, set],
    *,
    alpha: int = 1,
) -> Tuple[int, int, int]:
    """Return (tmax, full_hits, best_index)."""
    best_score = -1
    full_hits = 0
    best_idx = -1
    full = len(moduli)
    for i, A in enumerate(centers):
        s = score_center(n, A, moduli, qr, alpha=alpha)
        if s == full:
            full_hits += 1
        if s > best_score:
            best_score = s
            best_idx = i
    return best_score, full_hits, best_idx


def random_residue_full_hit_probability(moduli: Sequence[int]) -> float:
    prob = 1.0
    for m in moduli:
        prob *= (m + 1) / (2 * m)  # QR including 0 among residues modulo odd prime m
    return prob


def run_diagnostics(
    *,
    bit_size: int,
    samples: int,
    seed: int,
    window_bits: int,
    weight: int,
    moduli_count: int,
    out: Path,
    lambda_min: float,
    lambda_max: float,
    max_attempts: int,
) -> None:
    rng = random.Random(seed)
    r = bit_size // 2
    centers = candidate_centers(r, window_bits, weight)
    moduli = odd_prime_moduli(moduli_count)
    qr = quadratic_residue_sets(moduli)
    full_prob = random_residue_full_hit_probability(moduli)
    familywise_bound = min(1.0, len(centers) * full_prob)

    out.parent.mkdir(parents=True, exist_ok=True)
    with out.open("w", newline="", encoding="utf-8") as f:
        writer = csv.DictWriter(
            f,
            fieldnames=[
                "family",
                "sample_index",
                "bit_size",
                "n_bits",
                "r",
                "window_bits",
                "weight",
                "center_set_size",
                "moduli_count",
                "moduli",
                "full_score_threshold",
                "tmax",
                "full_hits",
                "has_full_hit",
                "best_index",
                "true_score",
                "true_center_in_set",
                "true_positive",
                "fermat_iterations",
                "generation_attempts",
                "random_residue_full_hit_prob",
                "familywise_false_positive_bound",
                "elapsed_seconds",
            ],
        )
        writer.writeheader()

        for family in ["random_balanced", "sparse_center"]:
            for i in range(samples):
                t0 = time.perf_counter()
                if family == "random_balanced":
                    rec = generate_random_balanced_semiprime(bit_size, rng)
                    true_score = ""
                    true_center_in_set = False
                    true_positive = ""
                else:
                    rec = generate_sparse_center_semiprime(
                        bit_size,
                        window_bits,
                        weight,
                        rng,
                        lambda_min=lambda_min,
                        lambda_max=lambda_max,
                        max_attempts=max_attempts,
                    )
                    true_score_int = score_center(rec.n, rec.A, moduli, qr)
                    true_score = true_score_int
                    true_center_in_set = rec.A in centers
                    true_positive = bool(true_center_in_set and true_score_int == len(moduli))

                tmax, full_hits, best_idx = score_profile(rec.n, centers, moduli, qr)
                elapsed = time.perf_counter() - t0
                writer.writerow(
                    {
                        "family": family,
                        "sample_index": i,
                        "bit_size": bit_size,
                        "n_bits": rec.n.bit_length(),
                        "r": r,
                        "window_bits": window_bits,
                        "weight": weight,
                        "center_set_size": len(centers),
                        "moduli_count": len(moduli),
                        "moduli": " ".join(map(str, moduli)),
                        "full_score_threshold": len(moduli),
                        "tmax": tmax,
                        "full_hits": full_hits,
                        "has_full_hit": bool(full_hits > 0),
                        "best_index": best_idx,
                        "true_score": true_score,
                        "true_center_in_set": true_center_in_set,
                        "true_positive": true_positive,
                        "fermat_iterations": rec.fermat_iterations,
                        "generation_attempts": rec.attempts,
                        "random_residue_full_hit_prob": full_prob,
                        "familywise_false_positive_bound": familywise_bound,
                        "elapsed_seconds": f"{elapsed:.6f}",
                    }
                )
                print(
                    f"[{bit_size}] {family} {i+1}/{samples}: tmax={tmax}, full_hits={full_hits}, elapsed={elapsed:.3f}s"
                )


def main() -> None:
    parser = argparse.ArgumentParser(description="Run public modular diagnostic-score experiments.")
    parser.add_argument("--bit-size", type=int, default=128)
    parser.add_argument("--samples", type=int, default=100)
    parser.add_argument("--seed", type=int, default=20260701)
    parser.add_argument("--window-bits", type=int, default=20)
    parser.add_argument("--weight", type=int, default=3)
    parser.add_argument("--moduli-count", type=int, default=24)
    parser.add_argument("--out", type=Path, default=Path("results/diagnostics_128.csv"))
    parser.add_argument("--lambda-min", type=float, default=0.30)
    parser.add_argument("--lambda-max", type=float, default=0.75)
    parser.add_argument("--max-attempts", type=int, default=20000)
    args = parser.parse_args()
    run_diagnostics(**vars(args))


if __name__ == "__main__":
    main()
