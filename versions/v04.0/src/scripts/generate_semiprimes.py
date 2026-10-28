#!/usr/bin/env python3
"""Utilities for generating random and center-compressible semiprimes.

The functions in this file are intentionally deterministic under a Python
``random.Random`` instance so that benchmarks can be reproduced exactly.
They use SymPy primality testing, which is sufficient for the 64--1024 bit
positive-control experiments proposed for the article draft.
"""

from __future__ import annotations

import argparse
import json
import math
import random
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Iterable, List, Optional, Sequence, Tuple

from sympy import isprime, nextprime


@dataclass
class SemiprimeRecord:
    family: str
    bit_size: int
    r: int
    p: int
    q: int
    n: int
    A: int
    B: int
    z: Optional[int]
    window_bits: Optional[int]
    weight: Optional[int]
    attempts: int
    fermat_iterations: int

    def to_json_dict(self) -> dict:
        d = asdict(self)
        d.update(
            {
                "p_bits": int(self.p.bit_length()),
                "q_bits": int(self.q.bit_length()),
                "n_bits": int(self.n.bit_length()),
                "identity_A2_minus_n_equals_B2": (self.A * self.A - self.n == self.B * self.B),
                "p_is_prime": bool(isprime(self.p)),
                "q_is_prime": bool(isprime(self.q)),
            }
        )
        return d


def sparse_offsets(window_bits: int, weight: int) -> List[int]:
    """Return all non-negative offsets z < 2^window_bits of exact Hamming weight.

    For the experiments, this list is intentionally kept small enough to fit
    in memory (e.g. C(20,3)=1140, C(64,3)=41664). For very large windows use
    a streaming iterator instead.
    """
    if weight < 0 or weight > window_bits:
        raise ValueError("weight must satisfy 0 <= weight <= window_bits")
    offsets: List[int] = []

    def rec(start: int, left: int, value: int) -> None:
        if left == 0:
            offsets.append(value)
            return
        for pos in range(start, window_bits - left + 1):
            rec(pos + 1, left - 1, value | (1 << pos))

    rec(0, weight, 0)
    return offsets


def random_sparse_offset(window_bits: int, weight: int, rng: random.Random, *, require_even: bool = True) -> int:
    """Sample a sparse offset.

    ``require_even=True`` avoids setting bit 0. This keeps A=2^r+z even,
    which in turn makes p and q odd when p+q=2A.
    """
    if require_even and weight > window_bits - 1:
        raise ValueError("require_even leaves only window_bits-1 usable positions")
    positions = list(range(1 if require_even else 0, window_bits))
    chosen = rng.sample(positions, weight)
    z = 0
    for pos in chosen:
        z |= 1 << pos
    return z


def random_prime_with_bits(bits: int, rng: random.Random, max_attempts: int = 10000) -> Tuple[int, int]:
    """Generate an odd prime with exactly ``bits`` bits using nextprime."""
    if bits < 2:
        raise ValueError("bits must be >= 2")
    lo = 1 << (bits - 1)
    hi = 1 << bits
    for attempt in range(1, max_attempts + 1):
        cand = rng.randrange(lo, hi)
        cand |= 1
        p = int(nextprime(cand))
        if p < hi:
            return p, attempt
    raise RuntimeError(f"failed to generate a {bits}-bit prime after {max_attempts} attempts")


def generate_random_balanced_semiprime(bit_size: int, rng: random.Random) -> SemiprimeRecord:
    """Generate a random balanced semiprime for the random baseline."""
    r = bit_size // 2
    p, a1 = random_prime_with_bits(r, rng)
    q, a2 = random_prime_with_bits(r, rng)
    if p > q:
        p, q = q, p
    n = p * q
    A = (p + q) // 2
    B = (q - p) // 2
    return SemiprimeRecord(
        family="random_balanced",
        bit_size=bit_size,
        r=r,
        p=p,
        q=q,
        n=n,
        A=A,
        B=B,
        z=None,
        window_bits=None,
        weight=None,
        attempts=a1 + a2,
        fermat_iterations=A - (math.isqrt(n) if math.isqrt(n) ** 2 == n else math.isqrt(n) + 1),
    )


def generate_prime_pair_with_center(
    A: int,
    rng: random.Random,
    *,
    lambda_min: float = 0.30,
    lambda_max: float = 0.75,
    max_attempts: int = 20000,
) -> Tuple[int, int, int, int]:
    """Find primes p,q with p+q=2A and B=(q-p)/2 in [lambda_min*A, lambda_max*A].

    Instead of sampling B and testing both A-B and A+B for primality, we sample
    a prime p below A and test q=2A-p. This is much faster and still gives a
    certified center-compressible semiprime.
    """
    if not (0 < lambda_min < lambda_max < 1):
        raise ValueError("need 0 < lambda_min < lambda_max < 1")
    p_lo = max(3, int((1.0 - lambda_max) * A))
    p_hi = max(p_lo + 10, int((1.0 - lambda_min) * A))
    for attempt in range(1, max_attempts + 1):
        cand = rng.randrange(p_lo, p_hi)
        cand |= 1
        p = int(nextprime(cand))
        if p >= p_hi:
            continue
        q = 2 * A - p
        if q <= p or q % 2 == 0:
            continue
        if isprime(q):
            B = (q - p) // 2
            return p, q, B, attempt
    raise RuntimeError(
        f"failed to find prime pair with fixed center after {max_attempts} attempts; "
        f"try a different seed or increase max_attempts"
    )


def generate_sparse_center_semiprime(
    bit_size: int,
    window_bits: int,
    weight: int,
    rng: random.Random,
    *,
    lambda_min: float = 0.30,
    lambda_max: float = 0.75,
    max_attempts: int = 20000,
) -> SemiprimeRecord:
    """Generate a balanced sparse-center positive-control semiprime."""
    r = bit_size // 2
    z = random_sparse_offset(window_bits, weight, rng, require_even=True)
    A = (1 << r) + z
    p, q, B, attempts = generate_prime_pair_with_center(
        A, rng, lambda_min=lambda_min, lambda_max=lambda_max, max_attempts=max_attempts
    )
    n = p * q
    sqrt_n = math.isqrt(n)
    ceil_sqrt_n = sqrt_n if sqrt_n * sqrt_n == n else sqrt_n + 1
    return SemiprimeRecord(
        family="sparse_center",
        bit_size=bit_size,
        r=r,
        p=p,
        q=q,
        n=n,
        A=A,
        B=B,
        z=z,
        window_bits=window_bits,
        weight=weight,
        attempts=attempts,
        fermat_iterations=A - ceil_sqrt_n,
    )


def write_json_record(record: SemiprimeRecord, path: Path) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(record.to_json_dict(), indent=2), encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description="Generate random or sparse-center semiprimes.")
    parser.add_argument("--family", choices=["random", "sparse"], default="sparse")
    parser.add_argument("--bit-size", type=int, default=128)
    parser.add_argument("--window-bits", type=int, default=20)
    parser.add_argument("--weight", type=int, default=3)
    parser.add_argument("--seed", type=int, default=20260701)
    parser.add_argument("--out", type=Path, default=Path("certificates/example.json"))
    parser.add_argument("--lambda-min", type=float, default=0.30)
    parser.add_argument("--lambda-max", type=float, default=0.75)
    parser.add_argument("--max-attempts", type=int, default=20000)
    args = parser.parse_args()

    rng = random.Random(args.seed)
    if args.family == "random":
        rec = generate_random_balanced_semiprime(args.bit_size, rng)
    else:
        rec = generate_sparse_center_semiprime(
            args.bit_size,
            args.window_bits,
            args.weight,
            rng,
            lambda_min=args.lambda_min,
            lambda_max=args.lambda_max,
            max_attempts=args.max_attempts,
        )
    write_json_record(rec, args.out)
    print(json.dumps(rec.to_json_dict(), indent=2))


if __name__ == "__main__":
    main()
