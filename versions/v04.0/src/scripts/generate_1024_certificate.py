#!/usr/bin/env python3
"""Generate a 1024-bit sparse-center positive-control certificate.

The output JSON is designed for a reproducibility archive. The optional LaTeX
snippet summarizes the certificate without forcing the article body to carry
long integers.
"""

from __future__ import annotations

import argparse
import json
import math
import random
from pathlib import Path

from generate_semiprimes import generate_sparse_center_semiprime, write_json_record


def latex_int_block(name: str, value: int) -> str:
    return rf"\texttt{{{name}}} = \texttt{{{value}}}"


def write_latex_snippet(record, path: Path) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    data = record.to_json_dict()
    lines = []
    lines.append(r"\subsection{Sparse shifted center, 1024-bit scale}")
    lines.append(r"This certificate demonstrates that the construction is not tied to toy bit-lengths.")
    lines.append(r"\begin{itemize}")
    lines.append(rf"\item $r={record.r}$, window bits $={record.window_bits}$, Hamming weight $={record.weight}$.")
    lines.append(rf"\item $|\mathcal Z| = \binom{{{record.window_bits}}}{{{record.weight}}}$.")
    lines.append(rf"\item $\operatorname{{bitlen}}(n)={record.n.bit_length()}$, $\operatorname{{bitlen}}(p)={record.p.bit_length()}$, $\operatorname{{bitlen}}(q)={record.q.bit_length()}$.")
    lines.append(rf"\item Fermat iteration count from $\lceil\sqrt n\rceil$ to the true center: {record.fermat_iterations}.")
    lines.append(rf"\item Verified identity: $A^2-n=B^2$ is \texttt{{{data['identity_A2_minus_n_equals_B2']}}}; primality flags are $p$: \texttt{{{data['p_is_prime']}}}, $q$: \texttt{{{data['q_is_prime']}}}.")
    lines.append(r"\end{itemize}")
    lines.append(r"The full decimal certificate is included in the reproducibility archive as JSON.")
    path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description="Generate one 1024-bit sparse-center certificate.")
    parser.add_argument("--bit-size", type=int, default=1024)
    parser.add_argument("--window-bits", type=int, default=128)
    parser.add_argument("--weight", type=int, default=4)
    parser.add_argument("--seed", type=int, default=20260701)
    parser.add_argument("--out", type=Path, default=Path("certificates/example_1024.json"))
    parser.add_argument("--tex", type=Path, default=Path("tables/example_1024_certificate.tex"))
    parser.add_argument("--lambda-min", type=float, default=0.30)
    parser.add_argument("--lambda-max", type=float, default=0.75)
    parser.add_argument("--max-attempts", type=int, default=200000)
    args = parser.parse_args()

    rng = random.Random(args.seed)
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
    write_latex_snippet(rec, args.tex)
    print(json.dumps(rec.to_json_dict(), indent=2))
    print(f"wrote {args.out} and {args.tex}")


if __name__ == "__main__":
    main()
