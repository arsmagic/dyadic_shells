#!/usr/bin/env python3
"""Run the v0.4 reproducibility benchmark pipeline.

This wrapper intentionally delegates to the individual scripts so that each
experiment can also be rerun independently by reviewers.
"""

from __future__ import annotations

import argparse
import subprocess
import sys
from pathlib import Path


def run(cmd: list[str], cwd: Path) -> None:
    print("\n$ " + " ".join(cmd))
    subprocess.run(cmd, cwd=str(cwd), check=True)


def main() -> None:
    parser = argparse.ArgumentParser(description="Run v0.4 diagnostics and sieve benchmarks.")
    parser.add_argument("--seed", type=int, default=20260701)
    parser.add_argument("--samples", type=int, default=100)
    parser.add_argument("--bit-sizes", type=str, default="128,256")
    parser.add_argument("--window-bits", type=int, default=20)
    parser.add_argument("--weight", type=int, default=3)
    parser.add_argument("--moduli-count", type=int, default=24)
    parser.add_argument("--factor-base-size", type=int, default=12)
    parser.add_argument("--out-dir", type=Path, default=Path("."))
    parser.add_argument("--quick", action="store_true", help="small smoke-test settings")
    parser.add_argument("--skip-1024", action="store_true")
    args = parser.parse_args()

    root = args.out_dir.resolve()
    scripts = root / "scripts"
    results = root / "results"
    tables = root / "tables"
    certs = root / "certificates"
    results.mkdir(parents=True, exist_ok=True)
    tables.mkdir(parents=True, exist_ok=True)
    certs.mkdir(parents=True, exist_ok=True)

    if args.quick:
        bit_sizes = [64]
        samples = 3
        window_bits = 10
        weight = 2
        moduli_count = 8
        factor_base_size = 5
    else:
        bit_sizes = [int(x.strip()) for x in args.bit_sizes.split(",") if x.strip()]
        samples = args.samples
        window_bits = args.window_bits
        weight = args.weight
        moduli_count = args.moduli_count
        factor_base_size = args.factor_base_size

    for bit_size in bit_sizes:
        run(
            [
                sys.executable,
                str(scripts / "diagnostic_scores.py"),
                "--bit-size",
                str(bit_size),
                "--samples",
                str(samples),
                "--seed",
                str(args.seed + bit_size),
                "--window-bits",
                str(window_bits),
                "--weight",
                str(weight),
                "--moduli-count",
                str(moduli_count),
                "--out",
                str(results / f"diagnostics_{bit_size}.csv"),
            ],
            root,
        )
        run(
            [
                sys.executable,
                str(scripts / "sieve_benchmark.py"),
                "--bit-size",
                str(bit_size),
                "--samples",
                str(max(1, min(samples, 100))),
                "--seed",
                str(args.seed + 1000 + bit_size),
                "--window-bits",
                str(window_bits),
                "--weight",
                str(weight),
                "--factor-base-size",
                str(factor_base_size),
                "--out",
                str(results / f"sieve_{bit_size}.csv"),
            ],
            root,
        )

    run(
        [
            sys.executable,
            str(scripts / "make_latex_tables.py"),
            "--results-dir",
            str(results),
            "--tables-dir",
            str(tables),
        ],
        root,
    )

    if not args.quick and not args.skip_1024:
        run(
            [
                sys.executable,
                str(scripts / "generate_1024_certificate.py"),
                "--seed",
                str(args.seed),
                "--out",
                str(certs / "example_1024.json"),
                "--tex",
                str(tables / "example_1024_certificate.tex"),
            ],
            root,
        )

    print("\nPipeline finished. See results/, tables/, and certificates/.")


if __name__ == "__main__":
    main()
