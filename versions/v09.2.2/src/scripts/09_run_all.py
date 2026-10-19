#!/usr/bin/env python3
"""Convenience runner for a small reproducible experimental pipeline."""
from __future__ import annotations
import argparse
import subprocess
import sys
from pathlib import Path

from base_shell_lib import ExperimentConfig, ensure_dirs, manifest, write_json


def run(cmd: list[str], cwd: Path) -> None:
    print("\n$", " ".join(cmd))
    subprocess.run(cmd, cwd=str(cwd), check=True)


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--bits", nargs="+", type=int, default=[64, 96, 128])
    ap.add_argument("--samples", type=int, default=50, help="Use 50 for smoke test; 200+ for paper runs")
    ap.add_argument("--bases", nargs="+", type=int, default=[2, 3, 5, 7, 11])
    ap.add_argument("--seed", type=int, default=20260628)
    ap.add_argument("--skip-generation", action="store_true")
    ap.add_argument("--skip-weyl", action="store_true")
    args = ap.parse_args()

    root = Path(__file__).resolve().parents[1]
    ensure_dirs(root)
    py = sys.executable
    bits_str = [str(b) for b in args.bits]
    bases_str = [str(b) for b in args.bases]

    if not args.skip_generation:
        run([py, "scripts/01_generate_semiprimes.py", "--bits", *bits_str, "--samples", str(args.samples), "--seed", str(args.seed), "--out", "data"], root)

    # Sanity checks use smaller bit lengths; harmless even in main run.
    run([py, "scripts/02_exact_window_sanity.py", "--bits", "32", "40", "48", "--samples", "10", "--out", "results/exact_window_sanity.csv"], root)

    input_files = []
    for b in args.bits:
        input_files.extend([f"data/random_{b}.csv", f"data/biased_{b}.csv"])
    run([py, "scripts/03_compute_zglob.py", "--inputs", *input_files, "--bases", *bases_str, "--out-dir", "results"], root)

    zglob_files = [str(p) for p in sorted((root / "results").glob("zglob_*.csv"))]
    run([py, "scripts/07_analyze_statistics.py", "--inputs", *[str(Path(f).relative_to(root)) for f in zglob_files]], root)

    # Validation coset audit on smaller generated files to keep runtime controlled.
    validation_inputs = [f"data/random_{args.bits[0]}.csv", f"data/biased_{args.bits[0]}.csv"]
    run([py, "scripts/04_validation_coset_audit.py", "--inputs", *validation_inputs, "--bases", *bases_str, "--out", "results/validation_coset_audit.csv"], root)

    if not args.skip_weyl:
        run([py, "scripts/06_weyl_profile.py", "--inputs", *validation_inputs, "--bases", *bases_str, "--max-N-per-file", "10", "--out", "results/weyl_profiles.csv"], root)

    run([py, "scripts/08_make_tables_figures.py", "--zglob-files", *[str(Path(f).relative_to(root)) for f in zglob_files], "--out-dir", "figures"], root)

    cfg = ExperimentConfig(seed=args.seed, bit_lengths=tuple(args.bits), bases=tuple(args.bases), population_size_small=args.samples)
    write_json(root / "manifest.json", manifest(root, cfg, extra={"runner": "09_run_all.py"}))
    print("\nPipeline completed. See results/, figures/, and manifest.json")

if __name__ == "__main__":
    main()
