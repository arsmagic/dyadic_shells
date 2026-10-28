#!/usr/bin/env python3
"""Generate article-ready tables and basic figures from result CSVs."""
from __future__ import annotations
import argparse
from pathlib import Path
from typing import Dict, List

from base_shell_lib import read_csv, write_csv

try:
    import matplotlib.pyplot as plt  # type: ignore
except Exception:  # pragma: no cover
    plt = None


def make_zglob_histogram(zglob_files: List[str], out_dir: Path) -> None:
    if plt is None:
        print("matplotlib not available; skipping figures")
        return
    rows = []
    for f in zglob_files:
        rows.extend(read_csv(f))
    # Group by theta band and bit length lightly; one combined figure is robust.
    by_gen: Dict[str, List[float]] = {}
    for row in rows:
        gen = row.get("generator_type", "unknown")
        by_gen.setdefault(gen, []).append(float(row["Zglob"]))
    if not by_gen:
        return
    plt.figure(figsize=(8, 5))
    for gen, vals in sorted(by_gen.items()):
        plt.hist(vals, bins=30, alpha=0.5, label=gen)
    plt.xlabel("Zglob")
    plt.ylabel("count")
    plt.title("Public global-window anomaly scores")
    plt.legend()
    plt.tight_layout()
    plt.savefig(out_dir / "zglob_histogram.png", dpi=200)
    plt.close()


def make_weyl_plot(weyl_csv: str, out_dir: Path) -> None:
    if plt is None or not Path(weyl_csv).exists():
        return
    rows = read_csv(weyl_csv)
    # Plot aggregated median-ish by H using mean fallback.
    by_H: Dict[int, List[float]] = {}
    for row in rows:
        if row.get("h") != "1":
            continue
        H = int(row["H"])
        by_H.setdefault(H, []).append(float(row["normalized_magnitude"]))
    if not by_H:
        return
    xs = sorted(by_H)
    ys = [sum(by_H[x]) / len(by_H[x]) for x in xs]
    plt.figure(figsize=(8, 5))
    plt.plot(xs, ys, marker="o")
    plt.xlabel("H")
    plt.ylabel("mean |S_H(1)| / H")
    plt.title("Empirical Weyl profile")
    plt.tight_layout()
    plt.savefig(out_dir / "weyl_profile_h1.png", dpi=200)
    plt.close()


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--zglob-files", nargs="*", default=[])
    ap.add_argument("--summary", default="results/statistical_summary.csv")
    ap.add_argument("--pairwise", default="results/pairwise_tests.csv")
    ap.add_argument("--weyl", default="results/weyl_profiles.csv")
    ap.add_argument("--out-dir", default="figures")
    args = ap.parse_args()
    out_dir = Path(args.out_dir); out_dir.mkdir(parents=True, exist_ok=True)
    if args.zglob_files:
        make_zglob_histogram(args.zglob_files, out_dir)
    make_weyl_plot(args.weyl, out_dir)
    print(f"Figures written to {out_dir}")

if __name__ == "__main__":
    main()
