#!/usr/bin/env python3
"""Compute public global-window capacity Cglob and calibrated null Zglob for semiprime CSV files."""
from __future__ import annotations
import argparse
from pathlib import Path
from typing import Dict, List

from base_shell_lib import compute_zglob_for_n, read_csv, write_csv


def process_file(path: Path, bases: List[int], theta_bands: List[tuple[float, float]], out_dir: Path) -> Path:
    rows_in = read_csv(path)
    rows_out: List[Dict[str, object]] = []
    for row in rows_in:
        n = int(row["N"])
        for theta0, theta1 in theta_bands:
            z = compute_zglob_for_n(n, bases, theta0, theta1)
            rows_out.append({
                "N_id": row.get("N_id", ""),
                "N": row["N"],
                "bit_length_actual": row.get("bit_length_actual", n.bit_length()),
                "generator_type": row.get("generator_type", "unknown"),
                "theta0": theta0, "theta1": theta1,
                **z,
            })
    out_path = out_dir / f"zglob_{path.stem}.csv"
    fieldnames = ["N_id", "N", "bit_length_actual", "generator_type", "theta0", "theta1", "bases", "num_heights", "Cglob", "mu", "sigma", "Zglob", "base_details_json"]
    write_csv(out_path, rows_out, fieldnames)
    return out_path


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--inputs", nargs="+", required=True, help="CSV files with N column")
    ap.add_argument("--bases", nargs="+", type=int, default=[2, 3, 5, 7, 11])
    ap.add_argument("--theta", nargs="+", type=float, default=[0.15, 0.35, 0.25, 0.50], help="Pairs theta0 theta1 ...")
    ap.add_argument("--out-dir", type=str, default="results")
    args = ap.parse_args()
    if len(args.theta) % 2 != 0:
        raise ValueError("--theta must contain pairs: theta0 theta1 ...")
    theta_bands = [(args.theta[i], args.theta[i+1]) for i in range(0, len(args.theta), 2)]
    out_dir = Path(args.out_dir); out_dir.mkdir(parents=True, exist_ok=True)
    for inp in args.inputs:
        out_path = process_file(Path(inp), args.bases, theta_bands, out_dir)
        print(f"Wrote {out_path}")

if __name__ == "__main__":
    main()
