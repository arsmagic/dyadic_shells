#!/usr/bin/env python3
"""Empirical Weyl/exponential-sum profiles for base-power orbits modulo N."""
from __future__ import annotations
import argparse
from pathlib import Path
from typing import Dict, List

from base_shell_lib import read_csv, weyl_sum_profile, write_csv


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--inputs", nargs="+", required=True)
    ap.add_argument("--bases", nargs="+", type=int, default=[2, 3, 5, 7, 11])
    ap.add_argument("--h-values", nargs="+", type=int, default=list(range(1, 21)))
    ap.add_argument("--H-values", nargs="+", type=int, default=[10, 20, 50, 100, 200, 500])
    ap.add_argument("--max-N-per-file", type=int, default=50)
    ap.add_argument("--out", type=str, default="results/weyl_profiles.csv")
    args = ap.parse_args()

    rows: List[Dict[str, object]] = []
    for inp in args.inputs:
        for idx, row in enumerate(read_csv(inp)):
            if idx >= args.max_N_per_file:
                break
            n = int(row["N"])
            for b in args.bases:
                if n % b == 0:
                    continue
                prof = weyl_sum_profile(n, b, args.h_values, args.H_values)
                for pr in prof:
                    pr.update({
                        "N_id": row.get("N_id", f"{Path(inp).stem}_{idx}"),
                        "generator_type": row.get("generator_type", "unknown"),
                        "bit_length_actual": row.get("bit_length_actual", n.bit_length()),
                    })
                    rows.append(pr)
    fieldnames = ["N_id", "N", "bit_length_actual", "generator_type", "base", "h", "H", "normalized_magnitude"]
    write_csv(args.out, rows, fieldnames)
    print(f"Wrote {args.out}. rows={len(rows)}")

if __name__ == "__main__":
    main()
