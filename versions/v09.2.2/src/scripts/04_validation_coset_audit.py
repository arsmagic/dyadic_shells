#!/usr/bin/env python3
"""Validation-mode audit of CRT class distribution for finite-window representatives."""
from __future__ import annotations
import argparse
from pathlib import Path
from typing import Dict, List

from base_shell_lib import e_representatives, exact_window_representatives_for_class, theta_height_range, read_csv, write_csv


def audit_one(n: int, p: int, q: int, n_id: str, bases: List[int], theta0: float, theta1: float, max_emit_per_class: int) -> List[Dict[str, object]]:
    rows: List[Dict[str, object]] = []
    reps = e_representatives(p, q)
    for b in bases:
        if n % b == 0:
            continue
        for r in theta_height_range(n, b, theta0, theta1):
            a = pow(b, r)
            for rep in reps:
                ss = exact_window_representatives_for_class(n, a, int(rep["e"]), max_emit=max_emit_per_class)
                for s in ss:
                    gm = __import__("math").gcd(a - s, n)
                    gp = __import__("math").gcd(a + s, n)
                    rows.append({
                        "N_id": n_id, "N": str(n), "bit_length": n.bit_length(),
                        "base": b, "r": r, "A": str(a), "s": str(s),
                        "class_label": rep["label"], "is_mixed": rep["is_mixed"], "is_homogeneous": rep["is_homogeneous"],
                        "gcd_minus": str(gm), "gcd_plus": str(gp),
                        "nontrivial_gcd": (1 < gm < n) or (1 < gp < n),
                    })
    return rows


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--inputs", nargs="+", required=True, help="CSV files with N,p,q columns")
    ap.add_argument("--bases", nargs="+", type=int, default=[2, 3, 5, 7, 11])
    ap.add_argument("--theta0", type=float, default=0.15)
    ap.add_argument("--theta1", type=float, default=0.50)
    ap.add_argument("--max-emit-per-class", type=int, default=3)
    ap.add_argument("--out", type=str, default="results/validation_coset_audit.csv")
    args = ap.parse_args()

    rows: List[Dict[str, object]] = []
    for inp in args.inputs:
        for row in read_csv(inp):
            if not row.get("p") or not row.get("q"):
                continue
            n = int(row["N"]); p = int(row["p"]); q = int(row["q"])
            rows.extend(audit_one(n, p, q, row.get("N_id", Path(inp).stem), args.bases, args.theta0, args.theta1, args.max_emit_per_class))
    fieldnames = ["N_id", "N", "bit_length", "base", "r", "A", "s", "class_label", "is_mixed", "is_homogeneous", "gcd_minus", "gcd_plus", "nontrivial_gcd"]
    write_csv(args.out, rows, fieldnames)
    print(f"Wrote {args.out}. rows={len(rows)}")

if __name__ == "__main__":
    main()
