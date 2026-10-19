#!/usr/bin/env python3
"""
Run public-mode screening on legacy benchmark moduli.

The JSON file should contain entries such as:
[
  {"name":"RSA-110", "N":"...", "category":"rsa_challenge", "factors_known":true, "p":"...", "q":"..."},
  {"name":"ROCA-1024", "N":"...", "category":"structured_single_instance", "factors_known":false}
]

No legacy constants are hard-coded here to avoid accidental transcription errors.
"""
from __future__ import annotations
import argparse
import math
from pathlib import Path
from typing import Dict, List

from base_shell_lib import read_json, write_csv, compute_zglob_for_n, theta_height_range, public_global_indicator, e_representatives, exact_window_representatives_for_class


def public_scan(n: int, bases: List[int], theta0: float, theta1: float) -> Dict[str, object]:
    public_hits = 0
    nontrivial_gcd_events = 0
    height_count = 0
    for b in bases:
        if math.gcd(b, n) != 1:
            continue
        for r in theta_height_range(n, b, theta0, theta1):
            a = pow(b, r)
            x = pow(b, r, n)
            candidates = []
            if x < a:
                candidates.append(x)
            if x > n - a:
                candidates.append(n - x)
            public_hits += len(candidates)
            height_count += 1
            for s in candidates:
                for delta in (a - s, a + s):
                    g = math.gcd(delta, n)
                    if 1 < g < n:
                        nontrivial_gcd_events += 1
    return {"public_hits": public_hits, "nontrivial_gcd_events": nontrivial_gcd_events, "height_count": height_count}


def validation_full_class_count(n: int, p: int, q: int, bases: List[int], theta0: float, theta1: float) -> Dict[str, int]:
    counts = {"++": 0, "--": 0, "+-": 0, "-+": 0}
    for b in bases:
        if math.gcd(b, n) != 1:
            continue
        for r in theta_height_range(n, b, theta0, theta1):
            a = pow(b, r)
            for rep in e_representatives(p, q):
                label = str(rep["label"])
                counts[label] += len(exact_window_representatives_for_class(n, a, int(rep["e"]), max_emit=None))
    return counts


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--legacy-json", default="data/legacy_moduli.json")
    ap.add_argument("--bases", nargs="+", type=int, default=[2, 3, 5, 7, 11])
    ap.add_argument("--theta", nargs="+", type=float, default=[0.15, 0.35, 0.25, 0.50])
    ap.add_argument("--out", default="results/legacy_summary.csv")
    args = ap.parse_args()
    if len(args.theta) % 2 != 0:
        raise ValueError("--theta must contain pairs theta0 theta1")
    entries = read_json(args.legacy_json)
    rows: List[Dict[str, object]] = []
    for ent in entries:  # type: ignore[assignment]
        name = ent["name"]
        n = int(ent["N"])
        for i in range(0, len(args.theta), 2):
            theta0, theta1 = args.theta[i], args.theta[i+1]
            z = compute_zglob_for_n(n, args.bases, theta0, theta1)
            ps = public_scan(n, args.bases, theta0, theta1)
            row: Dict[str, object] = {
                "name": name,
                "category": ent.get("category", "legacy"),
                "bit_length": n.bit_length(),
                "theta0": theta0, "theta1": theta1,
                **z,
                **ps,
            }
            if ent.get("factors_known") and ent.get("p") and ent.get("q"):
                counts = validation_full_class_count(n, int(ent["p"]), int(ent["q"]), args.bases, theta0, theta1)
                row.update({f"class_{k}": v for k, v in counts.items()})
            rows.append(row)
    fieldnames = sorted({k for row in rows for k in row.keys()})
    write_csv(args.out, rows, fieldnames)
    print(f"Wrote {args.out}. rows={len(rows)}")

if __name__ == "__main__":
    main()
