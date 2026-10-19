#!/usr/bin/env python3
"""
Parse improved_polynomial_screening_v11.py logs and emit Appendix-C style tables.

Usage:
    python parse_v11_screening_logs.py "Test logs" --latex
    python parse_v11_screening_logs.py rsa260_heavy_v11.txt rsa270_heavy_v11.txt --markdown

The parser is intentionally conservative: it only reports counters that are
printed explicitly in the log, and it marks missing fields as n/a.
"""
from __future__ import annotations

import argparse
import os
import re
import statistics as stats
from pathlib import Path
from typing import Dict, Iterable, List, Optional, Tuple

LOG_NAMES = {
    "rsa110": "RSA-110",
    "rsa260": "RSA-260",
    "rsa270": "RSA-270",
    "rsa896": "RSA-896",
    "roca1024": "ROCA-style 1024",
}

RE = {
    "start": re.compile(r"^Start time:\s*(.+)$"),
    "end": re.compile(r"^End time:\s*(.+)$"),
    "elapsed": re.compile(r"^Elapsed time:\s*(.+)$"),
    "status": re.compile(r"^Status:\s*(.+)$"),
    "digits": re.compile(r"^Input n digits:\s*(\d+)"),
    "bits": re.compile(r"^Input n bit length:\s*(\d+)"),
    "rR": re.compile(r"^r_min=(\d+),\s*R=(\d+),\s*protected original x=2R=(\d+),\s*default x_max=4R=(\d+)"),
    "pairs": re.compile(r"^Selected pairs:\s*(\d+);\s*x span=(\d+)\.\.(\d+);\s*u count=(\d+);\s*u range=(\d+)\.\.(\d+)"),
    "sq": re.compile(r"^Square multiplier scan:\s*(.+)$"),
    "range": re.compile(r"^Range mode:\s*(.+)$"),
    "factor": re.compile(r"^Factor extraction:\s*(.+)$"),
    "parallel": re.compile(r"^Parallel:\s*(.+)$"),
    "result_head": re.compile(r"^x=(\d+),\s*u=(\d+),\s*lambda=u\^2=(\d+)"),
    "candidates": re.compile(r"^candidates=(\d+),\s*exact=(\d+),\s*factors=(\[.*\])"),
    "best": re.compile(r"^best delta=([-+0-9.]+),\s*rho=([-+0-9.]+)"),
    "processed": re.compile(r"^Processed pairs:\s*(\d+)"),
    "total_candidates": re.compile(r"^Total candidates tested:\s*(\d+)"),
    "exact_found": re.compile(r"^Exact candidates found:\s*(\d+)"),
    "no_factor": re.compile(r"^No non-trivial factor found"),
    "factor_block": re.compile(r"^Non-trivial factors found:"),
}


def label_from_name(path: Path) -> str:
    name = path.name.lower()
    for key, label in LOG_NAMES.items():
        if key in name:
            return label
    return path.stem


def iter_logs(inputs: List[str]) -> List[Path]:
    paths: List[Path] = []
    for item in inputs:
        p = Path(item)
        if p.is_dir():
            paths.extend(sorted(p.glob("*.txt")))
        elif p.is_file():
            paths.append(p)
    return paths


def parse_log(path: Path) -> Dict[str, object]:
    out: Dict[str, object] = {"file": path.name, "modulus": label_from_name(path), "bytes": path.stat().st_size}
    deltas: List[float] = []
    per_pair_candidates: List[int] = []
    factors_seen = False
    current_pair: Optional[Tuple[int, int]] = None

    with path.open("r", encoding="utf-8", errors="replace") as fh:
        for raw in fh:
            line = raw.strip()
            if not line:
                continue
            for key in ("start", "end", "elapsed", "status", "sq", "range", "factor", "parallel"):
                m = RE[key].match(line)
                if m:
                    out[key] = m.group(1)
                    break
            else:
                if (m := RE["digits"].match(line)):
                    out["digits"] = int(m.group(1))
                elif (m := RE["bits"].match(line)):
                    out["bits"] = int(m.group(1))
                elif (m := RE["rR"].match(line)):
                    out.update({"r_min": int(m.group(1)), "R": int(m.group(2)), "x_2R": int(m.group(3)), "x_4R": int(m.group(4))})
                elif (m := RE["pairs"].match(line)):
                    out.update({
                        "selected_pairs": int(m.group(1)), "x_min": int(m.group(2)), "x_max": int(m.group(3)),
                        "u_count": int(m.group(4)), "u_min": int(m.group(5)), "u_max": int(m.group(6)),
                    })
                elif (m := RE["result_head"].match(line)):
                    current_pair = (int(m.group(1)), int(m.group(2)))
                elif (m := RE["candidates"].match(line)):
                    per_pair_candidates.append(int(m.group(1)))
                    if m.group(3).strip() != "[]":
                        factors_seen = True
                elif (m := RE["best"].match(line)):
                    try:
                        deltas.append(float(m.group(1)))
                    except ValueError:
                        pass
                elif (m := RE["processed"].match(line)):
                    out["processed_pairs"] = int(m.group(1))
                elif (m := RE["total_candidates"].match(line)):
                    out["total_candidates"] = int(m.group(1))
                elif (m := RE["exact_found"].match(line)):
                    out["exact_candidates"] = int(m.group(1))
                elif RE["factor_block"].match(line):
                    factors_seen = True
                elif RE["no_factor"].match(line):
                    out["factors_found"] = 0

    out["factors_found"] = int(bool(factors_seen)) if "factors_found" not in out else out["factors_found"]
    if per_pair_candidates:
        out["candidate_rows"] = len(per_pair_candidates)
        out["cand_mean"] = sum(per_pair_candidates) / len(per_pair_candidates)
        out["cand_median"] = stats.median(per_pair_candidates)
        out["cand_max"] = max(per_pair_candidates)
    if deltas:
        out["delta_n"] = len(deltas)
        out["delta_mean"] = sum(deltas) / len(deltas)
        out["delta_median"] = stats.median(deltas)
        out["delta_min"] = min(deltas)
        out["delta_max"] = max(deltas)
        out["delta_neg"] = sum(1 for d in deltas if d < 0)
        out["delta_zero"] = sum(1 for d in deltas if d == 0)
        out["delta_pos"] = sum(1 for d in deltas if d > 0)
    return out


def fmt(v: object, ndigits: int = 1) -> str:
    if v is None:
        return "n/a"
    if isinstance(v, float):
        return f"{v:.{ndigits}f}"
    return str(v)


def latex_rows(records: List[Dict[str, object]]) -> None:
    print("% Parameters")
    for r in records:
        print(f"{r['modulus']} & {fmt(r.get('bits'),0)} & {fmt(r.get('r_min'),0)} & {fmt(r.get('R'),0)} & {fmt(r.get('x_min'),0)}--{fmt(r.get('x_max'),0)} & {fmt(r.get('u_count'),0)} \\")
    print("\n% Outcomes")
    for r in records:
        total = r.get("total_candidates", r.get("candidate_rows"))
        print(f"{r['modulus']} & {fmt(r.get('processed_pairs'),0)} & {fmt(total,0)} & {fmt(r.get('cand_mean'))} & {fmt(r.get('cand_median'))} & {fmt(r.get('cand_max'),0)} & {fmt(r.get('exact_candidates'),0)} & {fmt(r.get('factors_found'),0)} \\")
    print("\n% Delta distribution")
    for r in records:
        print(f"{r['modulus']} & {fmt(r.get('delta_n'),0)} & {fmt(r.get('delta_mean'))} & {fmt(r.get('delta_median'))} & {fmt(r.get('delta_min'))} & {fmt(r.get('delta_max'))} & {fmt(r.get('delta_neg'),0)} & {fmt(r.get('delta_zero'),0)} & {fmt(r.get('delta_pos'),0)} \\")
    print("\n% Runtime")
    for r in records:
        print(f"{r['modulus']} & {fmt(r.get('start'))} & {fmt(r.get('end'))} & {fmt(r.get('elapsed'))} & {fmt(r.get('status'))} \\")


def markdown_table(records: List[Dict[str, object]]) -> None:
    headers = ["modulus", "bits", "r_min", "R", "x_min", "x_max", "u_count", "processed_pairs", "total_candidates", "exact_candidates", "factors_found", "elapsed", "status"]
    print("| " + " | ".join(headers) + " |")
    print("|" + "|".join(["---"] * len(headers)) + "|")
    for r in records:
        print("| " + " | ".join(fmt(r.get(h)) for h in headers) + " |")


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("paths", nargs="+", help="Log files or directories containing *.txt logs")
    group = ap.add_mutually_exclusive_group()
    group.add_argument("--latex", action="store_true", help="Emit LaTeX table rows")
    group.add_argument("--markdown", action="store_true", help="Emit a compact Markdown table")
    args = ap.parse_args()

    logs = iter_logs(args.paths)
    if not logs:
        raise SystemExit("No log files found")
    records = [parse_log(p) for p in logs]
    records.sort(key=lambda r: str(r["modulus"]))
    if args.latex:
        latex_rows(records)
    else:
        markdown_table(records)


if __name__ == "__main__":
    main()
