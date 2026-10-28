#!/usr/bin/env python3
"""Build LaTeX summary tables from benchmark CSV files."""

from __future__ import annotations

import argparse
import csv
import math
import statistics as stats
from collections import defaultdict
from pathlib import Path
from typing import Dict, Iterable, List, Tuple


def read_csv(path: Path) -> List[dict]:
    with path.open(newline="", encoding="utf-8") as f:
        return list(csv.DictReader(f))


def mean_float(rows: List[dict], key: str) -> float:
    vals = [float(r[key]) for r in rows if r.get(key) not in (None, "")]
    return stats.mean(vals) if vals else float("nan")


def std_float(rows: List[dict], key: str) -> float:
    vals = [float(r[key]) for r in rows if r.get(key) not in (None, "")]
    return stats.pstdev(vals) if len(vals) > 1 else 0.0


def bool_rate(rows: List[dict], key: str) -> float:
    vals = [r.get(key, "").lower() in ("true", "1", "yes") for r in rows]
    return sum(vals) / len(vals) if vals else float("nan")


def fmt(x: float, digits: int = 3) -> str:
    if math.isnan(x):
        return "--"
    if x == 0:
        return "0"
    if abs(x) < 1e-3 or abs(x) >= 1e5:
        return f"{x:.{digits}e}"
    return f"{x:.{digits}f}"


def diagnostics_table(results_dir: Path, out: Path) -> None:
    files = sorted(results_dir.glob("diagnostics_*.csv"))
    rows: List[dict] = []
    for file in files:
        rows.extend(read_csv(file))
    groups: Dict[Tuple[str, str, str, str, str], List[dict]] = defaultdict(list)
    for r in rows:
        key = (r["bit_size"], r["family"], r["center_set_size"], r["moduli_count"], r["window_bits"])
        groups[key].append(r)

    lines = []
    lines.append(r"\begin{table}[htbp]")
    lines.append(r"\centering")
    lines.append(r"\caption{Public modular diagnostic scores: random baseline vs. sparse-center positives.}")
    lines.append(r"\label{tab:diagnostic-scores}")
    lines.append(r"\begin{tabular}{@{}llrrrrrr@{}}")
    lines.append(r"\toprule")
    lines.append(r"Bits & Family & Samples & $|\mathcal A|$ & $|\mathcal M|$ & Mean $T_{\max}$ & Full-hit rate & True-positive rate \\")
    lines.append(r"\midrule")
    for key, rs in sorted(groups.items(), key=lambda kv: (int(kv[0][0]), kv[0][1])):
        bit_size, family, set_size, mcount, window_bits = key
        full_hit_rate = bool_rate(rs, "has_full_hit")
        true_rows = [x for x in rs if x.get("true_positive") not in ("", None)]
        true_pos_rate = bool_rate(true_rows, "true_positive") if true_rows else float("nan")
        family_label = "random" if family == "random_balanced" else "sparse-center"
        lines.append(
            f"{bit_size} & {family_label} & {len(rs)} & {set_size} & {mcount} & "
            f"{fmt(mean_float(rs, 'tmax'))} $\\pm$ {fmt(std_float(rs, 'tmax'))} & "
            f"{fmt(full_hit_rate)} & {fmt(true_pos_rate)} \\\\"
        )
    lines.append(r"\bottomrule")
    lines.append(r"\end{tabular}")
    lines.append(r"\end{table}")
    out.write_text("\n".join(lines) + "\n", encoding="utf-8")


def sieve_table(results_dir: Path, out: Path) -> None:
    files = sorted(results_dir.glob("sieve_*.csv"))
    rows: List[dict] = []
    for file in files:
        rows.extend(read_csv(file))
    groups: Dict[Tuple[str, str, str, str], List[dict]] = defaultdict(list)
    for r in rows:
        key = (r["bit_size"], r["center_set_size"], r["factor_base_size"], r["window_bits"])
        groups[key].append(r)

    lines = []
    lines.append(r"\begin{table}[htbp]")
    lines.append(r"\centering")
    lines.append(r"\caption{Modular QR sieve benchmark for sparse shifted-shell scans.}")
    lines.append(r"\label{tab:sieve-benchmark}")
    lines.append(r"\begin{tabular}{@{}rrrrrrr@{}}")
    lines.append(r"\toprule")
    lines.append(r"Bits & Samples & $|\mathcal A|$ & $k$ & Theor. survivors & Emp. survivors & Exact-test speedup \\")
    lines.append(r"\midrule")
    for key, rs in sorted(groups.items(), key=lambda kv: int(kv[0][0])):
        bit_size, set_size, k, window_bits = key
        true_survival = bool_rate(rs, "true_center_survived")
        lines.append(
            f"{bit_size} & {len(rs)} & {set_size} & {k} & "
            f"{fmt(mean_float(rs, 'theoretical_survivors'))} & "
            f"{fmt(mean_float(rs, 'empirical_survivors'))} $\\pm$ {fmt(std_float(rs, 'empirical_survivors'))} & "
            f"{fmt(mean_float(rs, 'estimated_exact_test_speedup'))}x \\\\"
        )
    lines.append(r"\bottomrule")
    lines.append(r"\end{tabular}")
    lines.append(r"\end{table}")
    out.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    parser = argparse.ArgumentParser(description="Generate LaTeX tables from CSV benchmark outputs.")
    parser.add_argument("--results-dir", type=Path, default=Path("results"))
    parser.add_argument("--tables-dir", type=Path, default=Path("tables"))
    args = parser.parse_args()
    args.tables_dir.mkdir(parents=True, exist_ok=True)
    diagnostics_table(args.results_dir, args.tables_dir / "diagnostics_table.tex")
    sieve_table(args.results_dir, args.tables_dir / "sieve_table.tex")
    print(f"wrote tables to {args.tables_dir}")


if __name__ == "__main__":
    main()
