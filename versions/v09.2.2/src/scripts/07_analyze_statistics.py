#!/usr/bin/env python3
"""Statistical summaries for Zglob random-vs-synthetic experiments."""
from __future__ import annotations
import argparse
from collections import defaultdict
from pathlib import Path
from typing import Dict, List, Tuple

from base_shell_lib import read_csv, write_csv, summarize_numeric, manual_auc, ks_statistic

try:
    from scipy import stats  # type: ignore
except Exception:  # pragma: no cover
    stats = None


def load_rows(paths: List[str]) -> List[Dict[str, str]]:
    rows: List[Dict[str, str]] = []
    for p in paths:
        rows.extend(read_csv(p))
    return rows


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--inputs", nargs="+", required=True, help="zglob_*.csv files")
    ap.add_argument("--out-summary", default="results/statistical_summary.csv")
    ap.add_argument("--out-pairwise", default="results/pairwise_tests.csv")
    args = ap.parse_args()

    rows = load_rows(args.inputs)
    groups: Dict[Tuple[str, str, str], List[float]] = defaultdict(list)
    # key: (bit_length, theta_band, generator_type)
    for row in rows:
        bit = str(row.get("bit_length_actual", ""))
        theta = f"{row.get('theta0')}-{row.get('theta1')}"
        gen = row.get("generator_type", "unknown")
        try:
            groups[(bit, theta, gen)].append(float(row["Zglob"]))
        except Exception:
            pass

    summary_rows: List[Dict[str, object]] = []
    for (bit, theta, gen), vals in sorted(groups.items()):
        s = summarize_numeric(vals)
        summary_rows.append({"bit_length": bit, "theta_band": theta, "generator_type": gen, **s})

    pair_rows: List[Dict[str, object]] = []
    # Compare random_balanced against synthetic_residue_biased for each bit/theta when present.
    bit_theta_keys = sorted({(k[0], k[1]) for k in groups})
    for bit, theta in bit_theta_keys:
        random_vals = groups.get((bit, theta, "random_balanced"), [])
        biased_vals = groups.get((bit, theta, "synthetic_residue_biased"), [])
        if not random_vals or not biased_vals:
            continue
        y_true = [0] * len(random_vals) + [1] * len(biased_vals)
        scores = random_vals + biased_vals
        auc = manual_auc(y_true, scores)
        ks_d = ks_statistic(random_vals, biased_vals)
        ks_p = None
        mw_p = None
        if stats is not None:
            try:
                ks_p = float(stats.ks_2samp(random_vals, biased_vals).pvalue)
                mw_p = float(stats.mannwhitneyu(random_vals, biased_vals, alternative="two-sided").pvalue)
            except Exception:
                pass
        pair_rows.append({
            "bit_length": bit, "theta_band": theta,
            "n_random": len(random_vals), "n_biased": len(biased_vals),
            "mean_random": summarize_numeric(random_vals)["mean"],
            "mean_biased": summarize_numeric(biased_vals)["mean"],
            "ks_statistic": ks_d, "ks_pvalue": ks_p,
            "mannwhitney_pvalue": mw_p,
            "auc_biased_gt_random": auc,
        })

    write_csv(args.out_summary, summary_rows)
    write_csv(args.out_pairwise, pair_rows)
    print(f"Wrote {args.out_summary} and {args.out_pairwise}")

if __name__ == "__main__":
    main()
