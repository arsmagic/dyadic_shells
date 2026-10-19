#!/usr/bin/env python3
"""Build multi-base cross-gcd graph diagnostics in public or validation mode."""
from __future__ import annotations
import argparse
import math
from itertools import combinations
from pathlib import Path
from typing import Dict, List, Optional

from base_shell_lib import e_representatives, exact_window_representatives_for_class, public_global_indicator, theta_height_range, read_csv, write_csv


def build_vertices_public(n: int, n_id: str, bases: List[int], theta0: float, theta1: float, max_vertices: int) -> List[Dict[str, object]]:
    vertices: List[Dict[str, object]] = []
    for b in bases:
        if math.gcd(b, n) != 1:
            continue
        for r in theta_height_range(n, b, theta0, theta1):
            a = pow(b, r)
            x = pow(b, r, n)
            candidates = []
            if x < a:
                candidates.append((x, "global_plus"))
            if x > n - a:
                candidates.append((n - x, "global_minus"))
            for s, label in candidates:
                vertices.append({"vertex_id": f"{n_id}_v{len(vertices)}", "N_id": n_id, "N": str(n), "base": b, "r": r, "A": str(a), "s": str(s), "class_label": label})
                if len(vertices) >= max_vertices:
                    return vertices
    return vertices


def build_vertices_validation(n: int, p: int, q: int, n_id: str, bases: List[int], theta0: float, theta1: float, max_vertices: int) -> List[Dict[str, object]]:
    vertices: List[Dict[str, object]] = []
    reps = e_representatives(p, q)
    for b in bases:
        if math.gcd(b, n) != 1:
            continue
        for r in theta_height_range(n, b, theta0, theta1):
            a = pow(b, r)
            for rep in reps:
                for s in exact_window_representatives_for_class(n, a, int(rep["e"]), max_emit=1):
                    vertices.append({"vertex_id": f"{n_id}_v{len(vertices)}", "N_id": n_id, "N": str(n), "base": b, "r": r, "A": str(a), "s": str(s), "class_label": rep["label"]})
                    if len(vertices) >= max_vertices:
                        return vertices
    return vertices


def build_edges(n: int, vertices: List[Dict[str, object]]) -> List[Dict[str, object]]:
    edges: List[Dict[str, object]] = []
    for vi, vj in combinations(vertices, 2):
        bi = int(vi["base"]); bj = int(vj["base"])
        ri = int(vi["r"]); rj = int(vj["r"])
        si = int(vi["s"]); sj = int(vj["s"])
        for sigma in (1, -1):
            delta = si * pow(bj, rj) - sigma * sj * pow(bi, ri)
            g = math.gcd(delta, n)
            edges.append({
                "source": vi["vertex_id"], "target": vj["vertex_id"], "sigma": sigma,
                "gcd": str(g), "is_nontrivial": 1 < g < n,
                "source_class": vi.get("class_label", ""), "target_class": vj.get("class_label", ""),
            })
    return edges


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--input", required=True, help="CSV with N and optionally p,q")
    ap.add_argument("--mode", choices=["public", "validation"], default="public")
    ap.add_argument("--bases", nargs="+", type=int, default=[2, 3, 5, 7, 11])
    ap.add_argument("--theta0", type=float, default=0.15)
    ap.add_argument("--theta1", type=float, default=0.50)
    ap.add_argument("--max-vertices-per-N", type=int, default=200)
    ap.add_argument("--out-prefix", type=str, default="results/multibase_graph")
    args = ap.parse_args()

    all_vertices: List[Dict[str, object]] = []
    all_edges: List[Dict[str, object]] = []
    for row in read_csv(args.input):
        n = int(row["N"]); n_id = row.get("N_id", "N")
        if args.mode == "validation" and row.get("p") and row.get("q"):
            vertices = build_vertices_validation(n, int(row["p"]), int(row["q"]), n_id, args.bases, args.theta0, args.theta1, args.max_vertices_per_N)
        else:
            vertices = build_vertices_public(n, n_id, args.bases, args.theta0, args.theta1, args.max_vertices_per_N)
        edges = build_edges(n, vertices)
        all_vertices.extend(vertices)
        all_edges.extend(edges)
    write_csv(f"{args.out_prefix}_vertices.csv", all_vertices)
    write_csv(f"{args.out_prefix}_edges.csv", all_edges)
    print(f"Wrote vertices={len(all_vertices)}, edges={len(all_edges)}")

if __name__ == "__main__":
    main()
