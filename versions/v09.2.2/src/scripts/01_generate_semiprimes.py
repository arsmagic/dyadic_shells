#!/usr/bin/env python3
"""
Generate control and synthetic residue-biased semiprime populations.

Examples:
  python scripts/01_generate_semiprimes.py --bits 128 --samples 200 --out data
  python scripts/01_generate_semiprimes.py --bits 128 192 --samples 500 --modulus 1155 --residue-p 1 --residue-q 1
"""
from __future__ import annotations
import argparse
import random
import time
from pathlib import Path
from typing import Dict, List

from base_shell_lib import generate_balanced_semiprime, generate_residue_biased_semiprime, write_csv, write_json


def build_rows(bits: int, samples: int, seed: int, modulus: int, residue_p: int, residue_q: int) -> Dict[str, List[Dict[str, object]]]:
    rng = random.Random(seed + bits * 1009)
    random_rows: List[Dict[str, object]] = []
    biased_rows: List[Dict[str, object]] = []

    for j in range(samples):
        t0 = time.time()
        n, p, q = generate_balanced_semiprime(bits, rng)
        random_rows.append({
            "N_id": f"random_{bits}_{j:05d}",
            "N": str(n), "p": str(p), "q": str(q),
            "bit_length_requested": bits, "bit_length_actual": n.bit_length(),
            "generator_type": "random_balanced",
            "modulus_M": "", "residue_p": "", "residue_q": "",
            "seed": seed, "seconds": round(time.time() - t0, 6),
        })

        t0 = time.time()
        n, p, q = generate_residue_biased_semiprime(bits, modulus, residue_p, residue_q, rng)
        biased_rows.append({
            "N_id": f"biased_{bits}_{j:05d}",
            "N": str(n), "p": str(p), "q": str(q),
            "bit_length_requested": bits, "bit_length_actual": n.bit_length(),
            "generator_type": "synthetic_residue_biased",
            "modulus_M": modulus, "residue_p": residue_p, "residue_q": residue_q,
            "seed": seed, "seconds": round(time.time() - t0, 6),
        })
    return {"random": random_rows, "biased": biased_rows}


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--bits", nargs="+", type=int, default=[64, 96, 128])
    ap.add_argument("--samples", type=int, default=200)
    ap.add_argument("--seed", type=int, default=20260628)
    ap.add_argument("--modulus", type=int, default=1155, help="Auxiliary modulus M for synthetic residue bias")
    ap.add_argument("--residue-p", type=int, default=1)
    ap.add_argument("--residue-q", type=int, default=1)
    ap.add_argument("--out", type=str, default="data")
    args = ap.parse_args()

    out = Path(args.out)
    out.mkdir(parents=True, exist_ok=True)
    manifest = {
        "purpose": "random and synthetic residue-biased semiprime generation",
        "seed": args.seed,
        "samples_per_population": args.samples,
        "bits": args.bits,
        "synthetic_bias": {"modulus": args.modulus, "residue_p": args.residue_p, "residue_q": args.residue_q},
    }
    write_json(out / "generation_manifest.json", manifest)

    for bits in args.bits:
        rows = build_rows(bits, args.samples, args.seed, args.modulus, args.residue_p, args.residue_q)
        fieldnames = ["N_id", "N", "p", "q", "bit_length_requested", "bit_length_actual", "generator_type", "modulus_M", "residue_p", "residue_q", "seed", "seconds"]
        write_csv(out / f"random_{bits}.csv", rows["random"], fieldnames)
        write_csv(out / f"biased_{bits}.csv", rows["biased"], fieldnames)
        print(f"bits={bits}: wrote {len(rows['random'])} random and {len(rows['biased'])} biased semiprimes")

if __name__ == "__main__":
    main()
