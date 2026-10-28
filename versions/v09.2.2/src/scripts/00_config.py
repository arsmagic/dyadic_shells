#!/usr/bin/env python3
"""Configuration for base-shell academic computational tests."""
from __future__ import annotations
from base_shell_lib import ExperimentConfig, ensure_dirs, write_json
from pathlib import Path

CONFIG = ExperimentConfig(
    seed=20260628,
    bit_lengths=(64, 96, 128, 192, 256),
    bases=(2, 3, 5, 7, 11),
    theta_bands=((0.15, 0.35), (0.25, 0.50)),
    population_size_small=200,
    population_size_main=1000,
    output_dir="results",
    figure_dir="figures",
    data_dir="data",
    logs_dir="logs",
    max_bruteforce_A=1_000_000,
)

if __name__ == "__main__":
    root = Path(__file__).resolve().parents[1]
    ensure_dirs(root)
    write_json(root / "config.json", CONFIG.__dict__)
    print(f"Wrote {root / 'config.json'}")
