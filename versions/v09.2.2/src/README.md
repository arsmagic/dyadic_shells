# Base-Shell Diagnostic Framework — Academic Computational Test Suite

This package contains reproducible Python scripts for the empirical and validation protocols proposed for the v9.2.0 development stage of the base-shell diagnostic framework.

The suite is conservative by design. It does **not** claim to factor RSA moduli, detect ROCA keys, or provide a universal weak-key detector. It provides public and validation-mode screening protocols for synthetic and legacy benchmark analysis.

## Quick start

```bash
python -m venv .venv
source .venv/bin/activate  # Windows: .venv\Scripts\activate
pip install -r requirements.txt
python scripts/09_run_all.py --bits 64 96 128 --samples 50
```

For a larger run:

```bash
python scripts/09_run_all.py --bits 128 192 256 --samples 200
```

## Script map

| Script | Role |
|---|---|
| `scripts/00_config.py` | Writes default config file. |
| `scripts/01_generate_semiprimes.py` | Generates random balanced and synthetic residue-biased semiprimes. |
| `scripts/02_exact_window_sanity.py` | Verifies exact finite-window formulas against brute force for small cases. |
| `scripts/03_compute_zglob.py` | Computes public `Cglob`, null baseline, and `Zglob`. |
| `scripts/04_validation_coset_audit.py` | Validation-mode CRT-class distribution audit using known factors. |
| `scripts/05_multibase_graph.py` | Multi-base cross-gcd graph diagnostics. |
| `scripts/06_weyl_profile.py` | Empirical Weyl/exponential-sum profiles. |
| `scripts/07_analyze_statistics.py` | Summary statistics, KS/Mann–Whitney tests, and AUC. |
| `scripts/08_make_tables_figures.py` | Basic article-ready figures. |
| `scripts/run_legacy_benchmarks.py` | Public screening for RSA-110, RSA-260, RSA-270, RSA-896, ROCA-1024 after values are supplied. |
| `scripts/09_run_all.py` | Convenience runner for the full small pipeline. |

## Legacy benchmarks

No RSA/ROCA constants are hard-coded to avoid transcription errors. Copy:

```bash
cp data/legacy_moduli_template.json data/legacy_moduli.json
```

Fill in decimal `N` values and, where available, `p` and `q`. Then run:

```bash
python scripts/run_legacy_benchmarks.py --legacy-json data/legacy_moduli.json --bases 2 3 5 7 11 --theta 0.15 0.35 0.25 0.50
```

The legacy suite should be reported as **continuity and stress tests**, not as statistical validation. Use synthetic populations for statistical inference.

## Recommended experimental sequence

1. Exact finite-window sanity checks (`02_exact_window_sanity.py`).
2. Generate random and synthetic residue-biased populations (`01_generate_semiprimes.py`).
3. Compute `Zglob` (`03_compute_zglob.py`).
4. Analyze random-vs-biased separation (`07_analyze_statistics.py`).
5. Run validation-mode CRT class audit on factored synthetic data (`04_validation_coset_audit.py`).
6. Run Weyl profiles (`06_weyl_profile.py`).
7. Run legacy benchmark continuity checks (`run_legacy_benchmarks.py`).
8. Generate tables/figures (`08_make_tables_figures.py`).

## Interpretation rules

Preferred language for the paper:

- “synthetic residue-bias anomaly screening”
- “public global-window observable”
- “validation-mode CRT-class audit”
- “continuity benchmark”
- “calibrated null baseline”

Avoid:

- “ROCA detector”
- “weak-key detector” without qualification
- “empirical proof of obstruction”
- “practical RSA attack”
- “expected AUC” before running experiments

## Outputs

The standard runner creates:

```text
data/       generated semiprime populations
results/    CSV results and statistical summaries
figures/    PNG figures
logs/       reserved for long-running job logs
manifest.json  file hashes and environment metadata
```

## Notes on validation vs public mode

- Public-mode scripts never require `p` and `q`.
- Validation-mode scripts require known factors and are intended for synthetic controls or known factored benchmarks.
- Mixed CRT-class diagnostics are validation-mode only unless a nontrivial gcd certificate appears publicly.
