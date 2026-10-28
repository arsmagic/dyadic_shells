# Dyadic Shell v0.4 Reproducibility Package

This package generates the empirical material proposed for version 0.4 of the article draft **Center-Compressible and Small-Alpha Semiprimes**.

It focuses on three reviewer-facing goals:

1. **Public modular diagnostics** for distinguishing random balanced semiprimes from sparse-center positive controls.
2. **Modular QR sieve benchmarks** showing how many expensive integer square tests are avoided.
3. **A 1024-bit sparse-center certificate** demonstrating that the construction is not tied to toy bit lengths.

The scripts are deterministic under fixed seeds and write CSV, JSON, and LaTeX outputs.

## Requirements

Python 3.10+ is recommended.

```bash
python -m pip install -r requirements.txt
```

The scripts use `sympy` for primality testing and prime generation.

## Quick smoke test

Run this first to confirm that the package works on your machine:

```bash
python scripts/run_v04_benchmarks.py --quick --out-dir .
```

This creates small 64-bit smoke-test outputs in:

- `results/diagnostics_64.csv`
- `results/sieve_64.csv`
- `tables/diagnostics_table.tex`
- `tables/sieve_table.tex`

## Recommended article-scale run

For a reasonable v0.4 empirical table:

```bash
python scripts/run_v04_benchmarks.py \
  --samples 1000 \
  --bit-sizes 128,256 \
  --window-bits 20 \
  --weight 3 \
  --moduli-count 24 \
  --factor-base-size 12 \
  --seed 20260701 \
  --out-dir .
```

This runs:

- 1000 random balanced and 1000 sparse-center samples for each bit size;
- modular diagnostic scores with 24 odd prime moduli;
- QR-sieve benchmarks with a factor base of 12 odd primes;
- one 1024-bit sparse-center certificate.

If you only want the CSV tables and want to skip the 1024-bit certificate:

```bash
python scripts/run_v04_benchmarks.py \
  --samples 1000 \
  --bit-sizes 128,256 \
  --window-bits 20 \
  --weight 3 \
  --moduli-count 24 \
  --factor-base-size 12 \
  --seed 20260701 \
  --out-dir . \
  --skip-1024
```

## Individual scripts

### 1. Generate semiprime certificates

```bash
python scripts/generate_semiprimes.py \
  --family sparse \
  --bit-size 128 \
  --window-bits 20 \
  --weight 3 \
  --seed 20260701 \
  --out certificates/example_128.json
```

Random balanced baseline:

```bash
python scripts/generate_semiprimes.py \
  --family random \
  --bit-size 128 \
  --seed 20260701 \
  --out certificates/random_128.json
```

### 2. Public modular diagnostics

```bash
python scripts/diagnostic_scores.py \
  --bit-size 128 \
  --samples 1000 \
  --window-bits 20 \
  --weight 3 \
  --moduli-count 24 \
  --seed 20260701 \
  --out results/diagnostics_128.csv
```

Main output columns:

- `family`: `random_balanced` or `sparse_center`.
- `center_set_size`: size of the candidate center set.
- `tmax`: maximum per-candidate diagnostic score.
- `full_hits`: number of candidate centers scoring full marks across all moduli.
- `has_full_hit`: empirical false-positive flag for random samples; true-positive flag proxy for structured samples.
- `true_score`: score of the planted center for structured samples.
- `familywise_false_positive_bound`: union-bound estimate under the random-residue model.

### 3. Modular QR sieve benchmark

```bash
python scripts/sieve_benchmark.py \
  --bit-size 128 \
  --samples 100 \
  --window-bits 20 \
  --weight 3 \
  --factor-base-size 12 \
  --seed 20260701 \
  --out results/sieve_128.csv
```

Main output columns:

- `theoretical_survivors`: expected number of false survivors under the random-residue model.
- `empirical_survivors`: actual number of centers surviving QR filters.
- `true_center_survived`: should be `True` for all structured samples.
- `estimated_exact_test_speedup`: candidate set size divided by survivor count.

### 4. LaTeX tables

```bash
python scripts/make_latex_tables.py --results-dir results --tables-dir tables
```

This generates:

- `tables/diagnostics_table.tex`
- `tables/sieve_table.tex`

These files can be inserted into the article with:

```latex
\input{tables/diagnostics_table.tex}
\input{tables/sieve_table.tex}
```

### 5. 1024-bit certificate

```bash
python scripts/generate_1024_certificate.py \
  --bit-size 1024 \
  --window-bits 128 \
  --weight 4 \
  --seed 20260701 \
  --out certificates/example_1024.json \
  --tex tables/example_1024_certificate.tex
```

The JSON file contains full decimal values for `p`, `q`, `n`, `A`, `B`, and `z`, along with primality flags and the identity check `A^2-n=B^2`.

The LaTeX snippet can be inserted into an appendix with:

```latex
\input{tables/example_1024_certificate.tex}
```

## Suggested v0.4 article insertion points

1. Replace the current public modular diagnostics section with the per-candidate score and maximum-score statistic.
2. Insert `tables/diagnostics_table.tex` after the proposition on family-wise false-positive bounds.
3. Insert `tables/sieve_table.tex` after the QR-sieve survival-rate proposition.
4. Insert `tables/example_1024_certificate.tex` in Appendix A.
5. Mention the exact command line and seed in a reproducibility paragraph.

Suggested reproducibility paragraph:

```latex
All empirical tables were generated with the scripts in the reproducibility archive using Python 3.10 and SymPy. Unless otherwise stated, the seed was fixed to 20260701. The diagnostic tables are reproduced by running \texttt{python scripts/run\_v04\_benchmarks.py --samples 1000 --bit-sizes 128,256 --window-bits 20 --weight 3 --moduli-count 24 --factor-base-size 12 --seed 20260701 --out-dir .}.
```

## Notes on interpretation

- The experiments are **not** claims of general RSA factorization.
- The random baseline models balanced random semiprimes.
- Sparse-center semiprimes are positive controls for center-compressible weak-key generation.
- The QR sieve is a pre-filter; it preserves true centers because true shell values are integer squares and therefore quadratic residues modulo every odd modulus.
- The public diagnostic is a statistical weak-generator detector, not a guaranteed factorization method when the candidate set is large.
