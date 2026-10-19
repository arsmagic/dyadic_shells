# Anchored Sparse-Offset Screening of Semiprimes

**Preprint Version:** 11.0.3
**Author:** Arsen A. Khachatryan, SibarS Labs, SibarS Group of Companies
**ORCID:** 0009-0006-7629-3833
**Status:** preprint, not peer reviewed
**Series:** continues the dyadic-shell preprint series (previous version 10.5.1, DOI 10.5281/zenodo.22055615; all versions: 10.5281/zenodo.20306132)

## Overview

The preprint studies structured semiprimes n = pq whose weighted arithmetic centre (ap + bq)/2 lies in a public
*anchored sparse set* 2^r + Z, where Z consists of all integers with h binary ones inside a w-bit window.
Membership is certified exactly by the identity A^2 - abn = ((ap - bq)/2)^2.

Main contents:

* an exact pass fraction 1/2 + chi_l(N)/(2l) for the quadratic-residue sieve, and the resulting prime-selection rule;
* a proof that two-adic filtering saturates (its gain is bounded by a constant independent of the number of bits);
* a lazily generated representation of offset sets of arbitrary span, with benchmarks on planted 1024- and 2048-bit moduli
  (up to 3.3 x 10^8 offsets);
* a pre-specified audit of 2,355 public RSA moduli (negative result) with 88 planted end-to-end controls.

The work is **not** a general attack on RSA and gives no evidence that any deployed key population is
anchor-compressible. All positive controls are planted by the author.

## Files

| File | Content |
| --- | --- |
| `..._v11_0_3.pdf` | the preprint |
| `..._v11_0_3_source_package.zip` | LaTeX source, scripts, aggregate audit results, requirements |

Inside the archive (`src/`):

| File | Purpose |
| --- | --- |
| `dyadic_kz_scan.py` | the (k, z)-scan with adaptive sieve; `--selftest` runs the built-in checks |
| `dyadic_kz_bench.py` | benchmarks: `nullmodel`, `scaling`, `primes`, `bigw`, `twoadic` (`--quick` for a short run) |
| `corpus_collect.py` | collects public `ssh-rsa` keys, stores only salted-hash identifiers, exponents and moduli |
| `corpus_audit.py` | the pre-specified audit battery, batch GCD, planted controls |
| `corpus_audit_results.json` | aggregate outcome of the audit (no keys, no account names) |
| `article_source.tex` | LaTeX source of the preprint |
| `requirements.txt` | Python dependencies |

## Reproducing

```bash
pip install -r requirements.txt
python3 dyadic_kz_scan.py --selftest
python3 dyadic_kz_bench.py twoadic
python3 dyadic_kz_bench.py nullmodel --quick
# corpus audit (your own key file in the format produced by corpus_collect.py):
CRAWLER_CONTACT="you@example.org" KEY_SALT="long-random-string" \
    python3 corpus_collect.py --seeds <account1>,<account2> --pages 40 --max-users 5000 --out keys.json
python3 corpus_audit.py keys.json audit.json --controls 64 24
```

Numerical results are statistical; timings were measured on one CPU core of a virtual machine (CPU model not recorded)
and depend on hardware. The key corpus used in the preprint is not redistributed.

## Scope and limitations

Convenience sample of one platform and one key type; controls planted at 1024 and 2048 bits only; no experimental
comparison with lattice-based methods; independence of sieve moduli is a heuristic. See Sections 8 and 9 of the preprint.

## Suggested citation

```text
Khachatryan, A. A. Anchored Sparse-Offset Screening of Semiprimes: An Exact Sieve Null Model, Two-Adic Saturation,
and Positive-Control Benchmarks up to 2048 Bits. Version 11.0.3. Zenodo, 2026. DOI: (assigned by Zenodo on publication).
```

## License

Creative Commons Attribution Non Commercial 4.0 International (CC BY-NC 4.0), as for the preceding versions of the series.
