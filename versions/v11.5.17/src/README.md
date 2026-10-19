# Anchored Sparse-Offset Screening of Semiprimes

**Preprint Version:** 11.5.17
**Author:** Arsen A. Khachatryan, SibarS Labs, SibarS Group of Companies
**ORCID:** 0009-0006-7629-3833
**Status:** preprint, not peer reviewed
**Series:** continues Version 11.0.3 (DOI 10.5281/zenodo.23135512); all versions: 10.5281/zenodo.20306132
**Licence:** Creative Commons Attribution Non Commercial 4.0 International (CC BY-NC 4.0)

## Overview

The preprint studies structured semiprimes n = pq whose weighted arithmetic centre (ap + bq)/2 lies in a public
*anchored sparse set* 2^r + Z, where Z consists of all integers with h binary ones inside a w-bit window.
Membership is certified exactly by the identity A^2 - abn = ((ap - bq)/2)^2, so the screen is sound by construction.

Version 11.5.17 extends Version 11.0.3 with:

* an **odd-prime depth saturation** result: for a prime l with chi_l(N) = +1, lifting to the modulus l^k drives the
  pass fraction down to mu_l = (l-3)/(2l) + 1/(l(l+1)) (verified numerically to four digits), giving a sharper
  adaptive prime-selection rule that cuts exact tests by 4-30x;
* an **implicit sparse scanner** that never materialises candidate rows (about 8x faster at 1.7e8-3.3e8 offsets);
* a **fractional-part meet-in-the-middle (FP-MITM)** for sparse centres whose window exceeds the Coppersmith range,
  with a coverage model and an unbalanced-split planner (recovers w = 300 at 1024 bits, w = 600 at 2048 bits);
* a **measured lattice crossover** (Coppersmith/Howgrave-Graham via fpylll): reliable recovery up to w ~ 230 bits,
  failing from w ~ 240, so the FP-MITM windows lie genuinely beyond the lattice;
* a **cost-model auditor** that selects a method per hypothesis and schedules by Smith's rule (expected-time optimal),
  with a validated cost model and an end-to-end demonstration;
* two further **pre-specified corpus audits** of the same 2,355 public RSA moduli: multi-anchor bases (c*2^m and b^r)
  and patterned prime factors. Both negative; all planted controls recovered.

The work is **not** a general attack on RSA and gives no evidence that any deployed key population is
anchor-compressible. All positive controls are planted by the author. The meet-in-the-middle core is classical
(Coppersmith's low-Hamming-weight discrete-logarithm algorithm, as presented by Stinson 2002) and is cited as such;
see `src/PRIOR_ART.md` and `src/PRIOR_ART_FINDINGS.md`.

## Files

| File | Content |
| --- | --- |
| `..._v11_5_17.pdf` | the preprint (17 pages) |
| `..._v11_5_17_source_package.zip` | Scripts, aggregate audit results, prior-art notes, requirements |

Inside the archive (`src/`):

| File | Purpose |
| --- | --- |
| `dyadic_kz_scan.py` | the (k, z)-scan with adaptive sieve, odd-prime depth and the implicit scanner; `--selftest` runs the checks |
| `dyadic_kz_bench.py` | benchmarks: `nullmodel`, `scaling`, `primes`, `bigw`, `twoadic` (`--quick` for a short run) |
| `corpus_collect.py` | collects public `ssh-rsa` keys, stores only salted-hash identifiers, exponents and moduli |
| `corpus_audit.py` | Battery 1 (anchored centres): pre-specified audit, batch GCD, planted controls |
| `multi_anchor_audit.py` | Battery 2 (multi-anchor bases c*2^m and b^r) |
| `patterned_primes_audit.py` | Battery 3 (patterned prime factors c*2^m+u and 2^k-u) |
| `fpmitm.py` | fractional-part meet-in-the-middle, with the `plan_y` unbalanced-split planner |
| `cop_lattice.py` | Coppersmith/Howgrave-Graham divisor method (fpylll); the measured lattice crossover |
| `auditor.py` | cost-model method selection and Smith's-rule scheduling |
| `demo.py` | end-to-end auditor demonstration (produces `demo_output.txt`) |
| `bench_fpmitm.py`, `bench_fpmitm_2048.py`, `holdout_validation.py` | FP-MITM and cost-model validation drivers |
| `corpus_audit_results.json`, `ma_all.json`, `pp_all.json` | aggregate audit outcomes (no keys, no account names) |
| `demo_output.txt` | auditor demonstration log |
| `PRIOR_ART.md`, `PRIOR_ART_FINDINGS.md`, `READING_LIST.md` | prior-art check and the required reading list |
| `requirements.txt` | Python dependencies |

## Reproducing

```bash
pip install -r requirements.txt            # numpy, sympy, gmpy2 (fpylll, cysignals only for the lattice baseline)
python3 dyadic_kz_scan.py --selftest       # scan correctness
python3 dyadic_kz_bench.py twoadic         # two-adic saturation table
python3 dyadic_kz_bench.py nullmodel --quick
python3 cop_lattice.py                      # lattice crossover (needs fpylll)
python3 demo.py 150                         # auditor demo, 150 s budget per modulus
# corpus audits (your own key file in the format produced by corpus_collect.py):
CRAWLER_CONTACT="you@example.org" KEY_SALT="long-random-string" \
    python3 corpus_collect.py --seeds <account1>,<account2> --pages 40 --max-users 5000 --out keys.json
python3 corpus_audit.py keys.json audit1.json --controls 64 24
python3 multi_anchor_audit.py keys.json audit2.json --controls 90
python3 patterned_primes_audit.py keys.json audit3.json --controls 60 --ubits 14
```

The `bench_*` and `holdout_validation.py` drivers contain hard-coded working-directory paths; adjust their
`sys.path.insert` lines before running. Numerical results are statistical; timings were measured on one CPU core
of a virtual machine (CPU model not recorded) and depend on hardware. The key corpus used in the preprint is not
redistributed.

## Scope and limitations

Convenience sample of one platform and one key type; controls planted at 1024 and 2048 bits; FP-MITM coverage is
heuristic (tested for z >= 0 and moderate p/B; the h = 8, w = 300 case was not completed); the lattice-time
extrapolation to sizes other than 1024 bits was not measured; the relation of FP-MITM to the Meng square-root
attacks is left open (full texts not consulted). See Sections 9-12 of the preprint.

## Suggested citation

```text
Khachatryan, A. A. Anchored Sparse-Offset Screening of Semiprimes: Exact Sieve Null Models, Two-Adic and
Odd-Prime Saturation, a Fractional-Part Meet-in-the-Middle Beyond the Lattice Range, and a Cost-Model Auditor.
Version 11.5.17. Zenodo, 2026. DOI: (assigned by Zenodo on publication).
```
