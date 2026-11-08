# Dyadic Shells, Version 11.7.23: Exact two-adic counts for Fermat-type quadratic sieves and the hyperbolic sieve

Author: Arsen A. Khachatryan (SibarS Labs, SibarS Group of Companies; ORCID 0009-0006-7629-3833)
Version: 11.7.23, 8 November 2026. DOI: 10.5281/zenodo.24051028 (series concept DOI 10.5281/zenodo.20306132).
Preprint, not peer-reviewed.

## Content

For odd N, C_m(N) is the number of residues A mod 2^m with A^2 - N a square mod 2^m. The paper proves:

- C_m(N) depends only on N mod 8; C_m = 2^(m-2) for N = 3 (mod 4); 2^(m-3) for N = 5 (mod 8), m >= 5;
  4 s(m-4) for N = 1 (mod 8), m >= 4, where s(n) is the number of squares mod 2^n;
- C_m(N)/2^m > 1/24 for all odd N and all m, and 1/24 is optimal (this proves the value stated as a
  conjecture in Version 11.5.17, DOI 10.5281/zenodo.23432486);
- |L_{N,2^e,k}| = C_e(kN)/2 for Hittmeir's hyperbolic sieve sets, odd N, k, e >= 1, which gives proofs of the
  values for powers of two recorded computationally in Hittmeir (J. Number Theory 249, 2023), with the
  recursion exponent e mod 2 (the arXiv v1 text prints (e+1) mod 2; the journal version was not inspected);
- a sieve prime dividing the multiplier exactly once removes a proportion 1/l at modulus l^2.

Version 11.5.17 is not modified by this version. No new general-purpose factoring algorithm is claimed.

## Files

- `Khachatryan_A_A_0009-0006-7629-3833_Dyadic_shells_v11_7_23.pdf` — the preprint.
- `Khachatryan_A_A_0009-0006-7629-3833_Dyadic_shells_v11_7_23_source_package.zip` — `verify_v11723.py` (pure Python 3, finite-range tests,
  exit status 0 iff all checks pass) and its output `test_log_v11723.txt`; the Lean file `TwoAdicExact.lean`.

## Reproducibility

    python3 verify_v11723.py      # about 10 s; prints all test groups and exits 0

The script is also pinned in the repository:
https://github.com/arsmagic/dyadic_shells/blob/c7a78b95f913a04f000ce7cd1593c6b652752049/research/twoadic-exact/verify_v11723.py

## Formal verification

Lean 4 v4.24.0 with Mathlib v4.24.0, repository https://github.com/arsmagic/dyadic_shells, file
`formal/DyadicShells/TwoAdicExact.lean` (commit 96b857a): `DyadicShells.passCard_unit_sq_mul` and
`DyadicShells.passCard_eq_of_modEq_eight` (reduction to N mod 8). The closed forms, the 1/24 bound and the
hyperbolic-sieve identity are proved in the paper but not formally verified.

## Licence

CC BY-NC 4.0.
