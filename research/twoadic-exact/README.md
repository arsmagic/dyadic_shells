# Exact two-adic counts — finite-range test script

`verify_revised.py` tests, over the finite ranges it prints, the identities of the
manuscript draft *Exact two-adic counts for Fermat-type quadratic sieves and the
hyperbolic sieve* (A. A. Khachatryan, draft of 2026-11-08). Pure Python 3, no
dependencies: `python3 verify_revised.py`. A finite test is not a proof; the proofs
are in the manuscript, and the reduction to `N mod 8` is formalised in
`formal/DyadicShells/TwoAdicExact.lean`.

`verify_v11723.py` is the verifier for the unpublished draft of Version 11.7.23 (exits with status 1 on any failed check); `test_log_v11723.txt` is its output.

Review branch only; not part of a release.
