# Dyadic Shells: Lean 4 formalization (work in progress)

**Mathematical author:** Arsen A. Khachatryan (ORCID 0009-0006-7629-3833)  
**Affiliation:** SibarS Labs  
**Status:** initial formalization, **NOT YET VERIFIED**.

Source publications:
- Anchored Sparse-Offset Screening of Semiprimes, v11.5.17, https://doi.org/10.5281/zenodo.23432486
- v11.0.3, https://doi.org/10.5281/zenodo.23135512

The three original targets are:
1. Weighted center identity, factor soundness and gcd recovery.
2. Exact quadratic-residue passing fraction over odd prime fields.
3. Uniform lower bound for two-adic passing density.

The current Lean sources provide the **algebraic core** of 1, the square-pair
and soundness lemmas for 2, and existence of a witness for 3.
They **do not yet constitute full formal proofs of all three results**.
See `THEOREM_MAPPING.md` and `VERIFICATION_STATUS.md` for exact gaps.

## Build

Install Lean toolchain using [elan](https://github.com/leanprover/elan).
From the `formal/` directory:

```sh
lake update
lake exe cache get
lake build
grep -R -n -E '\\b(sorry|admit)\\b' DyadicShells || true
```

CI builds using a pinned Lean/mathlib release. A green build confirms only
the **lemmas present in the files**, not the unimplemented full statements.
No experimental scaling, algorithmic complexity or claimed novelty is verified.

## Research ethics and attribution

These files are a formalization attempt prepared using AI assistance at the
user's direction; all mathematical claims and code require independent checking.
No new DOI is assigned and no public scientific claim of full Lean verification
should be made until the exact original statements are implemented and built.
