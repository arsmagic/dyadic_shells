# Dyadic Shells: Lean 4 formalization (work in progress)

**Mathematical author:** Arsen A. Khachatryan (ORCID 0009-0006-7629-3833)  
**Affiliation:** SibarS Labs  
**Status:** Target 1 (soundness & factor recovery) is **Lean-proved in CI**
(Lean 4.24.0 / Mathlib v4.24.0, green run #14 = `40660521229`, no proof holes;
axioms audited in CI — only `propext`, `Classical.choice`, `Quot.sound`). Targets 2 & 3 are **not yet proved**. Full-proposition
equivalence-to-prose review by the author/reviewer is still pending.

Source publications:
- Anchored Sparse-Offset Screening of Semiprimes, v11.5.17, https://doi.org/10.5281/zenodo.23432486
- v11.0.3, https://doi.org/10.5281/zenodo.23135512

The three original targets are:
1. Weighted center identity, factor soundness and gcd recovery.
2. Exact quadratic-residue passing fraction over odd prime fields.
3. Uniform lower bound for two-adic passing density.

Target 1 is now proved (weighted identity, arbitrary-certificate soundness,
exact gcd factor recovery, the published-hypotheses corollary with derived
cross-coprimality and proper-factor nontriviality, and the weighted-certificate
acceptance criterion with a regression showing an exact weighted square need not
factor `n`). Targets 2 and 3 still have only the square-pair/soundness lemmas and
a witness-existence lemma respectively; they **do not yet constitute full formal
proofs**. See `THEOREM_MAPPING.md` and `VERIFICATION_STATUS.md` for exact gaps
and the axiom audit.

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
