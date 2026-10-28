# Dyadic Shells — Lean 4 formalization

**Research author:** Arsen A. Khachatryan (SibarS Labs; ORCID 0009-0006-7629-3833).

**Status:** **Target 1 (Proposition 3.1: soundness and factor recovery) is
Lean-proved.** Its source-to-code correspondence has been checked against
the published v11.0.3, page 3, including the converse for both signs.
An external human referee review has **not** been performed.
**Targets 2 and 3 remain open.**

- [v11.0.3](https://doi.org/10.5281/zenodo.23135512), Proposition 3.1
  (published source for Target 1), Propositions 4.1 and 4.2 (next targets).
- [v11.5.17](https://doi.org/10.5281/zenodo.23432486) (later extended framework).
- [Detailed theorem mapping](./THEOREM_MAPPING.md).
- [Verification ledger](./VERIFICATION_STATUS.md).
- [Lean CI](https://github.com/arsmagic/dyadic_shells/actions/workflows/lean-formal.yml).

## What Target 1 proves

`DyadicShells/Soundness.lean` proves the weighted square identity,
conditional recovery of `p,q` by exact gcd, and the published
prime-and-multiplier-bound corollary (with derived coprimality and
`t` constructed from `A`). The certificate converse checks both signs
and requires `1 < gcd(A ± t,n) < |n|` to claim a proper divisor.
A regression illustrates why an arbitrary `A²-k*n=t²` does not
automatically reveal factors of `n`.

The Lean corollary is more general than the publication in some hypotheses;
the published anchored and coprime-odd cases specialize it.
This verifies **the mathematics encoded in these theorems**, not
algorithmic complexity, scientific novelty, or practical RSA weakness.

## Reproduction

Install [elan](https://github.com/leanprover/elan) and run from
`formal/`:

```sh
lake update
lake exe cache get
lake build
lake env lean DyadicShells/AxiomAudit.lean
```

The CI workflow runs on changes to `formal/**` in pull requests and
on pushes to `main`, and checks for proof holes.
Lean and Mathlib are pinned to v4.24.0.

## Next targets

1. **Target 2:** exact quadratic-residue sieve fraction
   (Proposition 4.1), currently only elementary soundness lemmas.
2. **Target 3:** uniform two-adic density
   (Proposition 4.2), currently only existence of a square witness.

No new Zenodo DOI has been assigned for these formalization files.
AI assistance is disclosed; independent human peer review remains recommended.
