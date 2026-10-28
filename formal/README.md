# Dyadic Shells — Lean 4 formalization

**Research author:** Arsen A. Khachatryan (SibarS Labs; ORCID 0009-0006-7629-3833).

**Status:** **Targets 1, 2 and 3 are all Lean-proved.** Target 1
(Proposition 3.1: soundness and factor recovery), Target 2
(Proposition 4.1: exact quadratic-residue sieve count) and Target 3
(Proposition 4.2: uniform two-adic saturation lower bound) are
machine-verified in CI, including the axiom audit. Their source-to-code
correspondence has been checked against the published v11.0.3, page 3
(Target 1, both signs of the converse), Proposition 4.1 (Target 2) and
Proposition 4.2 (Target 3). An external human referee review has **not**
been performed.

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

## What Target 2 proves

`DyadicShells/QRSieve.lean` proves the exact square-or-zero sieve pass
count `#pass = (|F| + χ(N))/2` (Proposition 4.1) for every finite field
of odd characteristic and every `N ≠ 0`, via a difference-of-squares conic
parametrization, Mathlib's `quadraticChar_card_sqrts`, and the character
sum `∑_A χ(A²−N) = −1`. The zero residue is counted as passing. The
finite-field form is stronger than the source's prime-field statement.

## What Target 3 proves

`DyadicShells/TwoAdicSaturation.lean` proves Proposition 4.2: for odd
`N ≥ 3` the two-adic pass proportion satisfies `π_m(N) ≥ 2^(-(2v+3))`
uniformly in `m` (`v = v₂((N-1)/2)`), stated as
`2^m ≤ 2^(2v+3)·#{A<2^m : A²-N a square mod 2^m}`. The mechanism is a
Hensel square-lift showing the whole congruence class `A ≡ (N+1)/2`
`(mod 2^(2v+3))` is two-adically square — so two-adic filtering saturates
and cannot be strengthened by lifting.

## Remaining work

All three propositions (3.1, 4.1, 4.2) are Lean-proved. No new Zenodo DOI
has been assigned for these formalization files. AI assistance is disclosed;
an independent human peer review of the source-to-code fidelity remains
recommended.
