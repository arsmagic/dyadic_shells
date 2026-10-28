# Mapping published statements to Lean obligations

## 1. Soundness and factor recovery

**Published:** v11.0.3, Proposition 3.1; v11.5.17 weighted-center identity.

**Lean:** `DyadicShells/Soundness.lean`
- `weighted_center_decomposition`: sum/difference recover `ap,bq`.
- `weighted_center_square_identity`: `A²-abpq=t²`.
- `weighted_center_factor_witnesses`: divisibility by factors.
- `square_certificate_factorization`: arbitrary exact square certificate
  `A²-N=t²` gives the explicit factorization `N=(A-t)(A+t)` (no planted
  multipliers required). **[proved, CI #8]**
- `square_certificate_dvd`: both cofactors `(A-t),(A+t)` divide `N`.
  **[proved, CI #8]**
- `gcd_factor_recovery`: exact recovery `gcd(A+t,N)=|p|`, `gcd(A-t,N)=|q|`
  in the planted-multiplier setting. **[proved, CI #8]**

**Status (Target 1): proved in Lean, pending review.** The gcd recovery is
stated with the **exact cross-coprimality hypotheses** `gcd(a,q)=1`,
`gcd(b,p)=1` (Int.gcd), rather than the source's *sufficient* bound
`a,b<min(p,q)`; `gcd(a,b)=1` is deliberately not used (insufficient, per the
source warning). No primeness of `p,q` is needed for these statements. The
result is `=|p|,|q|` (natAbs), matching the ℕ-valued `Int.gcd`.

**Remaining for Target 1 (review-level, not code):**
- Human/reviewer confirmation that these statements faithfully encode the
  published Proposition 3.1 (including that the exact-coprimality hypotheses
  are the intended reading of the source's conditions).
- Optional: a corollary deriving the cross-coprimality conditions from the
  source's bound `0<a,b<min(p,q)` with `p,q` distinct primes, if the published
  hypotheses are preferred verbatim.

## 2. Exact quadratic-residue sieve fraction

**Published:** v11.0.3, Proposition 4.1.
For odd prime ℓ not dividing N,
`# { A mod ℓ | A² − N is a square } = (ℓ + χℓ(N))/2`.

**Lean:** `DyadicShells/QRSieve.lean`
- `square_test_iff_factor_pair` gives the `(A−y)(A+y)=N` identity.
- `exact_square_witness_passes` establishes finite-field sieve soundness.

**Open:** exact finite-field character sum / pair-count proof, and exact
cardinality in terms of quadratic character. The statement itself is
not yet encoded as a theorem.

## 3. Two-adic saturation

**Published:** v11.0.3, Proposition 4.2.
For odd N ≥3 and `v=v₂((N−1)/2)`, for every `m`,
`πₘ(N)≥2^(-(2v+3))`.

**Lean:** `DyadicShells/TwoAdicSaturation.lean`
- `odd_center_witness`: explicit integral square certificate.
- `every_odd_has_twoAdic_witness`: non-emptiness at each modulus.

**Open:** square lifting to the 2-adics for the full congruence class
`A≡(N+1)/2 mod 2^(2v+3)` and cardinality/density lower bound
uniform in m. Non-emptiness alone is not saturation.

## Scope exclusions

No claimed formal verification of: adaptive sieve independence
heuristics, odd-prime depth saturation, FP-MITM complexity or
cost-model crossovers.
