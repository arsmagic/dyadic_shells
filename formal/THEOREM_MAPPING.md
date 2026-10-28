# Mapping published statements to Lean obligations

## 1. Soundness and factor recovery

**Published:** v11.0.3, Proposition 3.1; v11.5.17 weighted-center identity.

**Lean:** `DyadicShells/Soundness.lean`
- `weighted_center_decomposition`: sum/difference recover `ap,bq`.
- `weighted_center_square_identity`: `A²-abpq=t²`.
- `weighted_center_factor_witnesses`: divisibility by factors.

**Open:** formulate and prove precise gcd equalities using distinct odd
prime hypotheses and suitable cross-coprimality conditions, avoiding
unjustified assumptions on multiplier orientation. Formalize that an
arbitrary square witness plus a proper nontrivial gcd certifies a factor.

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
