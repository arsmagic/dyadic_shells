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
  in the planted-multiplier setting, under cross-coprimality
  `gcd(a,q)=gcd(b,p)=1` (no primality needed). **[proved]**
- `prop31_factor_recovery` (T1-A): Proposition 3.1 under the **published
  hypotheses** — `p,q` prime, `0<a,b<min p q`, and `t := a*p - A` so that
  `2t = a*p - b*q` holds **by construction**; cross-coprimality is **derived**
  from primality + the bounds, then `gcd_factor_recovery` is applied. Concludes
  `gcd(A+t,pq)=p`, `gcd(A-t,pq)=q`. **[proved]**
- `prop31_recovered_proper` (T1-A): the recovered values are **proper**
  divisors, `1<p<n` and `1<q<n` for `n=pq`, `p,q` prime. **[proved]**
- `weighted_certificate_factorization` (T1-B): `A²-k·n=t² ⇒ k·n=(A-t)(A+t)`.
  **[proved]**
- `gcd_dvd_modulus`, `proper_divisor_criterion` (T1-B): a cofactor gcd always
  divides `|n|`, but is a *proper* divisor only when `1<gcd<|n|` — the explicit
  acceptance criterion. **[proved]**
- regression `example`s (T1-B): the certificate `n=35,k=3,A=53,t=52` satisfies
  `53²-3·35=52²` yet both cofactor gcds are trivial (`1` and `35`), proving an
  exact *weighted* square is **not** by itself a factor-recovery certificate.

**Three distinct statements, kept separate (do not conflate):**
1. *Generalized certificate* (`square_certificate_*`,
   `weighted_certificate_factorization`): sound for arbitrary `A,t,k`; factors
   `N` or `k·n` but gives a *proper* factor only when the acceptance criterion
   `1<gcd<|n|` holds (see the `n=35` regression).
2. *Planted recovery* (`gcd_factor_recovery`): exact factors under cross-
   coprimality; neither primality nor `gcd(a,b)=1` is used.
3. *Published Proposition 3.1* (`prop31_factor_recovery`,
   `prop31_recovered_proper`): the source's own hypotheses (primes + bounds),
   with cross-coprimality **derived** and properness established.

**Status (Target 1): code-proved, equivalence review pending.** No
`sorry`/`admit`; axioms audited in `DyadicShells/AxiomAudit.lean` (see
`VERIFICATION_STATUS.md`). `0<a,b<min p q` is used verbatim as the source's
condition, from which `gcd(a,q)=gcd(b,p)=1` is proved; `gcd(a,b)=1` is neither
used nor sufficient.

**Remaining for Target 1 (review-level, not code):** human/reviewer
confirmation that `prop31_*` faithfully encode the published Proposition 3.1.

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
