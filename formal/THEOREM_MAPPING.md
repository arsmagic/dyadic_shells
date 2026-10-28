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
- `proper_divisor_criterion_either_sign` (T1-B): the published
  converse for **either** `gcd(A+t,n)` or `gcd(A-t,n)`. When
  `1<d<|n|`, the gcd is a proper divisor. **[proved]**
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

**Status (Target 1): Lean-proved, with an internal PDF-to-code
fidelity review completed 2026-10-28.** The original is v11.0.3,
PDF p. 3, Definition 3.2 and Proposition 3.1. The source restricts
`p,q` to distinct odd primes, and `a,b` to coprime positive odd
integers smaller than `min(p,q)`; the anchored center is a special
case of the Lean premise `2*A=a*p+b*q`. The Lean recovery corollary
is **more general**, because distinctness, oddness, coprimality of
`a,b` and anchored membership are not needed for the algebraic
implication. The published `t=(a*p-b*q)/2` is represented by
`t=a*p-A` and derived from the center equality. The converse
covers both signs and both strict inequalities on the gcd.
The formulas match; this is not an external human peer review.

No `sorry`/`admit`; named axioms are printed by
`DyadicShells/AxiomAudit.lean` in CI (see
`VERIFICATION_STATUS.md`). External mathematical peer review is
recommended before any new formal-verification publication.

## 2. Exact quadratic-residue sieve fraction

**Published:** v11.0.3, Proposition 4.1.
For odd prime ℓ not dividing N,
`# { A mod ℓ | A² − N is a square } = (ℓ + χℓ(N))/2`.

**Lean:** `DyadicShells/QRSieve.lean`
- `square_test_iff_factor_pair` gives the `(A−y)(A+y)=N` identity.
- `exact_square_witness_passes` establishes finite-field sieve soundness.

**Exact count (Target 2, proved):**
- `qrPairsEquivNonzero`: explicit equivalence between the conic
  `A²-y²=N` and nonzero field elements for `N≠0` and characteristic ≠2.
- `qrPairsEquivSigma`: reindex pairs by their first coordinate.
- `qr_zero_center_count`: #solutions of `A²=N` from Mathlib's
  `quadraticChar_card_sqrts`.
- `qrPairs_count_as_character_sum` and `qr_quadratic_character_sum`:
  the exact character-sum identity `∑ₐ χ(A²-N)=-1`.
- `qr_exact_pass_count_double` and `qr_exact_pass_count`:
  the exact count `2·#pass = #F+χ(N)` and
  `#pass=(#F+χ(N))/2` for any finite field with odd characteristic
  and `N≠0`. The passing predicate includes zero. **[proved]**

**Status (Target 2): Lean-proved.** Verified by CI
[run #35](https://github.com/arsmagic/dyadic_shells/actions/runs/40697899551)
(commit `2e03d72`): `lake build`, axiom audit (all five declarations
depend only on `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`
or `Lean.ofReduceBool`), and `sorry`/`admit` rejection all succeeded.
No equidistribution, independent-filter or probabilistic hypothesis is
introduced. The generic finite-field form is stronger than the source's
prime-field case. This is machine verification, not an external human
peer review.

## 3. Two-adic saturation

**Published:** v11.0.3, Proposition 4.2.
For odd N ≥3 and `v=v₂((N−1)/2)`, for every `m`,
`πₘ(N)≥2^(-(2v+3))`.

**Lean:** `DyadicShells/TwoAdicSaturation.lean`
- `odd_center_witness`, `every_odd_has_twoAdic_witness`: explicit integral
  square certificate and non-emptiness at each modulus.
- `odd_sq_modEq_one_eight`, `isSquare_mod_two_pow_of_one_mod_eight`:
  Hensel square-lifting, `c≡1 mod 8 ⇒ ∀k ∃y, y²≡c mod 2^k`.
- `class_passesZ`, `twoAdicPass_of_classN`: the full class
  `A≡2^v·w+1 mod 2^(2v+3)` (with `(N-1)/2=2^v·w`, `w` odd) is a 2-adic
  square at every level. **[proved]**
- `twoAdicPass_of_succ`: squareness descends `m+1 → m` (monotonicity of π_m).
- `twoadic_saturation`: the uniform density bound
  `2^m ≤ 2^(2v+3)·#{A<2^m : A²-N a square mod 2^m}` for odd `N≥3` and
  every `m`, i.e. `π_m(N) ≥ 2^(-(2v+3))`. **[proved]**

**Status (Target 3): Lean-proved.** Verified by CI
[run #44](https://github.com/arsmagic/dyadic_shells/actions/runs/40716469544)
(commit `768e425`): `lake build`, axiom audit (standard axioms only; no
`sorryAx`/`ofReduceBool`), and `sorry`/`admit` rejection all succeeded.
The congruence-class lifting (not mere non-emptiness) gives the uniform
positive density. Machine verification, not an external human peer review.

## Scope exclusions

No claimed formal verification of: adaptive sieve independence
heuristics, odd-prime depth saturation, FP-MITM complexity or
cost-model crossovers.
