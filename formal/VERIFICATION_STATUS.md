# Formal verification status — Dyadic Shells

**Mathematical author:** Arsen A. Khachatryan (SibarS Labs; ORCID 0009-0006-7629-3833).

## Target 1: Soundness and factor recovery

**Mathematical status: Lean-proved.** The full soundness/recovery claims of
v11.0.3 Proposition 3.1 are covered by `DyadicShells/Soundness.lean`,
including both signs in the converse; see `THEOREM_MAPPING.md`.

- [x] Weighted difference-of-squares identity and factor divisibility.
- [x] Arbitrary exact-square factorization (`k=1`).
- [x] Planted-factor recovery under explicitly derived cross-coprimality.
- [x] Corollary from published prime and multiplier bounds, with `t` constructed.
- [x] Properness of the recovered prime factors.
- [x] General weighted certificate distinguishes factorization of `k*n`
      from recovery of a proper divisor of `n`.
- [x] Both signs of the converse: `d = gcd(A ± t, n)` and
      `1 < d < |n|` imply `d` is a proper divisor of `|n|`.
- [x] Concrete counterexample `n=35,k=3,A=53,t=52` is checked.
- [x] Technical comparison with the **published PDF**, v11.0.3,
      p. 3, Proposition 3.1 and Definition 3.2 (2026-10-28).
- [x] Lean 4.24.0 and pinned Mathlib v4.24.0: successful CI and axiom audit
      (baseline: [run #16](https://github.com/arsmagic/dyadic_shells/actions/runs/40663159966)).
- [x] The formal project and proof files are present on `main`.
- [ ] External, independent human mathematical peer review (recommended
      before a new formal-verification paper; **not** a Lean proof gap).

### Source-to-code fidelity

The source assumes `n=p*q` for distinct odd primes `p,q`, and
coprime positive odd multipliers `a,b < min(p,q)`, with a planted
anchored center satisfying `a*p+b*q=2*A`. The Lean corollary proves
factor recovery for **all** primes `p,q` and positive `a,b` within
these bounds given `2*A=a*p+b*q`, a mathematically *stronger* statement:
the source's distinctness, oddness, `gcd(a,b)=1`, and anchored-center
membership are not needed for the algebraic recovery implication.
The source's `t=(a*p-b*q)/2` is encoded as `t=a*p-A`.
The converse is formalized for both `A+t` and `A-t`, including the
explicit proper-divisor bounds. This is a technical equivalence review,
**not** an independent published referee report.

### Machine proof and axiom policy

GitHub Actions runs `lake build`, the `#print axioms` report from
`DyadicShells/AxiomAudit.lean`, and rejects `sorry`/`admit`.
The baseline axiom audit (run #16) listed only `propext`,
`Classical.choice`, and `Quot.sound`, with no `sorryAx`
or `Lean.ofReduceBool`. The new both-sign corollary is included in the
same automated audit in subsequent builds.
Source and diagnostics: [Lean workflow](https://github.com/arsmagic/dyadic_shells/actions/workflows/lean-formal.yml).

## Target 2: Exact quadratic-residue sieve count

**Mathematical status: Lean-proved.** The exact square-or-zero sieve
pass count of v11.0.3 Proposition 4.1 is formalized in
`DyadicShells/QRSieve.lean`, in a form valid for **every** finite field
of odd characteristic and **every** `N ≠ 0` — strictly more general than
the source's prime-field statement; see `THEOREM_MAPPING.md`.

- [x] Difference-of-squares conic parametrization `qrPairsEquivNonzero`
      (`|F|−1` solution pairs for `N ≠ 0`, characteristic ≠ 2).
- [x] Zero-center count `qr_zero_center_count` via Mathlib
      `quadraticChar_card_sqrts`.
- [x] Exact character sum `∑_A χ(A²−N) = −1` (`qr_quadratic_character_sum`).
- [x] Pointwise inclusive square-or-zero indicator identity
      `2·1_{IsSquare z} = 1 + χ(z) + 1_{z=0}`.
- [x] Exact count `2·#pass = |F| + χ(N)` and `#pass = (|F|+χ(N))/2`
      (`qr_exact_pass_count_double`, `qr_exact_pass_count`); the zero
      residue is counted as passing, as the source requires.
- [x] Lean 4.24.0 and pinned Mathlib v4.24.0: successful CI build and
      axiom audit
      ([run #35](https://github.com/arsmagic/dyadic_shells/actions/runs/40697899551),
      commit `2e03d72`).
- [ ] External, independent human mathematical peer review (recommended;
      **not** a Lean proof gap).

### Machine proof and axiom policy (Target 2)

The axiom audit for run #35 lists all five Target 2 declarations
(`qr_zero_center_count`, `qrPairs_count_as_character_sum`,
`qr_quadratic_character_sum`, `qr_exact_pass_count_double`,
`qr_exact_pass_count`) as depending only on `propext`,
`Classical.choice`, and `Quot.sound`, with no `sorryAx` or
`Lean.ofReduceBool`; `sorry`/`admit` are rejected in the same run.
No equidistribution, independent-filter, or probabilistic hypothesis is
introduced.

## Target 3: Uniform two-adic saturation

**Mathematical status: Lean-proved.** Proposition 4.2's uniform lower
bound on the two-adic pass density is formalized in
`DyadicShells/TwoAdicSaturation.lean` as `twoadic_saturation`: for odd
`N ≥ 3` there is `v = v₂((N-1)/2)` such that for every `m`

  `2^m ≤ 2^(2v+3) · #{A < 2^m : A²-N is a square mod 2^m}`,

i.e. the pass proportion `π_m(N) ≥ 2^(-(2v+3))`, uniformly in `m`.

- [x] Hensel square-lifting `isSquare_mod_two_pow_of_one_mod_eight`
      (`c ≡ 1 mod 8 ⇒ ∀ k, ∃ y, y² ≡ c mod 2^k`) and `odd² ≡ 1 mod 8`.
- [x] The whole residue class `A ≡ 2^v·w + 1 (mod 2^(2v+3))` is
      two-adically square at every level (`class_passesZ`,
      `twoAdicPass_of_classN`), via the `2`-adic decomposition
      `(N-1)/2 = 2^v·w`, `w` odd.
- [x] Monotone descent `twoAdicPass_of_succ` (squareness mod `2^(m+1)`
      ⇒ mod `2^m`), the monotonicity ingredient of `π_m`.
- [x] The density count: injecting the arithmetic progression
      `r + j·2^(2v+3)` of passing residues gives `#pass ≥ 2^(m-(2v+3))`.
- [x] Lean 4.24.0 and pinned Mathlib v4.24.0: successful CI build and
      axiom audit
      ([run #44](https://github.com/arsmagic/dyadic_shells/actions/runs/40716469544),
      commit `768e425`).
- [ ] External, independent human mathematical peer review (recommended;
      **not** a Lean proof gap).

### Machine proof and axiom policy (Target 3)

The axiom audit for run #44 lists all Target 3 declarations
(`odd_sq_modEq_one_eight`, `isSquare_mod_two_pow_of_one_mod_eight`,
`twoAdicPass_of_succ`, `class_passesZ`, `twoAdicPass_of_intWitness`,
`twoAdicPass_of_classN`, `twoAdicPass_congr`, `twoadic_saturation`) as
depending only on `propext`, `Classical.choice`, `Quot.sound` (two of them
only on `propext`), with no `sorryAx` or `Lean.ofReduceBool`;
`sorry`/`admit` are rejected in the same run. The proof is purely
arithmetic/Hensel: no equidistribution or probabilistic hypothesis.

## Target 4: Exact two-adic pass counts (milestones A, B and C)

**Mathematical status: milestones A, B and C all Lean-proved.**
Published manuscript v11.7.23: exact `C_m(N) = #{A mod 2^m : A²-N square}`
for every odd `N` and `m`, the sharp uniform bound `π_m(N) > 1/24`, and
`|L_{N,2^e,k}| = C_e(kN)/2` for Hittmeir's hyperbolic sieve sets. Milestone A
(the `N mod 8` reduction) and milestone B (the closed forms for every odd class
and the unconditional density) and milestone C (Hittmeir's hyperbolic-sieve
identity, Theorem 3) are all machine-verified.

- [x] Unit-square invariance `passCard_unit_sq_mul` (any `ZMod n`):
`#{A : A²-u²N square} = #{A : A²-N square}` for a unit `u`.
- [x] Reduction to `N mod 8` `passCard_eq_of_modEq_eight`: odd `N ≡ N' (mod 8)`
have equal pass counts modulo every `2^m`.
- [x] Lean 4.24.0 and pinned Mathlib v4.24.0: successful CI build and axiom audit
([run #42462026945](https://github.com/arsmagic/dyadic_shells/actions/runs/42462026945),
branch `formal/target4-twoadic-exact`); axioms only `propext`, `Classical.choice`,
`Quot.sound`.
- [x] Milestone B: closed forms for every odd class (merged to `main`, PR #13):
`N ≡ 3 (mod 4)` ⇒ `C_m = 2^(m-2)` (`passCard_three_mod_four`, covers `3,7 mod 8`);
`N ≡ 5 (mod 8)` ⇒ `C_m = 2^(m-3)` (`passCard_five_mod_eight`); `N ≡ 1 (mod 8)` ⇒
`3·C_m = 2^(m-3)+16` even `m`, `+20` odd `m` (`passCard_one_mod_eight_even/odd`);
and the now-unconditional density `2^m < 24·C_m` (`passCard_density`). Lean
v4.33.1, Mathlib `0df444a…`; axioms only `propext`, `Classical.choice`,
`Quot.sound`, no `sorryAx`.
- [x] Milestone B independent re-check: restated in the Mathlib-only statement
surface as `DyadicShellsStatements.Target4MilestoneB` (`MainResults.lean`),
proved in `Solution.lean`, and accepted by the second-kernel comparator (nanoda)
listed in `comparator.json`.
- [x] Milestone C (Theorem 3): `|L_{N,2^e,k}| = C_e(k·N)/2` for odd `N, k`,
`e ≥ 1`, formalized in `HyperbolicSieve.lean` as `two_mul_card_hyperbolicSieve`
(doubled form `2·|L| = C_e(k·N)`) and `card_hyperbolicSieve_eq_half` (the `/2`
form); restated on the statement surface as `Target4MilestoneC` and accepted by
the second-kernel comparator (nanoda). Axioms only `propext`, `Classical.choice`,
`Quot.sound`, no `sorryAx`.

## Remaining research targets

- [ ] Author approval for any **new DOI or external manuscript**.

**Targets 1, 2 and 3 are all Lean-proved.** Experimental performance,
FP-MITM complexity, and novelty are outside the scope of these formal
proofs; an external human referee review is still recommended.

AI assistance was used in preparing the formalization; the mathematical
author remains responsible for claims in any later scientific publication.
