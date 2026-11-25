/-
Dyadic Shells — PaperIndex (DRAFT). A TYPE-CHECKED map from each numbered
published statement to its Lean counterpart. Because every entry is an `alias`
to a real declaration, a rename or deletion in the proof files breaks the build:
the map cannot silently rot, unlike a prose table in Markdown.

This is the Lean companion to `THEOREM_MAPPING.md`; keep the prose file for
human-readable source-to-code fidelity notes, and keep this file for the
machine-checked name correspondence. Where the Lean form differs from the paper,
the difference is stated in the doc-comment above the alias.
-/
import MainResults
import DyadicShells.Soundness
import DyadicShells.QRSieve
import DyadicShells.TwoAdicSaturation
import DyadicShells.TwoAdicExact
import ClosedForms
import HyperbolicSieve

namespace PaperIndex

/-! ## v11.0.3, Proposition 3.1 — soundness and factor recovery

Difference from the paper: the paper restricts `p, q` to distinct odd primes and
`a, b` to coprime positive odd integers `< min(p,q)` with an anchored center; the
Lean recovery corollary needs none of distinctness, oddness, or `gcd(a,b)=1` —
cross-coprimality is derived from primality and the bounds. The paper's
`t = (a·p − b·q)/2` is encoded as `t = a·p − A`. -/

/-- Proposition 3.1, exactly under the published hypotheses (primes + bounds). -/
alias prop31_published := DyadicShells.prop31_factor_recovery

/-- Proposition 3.1, properness of the recovered factors (`1 < p < n`, `1 < q < n`). -/
alias prop31_proper := DyadicShells.prop31_recovered_proper

/-- The statement-file form of Proposition 3.1 (Mathlib-only surface). -/
alias prop31_statement := DyadicShellsStatements.Prop31

/-! ## v11.0.3, Proposition 4.1 — exact quadratic-residue sieve count

Difference from the paper: the published statement is for a prime field; the Lean
form holds for every finite field of odd characteristic and every `N ≠ 0`, which
is strictly more general. The zero residue is counted as passing, as the source
requires. -/

/-- Proposition 4.1, exact inclusive pass count `#pass = (|F| + χ(N))/2`. -/
alias prop41_published := DyadicShells.qr_exact_pass_count

/-- Proposition 4.1, the doubled form `2·#pass = |F| + χ(N)` (no division). -/
alias prop41_doubled := DyadicShells.qr_exact_pass_count_double

/-- The statement-file form of Proposition 4.1. -/
alias prop41_statement := DyadicShellsStatements.Prop41

/-! ## v11.0.3, Proposition 4.2 — uniform two-adic saturation

No material difference from the paper: `π_m(N) ≥ 2^(−(2v+3))` uniformly in `m`,
stated as `2^m ≤ 2^(2v+3)·#pass`, with `v = v₂((N−1)/2)`. -/

/-- Proposition 4.2, the uniform lower bound on the two-adic pass density. -/
alias prop42_published := DyadicShells.twoadic_saturation

/-- The statement-file form of Proposition 4.2. -/
alias prop42_statement := DyadicShellsStatements.Prop42

/-! ## Target 4 (manuscript, not yet public) — exact two-adic counts, milestone A -/

/-- Milestone A: the `N mod 8` reduction of the exact two-adic pass count. -/
alias target4_modEight := DyadicShells.passCard_eq_of_modEq_eight

/-- Milestone A companion: unit-square invariance of the pass count. -/
alias target4_unitSquare := DyadicShells.passCard_unit_sq_mul

/-- The statement-file form of Target 4, milestone A. -/
alias target4_statement := DyadicShellsStatements.Target4MilestoneA

/-! ## Target 4 (manuscript) — exact two-adic closed forms, milestone B -/

/-- Milestone B: `N ≡ 3 (mod 4)` ⇒ `C_m = 2^(m-2)` (covers `N ≡ 3, 7 (mod 8)`). -/
alias target4b_threeModFour := DyadicShells.ClosedForms.passCard_three_mod_four

/-- Milestone B: `N ≡ 5 (mod 8)` ⇒ `C_m = 2^(m-3)`. -/
alias target4b_fiveModEight := DyadicShells.ClosedForms.passCard_five_mod_eight

/-- Milestone B: `N ≡ 1 (mod 8)`, even `m` ⇒ `3·C_m = 2^(m-3)+16`. -/
alias target4b_oneModEightEven := DyadicShells.ClosedForms.passCard_one_mod_eight_even

/-- Milestone B: `N ≡ 1 (mod 8)`, odd `m` ⇒ `3·C_m = 2^(m-3)+20`. -/
alias target4b_oneModEightOdd := DyadicShells.ClosedForms.passCard_one_mod_eight_odd

/-- Milestone B: sharp unconditional density `2^m < 24·C_m` for odd `N`. -/
alias target4b_density := DyadicShells.ClosedForms.passCard_density

/-- The statement-file form of Target 4, milestone B. -/
alias target4b_statement := DyadicShellsStatements.Target4MilestoneB

/-! ## Target 4 (manuscript v11.7.23) — the hyperbolic sieve mod 2^e, milestone C -/

/-- Milestone C (Theorem 3, doubled form): `2·|L_{N,2^e,k}| = C_e(k·N)`. -/
alias target4c_theorem3 := DyadicShells.HyperbolicSieve.two_mul_card_hyperbolicSieve

/-- Milestone C (Theorem 3, `/2` form): `|L_{N,2^e,k}| = C_e(k·N)/2`. -/
alias target4c_half := DyadicShells.HyperbolicSieve.card_hyperbolicSieve_eq_half

/-- The statement-file form of Target 4, milestone C. -/
alias target4c_statement := DyadicShellsStatements.Target4MilestoneC

end PaperIndex
