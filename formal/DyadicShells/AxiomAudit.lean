import DyadicShells.Soundness
import DyadicShells.QRSieve
import DyadicShells.TwoAdicSaturation
import DyadicShells.TwoAdicExact
-- Statement-surface files (MainResults is Mathlib-only; Solution proves the
-- four claims from the theorems above; PaperIndex is the type-checked alias map).
-- Importing them here wires them into `lake build` and the axiom audit.
import MainResults
import Solution
import PaperIndex
import ClosedForms
import HyperbolicSieve
import SparseBias
import SparseBiasAsymp
import SparseFamily

/-!
# Axiom audit (Target 1)

`#print axioms` for every named Target 1 theorem. The output is emitted during
`lake build` and therefore appears in the GitHub Actions log.

Only the standard Mathlib axioms `propext`, `Classical.choice`, and `Quot.sound`
are expected. A proof-hole axiom (`sorryAx`), a user-declared axiom, or
`Lean.ofReduceBool` (introduced by compiled-decision tactics) would each be a
red flag; none are present here.
-/

#print axioms DyadicShells.weighted_center_decomposition
#print axioms DyadicShells.weighted_center_square_identity
#print axioms DyadicShells.weighted_center_factor_witnesses
#print axioms DyadicShells.square_certificate_factorization
#print axioms DyadicShells.square_certificate_dvd
#print axioms DyadicShells.gcd_factor_recovery
#print axioms DyadicShells.prop31_factor_recovery
#print axioms DyadicShells.prop31_recovered_proper
#print axioms DyadicShells.weighted_certificate_factorization
#print axioms DyadicShells.gcd_dvd_modulus
#print axioms DyadicShells.proper_divisor_criterion
#print axioms DyadicShells.proper_divisor_criterion_either_sign

/-! ## Target 2: exact quadratic-residue sieve count -/
#print axioms DyadicShells.qr_zero_center_count
#print axioms DyadicShells.qrPairs_count_as_character_sum
#print axioms DyadicShells.qr_quadratic_character_sum
#print axioms DyadicShells.qr_exact_pass_count_double
#print axioms DyadicShells.qr_exact_pass_count

/-! ## Target 3: two-adic saturation (Proposition 4.2) -/
#print axioms DyadicShells.odd_sq_modEq_one_eight
#print axioms DyadicShells.isSquare_mod_two_pow_of_one_mod_eight
#print axioms DyadicShells.twoAdicPass_of_succ
#print axioms DyadicShells.class_passesZ
#print axioms DyadicShells.twoAdicPass_of_intWitness
#print axioms DyadicShells.twoAdicPass_of_classN
#print axioms DyadicShells.twoAdicPass_congr
#print axioms DyadicShells.twoadic_saturation

/-! ## Target 4 (milestone A): reduction of the exact two-adic count to `N mod 8` -/
#print axioms DyadicShells.isSquare_unit_sq_mul_iff
#print axioms DyadicShells.passCard_unit_sq_mul
#print axioms DyadicShells.exists_inv_of_odd
#print axioms DyadicShells.passCard_eq_of_modEq_eight

/-! ## Statement surface: the four claims proved in `Solution.lean` against the
Mathlib-only statements of `MainResults.lean`. These must depend only on the
three standard axioms. -/
#print axioms DyadicShellsStatements.prop31
#print axioms DyadicShellsStatements.prop41
#print axioms DyadicShellsStatements.prop42
#print axioms DyadicShellsStatements.target4MilestoneA
#print axioms DyadicShellsStatements.target4MilestoneB
#print axioms DyadicShellsStatements.target4MilestoneC

/-! ## Sparse-bias gates, no-finite-gate theorem, binomial lemmas, and the
sparse-offset limits (Propositions 13-16 and Corollary 17 of the paper). -/
#print axioms DyadicShells.SparseBias.gate_three_mod_eight
#print axioms DyadicShells.SparseBias.gate_seven_mod_eight
#print axioms DyadicShells.SparseBias.gate_five_mod_eight
#print axioms DyadicShells.SparseBias.gate_five_count_mod32
#print axioms DyadicShells.SparseBias.castHom_N_five_cases
#print axioms DyadicShells.SparseBias.passCard_one_succ_ne_two_mul
#print axioms DyadicShells.SparseBias.no_finite_gate_one_mod_eight
#print axioms DyadicShells.SparseBias.sum_choose_sub_two_le
#print axioms DyadicShells.SparseBias.choose_pred_ratio_eq
#print axioms DyadicShells.SparseBias.choose_pred_ratio_tendsto_zero
#print axioms DyadicShells.SparseFamily.bad_fraction_tendsto_zero
#print axioms DyadicShells.SparseFamily.sparse_pass_limit
#print axioms DyadicShells.SparseFamily.cor17_three
#print axioms DyadicShells.SparseFamily.cor17_seven
#print axioms DyadicShells.SparseFamily.cor17_five
#print axioms DyadicShells.SparseFamily.cor17_three_anchorfree
#print axioms DyadicShells.SparseFamily.cor17_seven_anchorfree
