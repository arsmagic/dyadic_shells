import DyadicShells.Soundness
import DyadicShells.QRSieve
import DyadicShells.TwoAdicSaturation
import DyadicShells.PR2FullIff

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

/-! ## PR2 full iff candidate (sandbox only; not on `main`) -/
#print axioms DyadicShells.PR2FullIff.isSquare_zmod_two_pow_iff_of_odd
#print axioms DyadicShells.PR2FullIff.isSquare_zmod_two_pow_iff_of_odd_three_le
