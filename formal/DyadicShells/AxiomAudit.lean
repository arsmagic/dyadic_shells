import DyadicShells.Soundness
import DyadicShells.QRSieve

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
