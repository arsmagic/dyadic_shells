import DyadicShells.Soundness

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
