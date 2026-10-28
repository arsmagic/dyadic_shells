import Mathlib

/-!
# Weighted difference-of-squares: verified algebraic core

Source: Khachatryan, Dyadic Shells v11.5.17, DOI 10.5281/zenodo.23432486,
and v11.0.3, Proposition 3.1.

This file currently formalizes the **identity** and the two divisibility witnesses.
The stronger `gcd = p, q` statement (under primeness/coprimality hypotheses) is
a remaining proof obligation; see THEOREM_MAPPING.md.

These definitions and lemmas make no claims about RSA attack complexity.
-/

namespace DyadicShells

theorem weighted_center_decomposition
    (a b p q A t : ℤ)
    (hA : 2 * A = a * p + b * q)
    (ht : 2 * t = a * p - b * q) :
    A + t = a * p ∧ A - t = b * q := by
  constructor <;> linarith

theorem weighted_center_square_identity
    (a b p q A t : ℤ)
    (hA : 2 * A = a * p + b * q)
    (ht : 2 * t = a * p - b * q) :
    A ^ 2 - (a * b) * (p * q) = t ^ 2 := by
  obtain ⟨hp, hq⟩ := weighted_center_decomposition a b p q A t hA ht
  have hprod : (A + t) * (A - t) = (a * b) * (p * q) := by
    rw [hp, hq]
    ring
  calc
    A ^ 2 - (a * b) * (p * q) =
        (A + t) * (A - t) - (a * b) * (p * q) + t ^ 2 := by ring
    _ = t ^ 2 := by rw [hprod]; ring

theorem weighted_center_factor_witnesses
    (a b p q A t : ℤ)
    (hA : 2 * A = a * p + b * q)
    (ht : 2 * t = a * p - b * q) :
    p ∣ A + t ∧ q ∣ A - t := by
  obtain ⟨hp, hq⟩ := weighted_center_decomposition a b p q A t hA ht
  constructor
  · rw [hp]
    exact ⟨a, by ring⟩
  · rw [hq]
    exact ⟨b, by ring⟩

end DyadicShells
