import Mathlib

/-!
# Two-adic square witnesses: a checked starting lemma

Source: Khachatryan v11.0.3, Proposition 4.2, and v11.5.17.

The published saturation theorem states that for odd N ≥ 3, the fraction
of A modulo 2^m such that A² - N is a square is bounded below by
2^(-(2 * v₂((N-1)/2) + 3)), uniformly in m.

This file proves an exact witness for every odd N and every 2-power modulus.
It does **not** yet establish the claimed positive uniform density:
one witness per modulus does not imply a lower bound independent of m.
See THEOREM_MAPPING.md.
-/

namespace DyadicShells

def twoAdicPass (N m A : ℕ) : Prop :=
  ∃ y : ℕ, Nat.ModEq (2 ^ m) (A ^ 2) (N + y ^ 2)

theorem odd_center_witness (k m : ℕ) :
    twoAdicPass (2 * k + 1) m (k + 1) := by
  refine ⟨k, ?_⟩
  have h : (k + 1) ^ 2 = (2 * k + 1) + k ^ 2 := by ring
  change ((k + 1) ^ 2) % (2 ^ m) = ((2 * k + 1) + k ^ 2) % (2 ^ m)
  rw [h]

theorem every_odd_has_twoAdic_witness
    (N m : ℕ) (hodd : Odd N) :
    ∃ A : ℕ, twoAdicPass N m A := by
  rcases hodd with ⟨k, rfl⟩
  exact ⟨k + 1, odd_center_witness k m⟩

end DyadicShells
