import Mathlib
import DyadicShells.QRSieve
import DyadicShells.TwoAdicSaturation

/-!
# Upstream-candidate lemmas (library-standard forms)

Validation sandbox (NOT for merge to `main`): the two lemmas below are the
general, Mathlib-style forms of results proved specially in this project.
They are validated against the project's pinned Mathlib v4.24.0 here by
REUSING the already-proved special cases. For the actual Mathlib PR the base
cases are ported inline.

* `quadraticChar_sum_quadratic` — generalizes `qr_quadratic_character_sum`.
* `isSquare_zmod_two_pow_of_mod_eight` — reformulates
  `isSquare_mod_two_pow_of_one_mod_eight` in the `ZMod`/`IsSquare` idiom.
-/

namespace DyadicShells.Upstream
open Finset

/-- **Quadratic character sum over a quadratic polynomial.** For a finite
field `F` of odd characteristic, if `a ≠ 0` and the discriminant
`b² - 4 a c ≠ 0`, then `∑ x, χ(a x² + b x + c) = -χ(a)`. -/
theorem quadraticChar_sum_quadratic
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (h2 : ringChar F ≠ 2) {a : F} (b c : F) (ha : a ≠ 0)
    (hdisc : b ^ 2 - 4 * a * c ≠ 0) :
    (∑ x : F, quadraticChar F (a * x ^ 2 + b * x + c)) = - quadraticChar F a := by
  have h2F : (2 : F) ≠ 0 := by
    intro hz
    exact (Ring.neg_one_ne_one_of_char_ne_two h2) (by linear_combination -hz)
  have h4F : (4 : F) ≠ 0 := by
    intro hz
    have h22 : (2 : F) * 2 = 0 := by linear_combination hz
    exact h2F (mul_self_eq_zero.mp h22)
  have h4a : (4 * a : F) ≠ 0 := mul_ne_zero h4F ha
  have hcs : ∀ x : F,
      a * x ^ 2 + b * x + c = a * (x + b / (2 * a)) ^ 2 + (c - b ^ 2 / (4 * a)) := by
    intro x; field_simp [ha]; ring
  have hre : (∑ x : F, quadraticChar F (a * x ^ 2 + b * x + c))
      = ∑ x : F, quadraticChar F (a * x ^ 2 + (c - b ^ 2 / (4 * a))) := by
    calc (∑ x : F, quadraticChar F (a * x ^ 2 + b * x + c))
        = ∑ x : F, quadraticChar F
            (a * (x + b / (2 * a)) ^ 2 + (c - b ^ 2 / (4 * a))) :=
          Finset.sum_congr rfl (fun x _ => by rw [hcs x])
      _ = ∑ x : F, quadraticChar F (a * x ^ 2 + (c - b ^ 2 / (4 * a))) :=
          Fintype.sum_equiv (Equiv.addRight (b / (2 * a))) _ _ (fun _ => rfl)
  have hD : c - b ^ 2 / (4 * a) ≠ 0 := by
    intro h
    have hc : b ^ 2 / (4 * a) = c := (sub_eq_zero.mp h).symm
    have hbc : b ^ 2 = c * (4 * a) := (div_eq_iff h4a).mp hc
    exact hdisc (by linear_combination hbc)
  have hfac : ∀ x : F,
      a * x ^ 2 + (c - b ^ 2 / (4 * a))
        = a * (x ^ 2 - (-(c - b ^ 2 / (4 * a)) / a)) := by
    intro x; field_simp [ha]; ring
  have hsplit : (∑ x : F, quadraticChar F (a * x ^ 2 + (c - b ^ 2 / (4 * a))))
      = quadraticChar F a
          * ∑ x : F, quadraticChar F (x ^ 2 - (-(c - b ^ 2 / (4 * a)) / a)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun x _ => by rw [hfac x, quadraticChar_mul])
  have hNne : (-(c - b ^ 2 / (4 * a)) / a) ≠ 0 := div_ne_zero (neg_ne_zero.mpr hD) ha
  rw [hre, hsplit, qr_quadratic_character_sum h2 _ hNne]
  ring

/-- **Hensel square-lift modulo powers of two.** If `a ≡ 1 (mod 8)` then `a`
is a square in `ZMod (2^n)`, for every `n`. -/
theorem isSquare_zmod_two_pow_of_mod_eight {n : ℕ} {a : ℤ} (ha : a % 8 = 1) :
    IsSquare (a : ZMod (2 ^ n)) := by
  have hc : a ≡ 1 [ZMOD 8] := by show a % 8 = 1 % 8; rw [ha]
  obtain ⟨y, hy⟩ := isSquare_mod_two_pow_of_one_mod_eight a hc n
  refine ⟨(y : ZMod (2 ^ n)), ?_⟩
  have hmod : a ≡ y ^ 2 [ZMOD ((2 ^ n : ℕ) : ℤ)] := by push_cast; exact hy.symm
  have hcast : ((a : ℤ) : ZMod (2 ^ n)) = ((y ^ 2 : ℤ) : ZMod (2 ^ n)) :=
    (ZMod.intCast_eq_intCast_iff _ _ _).mpr hmod
  push_cast at hcast
  rw [hcast]; ring

end DyadicShells.Upstream
