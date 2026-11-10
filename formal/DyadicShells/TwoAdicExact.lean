import Mathlib
import DyadicShells.TwoAdicSaturation

/-!
# Exact two-adic pass counts: reduction to `N mod 8` (Target 4, milestone A)

For a modulus `n` and `N : ZMod n`, let `passCard N` be the number of residues
`A : ZMod n` such that `A ^ 2 - N` is a square in `ZMod n`. For `n = 2 ^ m` and
an odd integer `N`, `passCard N / 2 ^ m` is the two-adic pass proportion
`π_m(N)` of the series (Proposition 4.2).

This file proves the structural reduction behind the exact two-adic count:

* `passCard_unit_sq_mul`: multiplying `N` by the square of a unit does not change
  the count (the map `A ↦ u⁻¹ • A` is a bijection between the pass sets);
* `passCard_eq_of_modEq_eight`: for odd integers `N ≡ N' (mod 8)` the counts
  modulo `2 ^ m` coincide, for every `m`.

Consequently `π_m(N)` depends only on `N mod 8`, so the exact count for all odd
`N` reduces to the four representatives `N = 1, 3, 5, 7`. The closed forms for
those representatives (manuscript, Theorem 1) are milestone B.
-/

namespace DyadicShells

section General

variable {n : ℕ} [NeZero n]

open Classical in
/-- The number of residues `A` modulo `n` such that `A ^ 2 - N` is a square
modulo `n`. -/
noncomputable def passCard (N : ZMod n) : ℕ :=
  (Finset.univ.filter fun A : ZMod n => IsSquare (A ^ 2 - N)).card

/-- Scaling by the square of a unit preserves squareness. -/
theorem isSquare_unit_sq_mul_iff {R : Type*} [CommRing R] (u : Rˣ) (x : R) :
    IsSquare ((u : R) ^ 2 * x) ↔ IsSquare x := by
  constructor
  · rintro ⟨r, hr⟩
    refine ⟨(↑u⁻¹ : R) * r, ?_⟩
    have h1 : (↑u⁻¹ : R) * u = 1 := Units.inv_mul u
    linear_combination (↑u⁻¹ : R) ^ 2 * hr - x * ((↑u⁻¹ : R) * u + 1) * h1
  · rintro ⟨r, hr⟩
    exact ⟨(u : R) * r, by rw [hr]; ring⟩

/-- **Unit-square invariance.** The pass count of `u ^ 2 * N` equals that of
`N` for every unit `u`. -/
theorem passCard_unit_sq_mul (u : (ZMod n)ˣ) (N : ZMod n) :
    passCard ((u : ZMod n) ^ 2 * N) = passCard N := by
  classical
  unfold passCard
  have h1 : (↑u⁻¹ : ZMod n) * u = 1 := Units.inv_mul u
  refine Finset.card_bij' (fun A _ => (↑u⁻¹ : ZMod n) * A) (fun A _ => (u : ZMod n) * A)
    ?_ ?_ ?_ ?_
  · intro A hA
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hA ⊢
    have heq : ((↑u⁻¹ : ZMod n) * A) ^ 2 - N
        = (↑u⁻¹ : ZMod n) ^ 2 * (A ^ 2 - (u : ZMod n) ^ 2 * N) := by
      linear_combination (N * ((↑u⁻¹ : ZMod n) * u + 1)) * h1
    rw [heq]
    exact (isSquare_unit_sq_mul_iff u⁻¹ _).mpr hA
  · intro A hA
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hA ⊢
    have heq : ((u : ZMod n) * A) ^ 2 - (u : ZMod n) ^ 2 * N
        = (u : ZMod n) ^ 2 * (A ^ 2 - N) := by ring
    rw [heq]
    exact (isSquare_unit_sq_mul_iff u _).mpr hA
  · intro A _
    show (u : ZMod n) * ((↑u⁻¹ : ZMod n) * A) = A
    rw [← mul_assoc, Units.mul_inv, one_mul]
  · intro A _
    show (↑u⁻¹ : ZMod n) * ((u : ZMod n) * A) = A
    rw [← mul_assoc, h1, one_mul]

end General

/-- An odd integer is invertible modulo `2 ^ m`, with an integer inverse. -/
theorem exists_inv_of_odd (m : ℕ) (x : ℤ) (hx : Odd x) :
    ∃ a : ℤ, (a : ZMod (2 ^ m)) * (x : ZMod (2 ^ m)) = 1 := by
  obtain ⟨j, rfl⟩ := hx
  have h2 : IsCoprime (2 * j + 1) (2 : ℤ) := ⟨1, -j, by ring⟩
  obtain ⟨a, b, hab⟩ := h2.pow_right (n := m)
  refine ⟨a, ?_⟩
  have h0 : (2 : ZMod (2 ^ m)) ^ m = 0 := by
    exact_mod_cast ZMod.natCast_self (2 ^ m)
  have hc := congrArg (fun z : ℤ => (z : ZMod (2 ^ m))) hab
  push_cast at hc ⊢
  rw [h0, mul_zero, add_zero] at hc
  exact hc

/-- **Reduction to `N mod 8`.** For odd integers `N ≡ N' (mod 8)`, the two-adic
pass counts modulo `2 ^ m` coincide, for every `m`. -/
theorem passCard_eq_of_modEq_eight (m : ℕ) [NeZero (2 ^ m)] (N N' : ℤ)
    (hN : Odd N) (hN' : Odd N') (h8 : N ≡ N' [ZMOD 8]) :
    passCard ((N : ℤ) : ZMod (2 ^ m)) = passCard ((N' : ℤ) : ZMod (2 ^ m)) := by
  have hN'sq : N' * N' ≡ 1 [ZMOD 8] := by
    rw [← sq]; exact odd_sq_modEq_one_eight N' hN'
  have hc : N * N' ≡ 1 [ZMOD 8] := (h8.mul_right N').trans hN'sq
  obtain ⟨y, hy⟩ := isSquare_mod_two_pow_of_one_mod_eight (N * N') hc m
  obtain ⟨a, ha⟩ := exists_inv_of_odd m N' hN'
  obtain ⟨b, hb⟩ := exists_inv_of_odd m N hN
  have hyZ : (y : ZMod (2 ^ m)) ^ 2 = (N : ZMod (2 ^ m)) * (N' : ZMod (2 ^ m)) := by
    have h := (ZMod.intCast_eq_intCast_iff (y ^ 2) (N * N') (2 ^ m)).mpr
      (by exact_mod_cast hy)
    push_cast at h
    exact h
  have hkey : ((y : ZMod (2 ^ m)) * (a : ZMod (2 ^ m))) ^ 2 * (N' : ZMod (2 ^ m))
      = (N : ZMod (2 ^ m)) := by
    have hexp : ((y : ZMod (2 ^ m)) * (a : ZMod (2 ^ m))) ^ 2 * (N' : ZMod (2 ^ m))
        = (y : ZMod (2 ^ m)) ^ 2 * ((a : ZMod (2 ^ m)) * (N' : ZMod (2 ^ m)))
          * (a : ZMod (2 ^ m)) := by ring
    rw [hexp, hyZ]
    linear_combination
      (N : ZMod (2 ^ m)) * ((a : ZMod (2 ^ m)) * (N' : ZMod (2 ^ m)) + 1) * ha
  have hNunit : IsUnit (N : ZMod (2 ^ m)) :=
    (Units.mkOfMulEqOne (N : ZMod (2 ^ m)) (b : ZMod (2 ^ m))
      (by rw [mul_comm]; exact hb)).isUnit
  have huunit : IsUnit ((y : ZMod (2 ^ m)) * (a : ZMod (2 ^ m))) := by
    have hprod : IsUnit (((y : ZMod (2 ^ m)) * (a : ZMod (2 ^ m))) *
        (((y : ZMod (2 ^ m)) * (a : ZMod (2 ^ m))) * (N' : ZMod (2 ^ m)))) := by
      rw [← mul_assoc, ← sq, hkey]; exact hNunit
    exact isUnit_of_mul_isUnit_left hprod
  calc passCard ((N : ℤ) : ZMod (2 ^ m))
      = passCard (((huunit.unit : (ZMod (2 ^ m))ˣ) : ZMod (2 ^ m)) ^ 2
          * (N' : ZMod (2 ^ m))) := by rw [IsUnit.unit_spec, hkey]
    _ = passCard ((N' : ℤ) : ZMod (2 ^ m)) := passCard_unit_sq_mul _ _

end DyadicShells
