import Mathlib

/-!
# PR 1 (self-contained): quadratic character sum over a quadratic polynomial

Standalone — depends on **Mathlib only**. This is the submission-ready content
for `leanprover-community/mathlib4`:
`∑ x, quadraticChar F (a x² + b x + c) = - quadraticChar F a` for a finite field
of odd characteristic, `a ≠ 0`, discriminant `b² - 4 a c ≠ 0`.

The `qrPairs…` helpers build the base identity `∑ x, χ(x² - N) = -1`; in the PR
they become `private`. The namespace `DyadicShells.PR1Standalone` only avoids a
name clash with the project files while validating in this repo — strip it (and
`private`-ize the helpers) for the Mathlib PR. Target file:
`Mathlib/NumberTheory/LegendreSymbol/QuadraticChar/GaussSum.lean`.
-/

namespace DyadicShells.PR1Standalone
open Finset

/-- Pairs of field elements with a prescribed difference of squares. -/
def qrPairs (F : Type*) [Field F] (N : F) :=
  {v : F × F // v.1 ^ 2 - v.2 ^ 2 = N}

noncomputable instance qrPairsFintype
    {F : Type*} [Field F] [Fintype F] (N : F) :
    Fintype (qrPairs F N) := by
  classical
  change Fintype {v : F × F // v.1 ^ 2 - v.2 ^ 2 = N}
  infer_instance

private theorem qrPairs_mul
    {F : Type*} [Field F] (N : F) (v : qrPairs F N) :
    (v.1.1 - v.1.2) * (v.1.1 + v.1.2) = N := by
  calc
    (v.1.1 - v.1.2) * (v.1.1 + v.1.2) =
        v.1.1 ^ 2 - v.1.2 ^ 2 := by ring
    _ = N := v.2

private theorem qrPairs_sub_ne_zero
    {F : Type*} [Field F] (N : F) (hN : N ≠ 0)
    (v : qrPairs F N) : v.1.1 - v.1.2 ≠ 0 := by
  intro hz
  have hm := qrPairs_mul N v
  rw [hz, zero_mul] at hm
  exact hN hm.symm

/-- Parametrization of the difference-of-squares conic for nonzero N. -/
noncomputable def qrPairsEquivNonzero
    {F : Type*} [Field F]
    (N : F) (hN : N ≠ 0) (h2 : (2 : F) ≠ 0) :
    qrPairs F N ≃ {u : F // u ≠ 0} where
  toFun v := ⟨v.1.1 - v.1.2, qrPairs_sub_ne_zero N hN v⟩
  invFun u := ⟨((u.1 + N / u.1) / 2, (N / u.1 - u.1) / 2), by
    have hm : u.1 * (N / u.1) = N := by field_simp [u.2]
    dsimp
    calc
      ((u.1 + N / u.1) / 2) ^ 2 - ((N / u.1 - u.1) / 2) ^ 2 =
          u.1 * (N / u.1) := by field_simp [h2, u.2]; ring
      _ = N := hm⟩
  left_inv v := by
    have hu := qrPairs_sub_ne_zero N hN v
    have hprod := qrPairs_mul N v
    have hv : N / (v.1.1 - v.1.2) = v.1.1 + v.1.2 := by
      apply (div_eq_iff hu).2
      simpa [mul_comm] using hprod.symm
    apply Subtype.ext
    apply Prod.ext
    · dsimp
      rw [hv]
      field_simp [h2]; ring
    · dsimp
      rw [hv]
      field_simp [h2]; ring
  right_inv u := by
    apply Subtype.ext
    dsimp
    field_simp [h2, u.2]; ring

/-- Reindex the equation A²-y²=N by its first coordinate. -/
def qrPairsEquivSigma
    {F : Type*} [Field F] (N : F) :
    qrPairs F N ≃ (Σ A : F, {y : F // y ^ 2 = A ^ 2 - N}) where
  toFun v := ⟨v.1.1, ⟨v.1.2, by linear_combination -v.2⟩⟩
  invFun v := ⟨(v.1, v.2.1), by linear_combination -v.2.2⟩
  left_inv v := rfl
  right_inv v := rfl

/-- Summing the root-count formula over the centers. -/
private theorem qrPairs_count_as_character_sum
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (h2 : ringChar F ≠ 2) (N : F) :
    (Fintype.card (qrPairs F N) : ℤ) =
      ∑ A : F, (quadraticChar F (A ^ 2 - N) + 1) := by
  classical
  have hc : Fintype.card (qrPairs F N) =
      ∑ A : F, Fintype.card {y : F // y ^ 2 = A ^ 2 - N} := by
    rw [Fintype.card_congr (qrPairsEquivSigma N), Fintype.card_sigma]
  calc
    (Fintype.card (qrPairs F N) : ℤ) =
        ∑ A : F, (Fintype.card {y : F // y ^ 2 = A ^ 2 - N} : ℤ) := by
          exact_mod_cast hc
    _ = ∑ A : F, (quadraticChar F (A ^ 2 - N) + 1) := by
      apply Finset.sum_congr rfl
      intro A _
      simpa [Fintype.card_subtype, Set.toFinset_setOf] using
        (quadraticChar_card_sqrts h2 (A ^ 2 - N))

/-- Base identity: for nonzero `N` in a finite field of odd characteristic,
`∑ A, quadraticChar F (A² - N) = -1`. -/
theorem quadraticChar_sum_sq_sub
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (h2 : ringChar F ≠ 2) (N : F) (hN : N ≠ 0) :
    (∑ A : F, quadraticChar F (A ^ 2 - N)) = -1 := by
  classical
  have htwo : (2 : F) ≠ 0 := by
    intro hz
    have hne := Ring.neg_one_ne_one_of_char_ne_two h2
    apply hne
    calc
      (-1 : F) = 1 - 2 := by ring
      _ = 1 := by rw [hz]; ring
  have hpair : Fintype.card (qrPairs F N) =
      Fintype.card {u : F // u ≠ 0} :=
    Fintype.card_congr (qrPairsEquivNonzero N hN htwo)
  have hcomplement :
      Fintype.card {u : F // u ≠ 0} = Fintype.card F - 1 := by
    simp
  have hfieldNonempty : 0 < Fintype.card F :=
    Fintype.card_pos_iff.mpr ⟨(0 : F)⟩
  have hcard : (Fintype.card (qrPairs F N) : ℤ) =
      (Fintype.card F : ℤ) - 1 := by
    omega
  have hroots := qrPairs_count_as_character_sum h2 N
  have hexpand :
      (∑ A : F, (quadraticChar F (A ^ 2 - N) + 1)) =
        (∑ A : F, quadraticChar F (A ^ 2 - N)) +
        (Fintype.card F : ℤ) := by
    simp [Finset.sum_add_distrib]
  omega

/-- **Quadratic character sum over a quadratic polynomial.** For a finite field
`F` of odd characteristic, if `a ≠ 0` and the discriminant `b² - 4 a c ≠ 0`,
then `∑ x, quadraticChar F (a x² + b x + c) = - quadraticChar F a`. -/
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
    exact Finset.sum_congr rfl (fun x _ => by rw [hfac x, map_mul])
  have hNne : (-(c - b ^ 2 / (4 * a)) / a) ≠ 0 := div_ne_zero (neg_ne_zero.mpr hD) ha
  rw [hre, hsplit, quadraticChar_sum_sq_sub h2 _ hNne]
  ring

end DyadicShells.PR1Standalone
