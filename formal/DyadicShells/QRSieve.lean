import Mathlib

/-!
# Quadratic-residue sieve: factorization identity and soundness

Source: Khachatryan v11.0.3, Proposition 4.1, and v11.5.17.

We prove the exact algebraic equivalence underlying sieve certificates
and that any exact-square witness passes a finite-field square sieve.

**Not yet proved here**: for odd prime ℓ and ℓ ∤ N the exact count
  # {A : ZMod ℓ | IsSquare (A² - N)} = (ℓ + χℓ(N)) / 2.
This requires a finite-field cardinality proof; see THEOREM_MAPPING.md.
-/

namespace DyadicShells

theorem square_test_iff_factor_pair
    {R : Type*} [CommRing R] (A y N : R) :
    A ^ 2 - N = y ^ 2 ↔ (A - y) * (A + y) = N := by
  constructor
  · intro h
    calc
      (A - y) * (A + y) = A ^ 2 - y ^ 2 := by ring
      _ = N := by linear_combination h
  · intro h
    have h' : A ^ 2 - y ^ 2 = N := by
      calc
        A ^ 2 - y ^ 2 = (A - y) * (A + y) := by ring
        _ = N := h
    linear_combination h'

noncomputable def passingCenters
    (F : Type*) [CommRing F] [Fintype F] [DecidableEq F] (N : F) :
    Finset F := by
  classical
  exact Finset.univ.filter (fun A => IsSquare (A ^ 2 - N))

theorem exact_square_witness_passes
    {F : Type*} [CommRing F] [Fintype F] [DecidableEq F]
    (A y N : F) (h : A ^ 2 - N = y ^ 2) :
    A ∈ passingCenters F N := by
  classical
  simp only [passingCenters, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨y, by simpa [pow_two] using h⟩

/-!
## Target 2: exact finite-field counts

The exact pass count is **not** proved yet. The next lemmas build its
two independent counting ingredients: the zero-center count (via
`quadraticChar_card_sqrts`) and a bijection between
`A²-y²=N` solution pairs and the nonzero elements of a field.
-/

open Finset

/-- Pairs of field elements with a prescribed difference of squares. -/
def qrPairs (F : Type*) [Field F] (N : F) :=
  {v : F × F // v.1 ^ 2 - v.2 ^ 2 = N}

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
          u.1 * (N / u.1) := by field_simp [h2, u.2] <;> ring
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
      field_simp [h2] <;> ring
    · dsimp
      rw [hv]
      field_simp [h2] <;> ring
  right_inv u := by
    apply Subtype.ext
    dsimp
    field_simp [h2, u.2] <;> ring

/-- The number of centers A with A²=N, cast to the integers, is
1 + the quadratic character of N. -/
theorem qr_zero_center_count
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (h2 : ringChar F ≠ 2) (N : F) :
    (({A : F | A ^ 2 = N}.toFinset.card : ℤ)) =
      quadraticChar F N + 1 := by
  classical
  exact quadraticChar_card_sqrts h2 N

end DyadicShells
