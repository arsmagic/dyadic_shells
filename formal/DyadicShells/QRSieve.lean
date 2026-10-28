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

/-- Reindex the equation A²-y²=N by its first coordinate. -/
def qrPairsEquivSigma
    {F : Type*} [Field F] (N : F) :
    qrPairs F N ≃ (Σ A : F, {y : F // y ^ 2 = A ^ 2 - N}) where
  toFun v := ⟨v.1.1, ⟨v.1.2, by linear_combination -v.2⟩⟩
  invFun v := ⟨(v.1, v.2.1), by linear_combination -v.2.2⟩
  left_inv v := rfl
  right_inv v := rfl

/-- Summing the root-count formula over the centers. -/
theorem qrPairs_count_as_character_sum
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

/-- The precise character sum behind the sieve's null model:
for every nonzero N in a finite field of odd characteristic,
∑ A, χ(A²-N) = -1. -/
theorem qr_quadratic_character_sum
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
    simpa using (Fintype.card_subtype_compl (fun u : F => u = 0))
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

end DyadicShells
