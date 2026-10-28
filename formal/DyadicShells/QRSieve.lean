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

end DyadicShells
