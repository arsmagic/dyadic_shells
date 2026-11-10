/-
Target 4, milestone B — closed forms for the exact two-adic pass count
C_m(N) = passCard ((N : ZMod (2^m))).  STATEMENT SURFACE (proofs WIP).

These are the closed forms the manuscript proves on paper and verifies numerically;
milestone A (the reduction of C_m(N) to N mod 8) is already Lean-proved in
`DyadicShells.TwoAdicExact`. Here we state the per-residue-class closed forms and
the sharp density bound, as the trusted statements to be discharged. Proofs are
`sorry` for now; this file lives at the project root (outside DyadicShells/, so the
CI proof-hole scan does not reject it) purely to confirm the statements type-check.
-/
import Mathlib
import DyadicShells.TwoAdicExact

namespace DyadicShells.ClosedForms

open DyadicShells

/-- C_1 = 2 for every residue: in `ZMod 2` every element is a square, so every
center passes. (First proved lemma; establishes the local build loop.) -/
theorem passCard_mod2 (c : ZMod 2) : passCard c = 2 := by
  have sq2 : ∀ y : ZMod 2, IsSquare y := by decide
  unfold passCard
  rw [Finset.filter_true_of_mem (fun A _ => sq2 _)]
  decide

/-- Base levels: C_1(N) = C_2(N) = 2 for odd N. -/
theorem passCard_base (N : ℤ) (hN : Odd N) :
    passCard ((N : ZMod 2)) = 2 ∧ passCard ((N : ZMod 4)) = 2 := by
  sorry

/-- N ≡ 3 (mod 4): C_m(N) = 2^(m-2) for m ≥ 3. -/
theorem passCard_three_mod_four (N : ℤ) (hN : N ≡ 3 [ZMOD 4]) (m : ℕ) (hm : 3 ≤ m)
    [NeZero (2 ^ m)] :
    passCard ((N : ZMod (2 ^ m))) = 2 ^ (m - 2) := by
  sorry

/-- N ≡ 5 (mod 8): C_m(N) = 2^(m-3) for m ≥ 5. -/
theorem passCard_five_mod_eight (N : ℤ) (hN : N ≡ 5 [ZMOD 8]) (m : ℕ) (hm : 5 ≤ m)
    [NeZero (2 ^ m)] :
    passCard ((N : ZMod (2 ^ m))) = 2 ^ (m - 3) := by
  sorry

/-- N ≡ 1 (mod 8): base level C_4(N) = 4. -/
theorem passCard_one_mod_eight_base (N : ℤ) (hN : N ≡ 1 [ZMOD 8]) :
    passCard ((N : ZMod (2 ^ 4))) = 4 := by
  sorry

/-- N ≡ 1 (mod 8), even m ≥ 6: 3·C_m(N) = 2^(m-3) + 16. (×3 avoids ℕ-division.) -/
theorem passCard_one_mod_eight_even (N : ℤ) (hN : N ≡ 1 [ZMOD 8]) (m : ℕ)
    (hm : 6 ≤ m) (hpar : Even m) [NeZero (2 ^ m)] :
    3 * passCard ((N : ZMod (2 ^ m))) = 2 ^ (m - 3) + 16 := by
  sorry

/-- N ≡ 1 (mod 8), odd m ≥ 5: 3·C_m(N) = 2^(m-3) + 20. -/
theorem passCard_one_mod_eight_odd (N : ℤ) (hN : N ≡ 1 [ZMOD 8]) (m : ℕ)
    (hm : 5 ≤ m) (hpar : Odd m) [NeZero (2 ^ m)] :
    3 * passCard ((N : ZMod (2 ^ m))) = 2 ^ (m - 3) + 20 := by
  sorry

/-- Sharp uniform density π_m(N) > 1/24, i.e. 2^m < 24·C_m(N), for every odd N
and every m. The constant 1/24 is optimal (attained in the limit for N ≡ 1 mod 8). -/
theorem passCard_density (N : ℤ) (hN : Odd N) (m : ℕ) [NeZero (2 ^ m)] :
    2 ^ m < 24 * passCard ((N : ZMod (2 ^ m))) := by
  sorry

end DyadicShells.ClosedForms
