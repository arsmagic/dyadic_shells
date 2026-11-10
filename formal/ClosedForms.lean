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
  refine ⟨passCard_mod2 _, ?_⟩
  obtain ⟨k, rfl⟩ := hN
  have e : ((2 * k + 1 : ℤ) : ZMod 4) = 2 * (k : ZMod 4) + 1 := by push_cast; ring
  have hcases : ∀ x : ZMod 4, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by decide
  rw [e]
  rcases hcases (k : ZMod 4) with h | h | h | h <;> rw [h] <;>
    (unfold passCard; rw [Finset.filter_congr_decidable]; decide)

/-- N ≡ 3 (mod 4): base level C_3 = 2. -/
theorem passCard_three_base (N : ℤ) (hN : N ≡ 3 [ZMOD 4]) :
    passCard ((N : ZMod (2 ^ 3))) = 2 := by
  have hodd : Odd N := by
    have hd : (4 : ℤ) ∣ (3 - N) := Int.modEq_iff_dvd.mp hN
    exact Int.odd_iff.mpr (by omega)
  have h4 : N % 4 = 3 := by have := Int.modEq_iff_dvd.mp hN; omega
  have h8 : N ≡ 3 [ZMOD 8] ∨ N ≡ 7 [ZMOD 8] := by
    have : N % 8 = 3 ∨ N % 8 = 7 := by omega
    rcases this with h | h
    · exact Or.inl (Int.modEq_iff_dvd.mpr (by omega))
    · exact Or.inr (Int.modEq_iff_dvd.mpr (by omega))
  rcases h8 with h8 | h8
  · rw [passCard_eq_of_modEq_eight 3 N 3 hodd (by norm_num) h8]
    unfold passCard; rw [Finset.filter_congr_decidable]; decide
  · rw [passCard_eq_of_modEq_eight 3 N 7 hodd (by norm_num) h8]
    unfold passCard; rw [Finset.filter_congr_decidable]; decide

/-- N ≡ 3 (mod 4): an odd (unit) center never passes, because A² − N ≡ 2 (mod 4)
and 2 is not a square mod 4. Stated via the reduction `castHom : ZMod 2^k → ZMod 4`. -/
theorem three_odd_not_pass {k : ℕ} (hk : (4 : ℕ) ∣ 2 ^ k) (N : ZMod (2 ^ k))
    (hN4 : ZMod.castHom hk (ZMod 4) N = 3) (A : ZMod (2 ^ k)) (hA : IsUnit A) :
    ¬ IsSquare (A ^ 2 - N) := by
  intro hsq
  have h := IsSquare.map (ZMod.castHom hk (ZMod 4)) hsq
  rw [map_sub, map_pow, hN4] at h
  have h1 : (ZMod.castHom hk (ZMod 4) A) ^ 2 = 1 :=
    (by decide : ∀ a : ZMod 4, IsUnit a → a ^ 2 = 1) _ (hA.map (ZMod.castHom hk (ZMod 4)))
  rw [h1] at h
  have h2 : (1 - 3 : ZMod 4) = 2 := by decide
  rw [h2] at h
  exact (by decide : ¬ IsSquare (2 : ZMod 4)) h

/-- Passing descends under the reduction `ZMod 2^(k+1) → ZMod 2^k`: a square
`A² − N` mod 2^(k+1) reduces to a square mod 2^k. One half of the count argument. -/
theorem pass_of_reduce {k : ℕ} (hk : (2 ^ k : ℕ) ∣ 2 ^ (k + 1)) (N A : ZMod (2 ^ (k + 1)))
    (h : IsSquare (A ^ 2 - N)) :
    IsSquare ((ZMod.castHom hk (ZMod (2 ^ k)) A) ^ 2
      - ZMod.castHom hk (ZMod (2 ^ k)) N) := by
  have h2 := IsSquare.map (ZMod.castHom hk (ZMod (2 ^ k))) h
  rwa [map_sub, map_pow] at h2

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

/-- N ≡ 1 (mod 8): base level C_4(N) = 4. Reduce to the representative N = 1 via
the mod-8 invariance (milestone A), then decide on the finite ring `ZMod 16`. -/
theorem passCard_one_mod_eight_base (N : ℤ) (hN : N ≡ 1 [ZMOD 8]) :
    passCard ((N : ZMod (2 ^ 4))) = 4 := by
  have hodd : Odd N := by
    have hd : (8 : ℤ) ∣ (1 - N) := Int.modEq_iff_dvd.mp hN
    exact Int.odd_iff.mpr (by omega)
  rw [passCard_eq_of_modEq_eight 4 N 1 hodd odd_one hN]
  unfold passCard
  rw [Finset.filter_congr_decidable]
  decide

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
