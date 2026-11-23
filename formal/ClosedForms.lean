/-
Target 4, milestone B — closed forms for the exact two-adic pass count
C_m(N) = passCard ((N : ZMod (2^m))).  FULLY MACHINE-CHECKED (no sorry).

These are the closed forms the manuscript proves on paper and verifies numerically;
milestone A (the reduction of C_m(N) to N mod 8) is already Lean-proved in
`DyadicShells.TwoAdicExact`. Here we state the per-residue-class closed forms and
the sharp density bound.  All proofs are complete and depend only on the standard
axioms [propext, Classical.choice, Quot.sound] (no sorry / sorryAx).  This file
lives at the project root (outside DyadicShells/).
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

/-- The two preimages of a center under `ZMod 2^(k+1) → ZMod 2^k` give the SAME
value of `(·)² − N`: `(A + 2^k)² = A²` in `ZMod 2^(k+1)` (for k ≥ 1), since
`2^(k+1) = 0` and `2^(2k) = 0`. This is why passing doubles cleanly. -/
theorem lift_sq_eq {k : ℕ} (hk : 1 ≤ k) (A : ZMod (2 ^ (k + 1))) :
    (A + (2 : ZMod (2 ^ (k + 1))) ^ k) ^ 2 = A ^ 2 := by
  have hz : (2 : ZMod (2 ^ (k + 1))) ^ (k + 1) = 0 := by
    have h := ZMod.natCast_self (2 ^ (k + 1))
    push_cast at h
    simpa using h
  have hz2 : (2 : ZMod (2 ^ (k + 1))) ^ (2 * k) = 0 := by
    have e : (2 : ZMod (2 ^ (k + 1))) ^ (2 * k)
        = (2 : ZMod (2 ^ (k + 1))) ^ (k + 1)
          * (2 : ZMod (2 ^ (k + 1))) ^ (2 * k - (k + 1)) := by
      rw [← pow_add]; congr 1; omega
    rw [e, hz, zero_mul]
  linear_combination A * hz + hz2

/-- Characterization for `N ≡ 3 (mod 4)`, level `k ≥ 3`: a center `A` passes iff
the value `A² − N` is `≡ 1 (mod 8)`.  Forward: push to `ZMod 8` and `decide`
(the only odd square mod 8 is 1, and `N mod 8 ∈ {3,7}`).  Backward: the
1-mod-8 lifting lemma. -/
theorem pass_char_three {k : ℕ} (h8 : (8 : ℕ) ∣ 2 ^ k) (N : ℤ) (hN : N ≡ 3 [ZMOD 4])
    (A : ZMod (2 ^ k)) :
    IsSquare (A ^ 2 - ((N : ℤ) : ZMod (2 ^ k)))
      ↔ ZMod.castHom h8 (ZMod 8) (A ^ 2 - ((N : ℤ) : ZMod (2 ^ k))) = 1 := by
  have hN8 : ZMod.castHom h8 (ZMod 8) ((N : ℤ) : ZMod (2 ^ k)) = 3
          ∨ ZMod.castHom h8 (ZMod 8) ((N : ℤ) : ZMod (2 ^ k)) = 7 := by
    rw [map_intCast]
    have hd : (4 : ℤ) ∣ (3 - N) := Int.modEq_iff_dvd.mp hN
    have h8' : N % 8 = 3 ∨ N % 8 = 7 := by omega
    rcases h8' with h | h
    · left
      have hmod : N ≡ 3 [ZMOD 8] := Int.modEq_iff_dvd.mpr (by omega)
      have := (ZMod.intCast_eq_intCast_iff N 3 8).mpr hmod
      simpa using this
    · right
      have hmod : N ≡ 7 [ZMOD 8] := Int.modEq_iff_dvd.mpr (by omega)
      have := (ZMod.intCast_eq_intCast_iff N 7 8).mpr hmod
      simpa using this
  constructor
  · intro hsq
    have hmap := IsSquare.map (ZMod.castHom h8 (ZMod 8)) hsq
    rw [map_sub, map_pow] at hmap
    rw [map_sub, map_pow]
    have key : ∀ a b : ZMod 8, (b = 3 ∨ b = 7) → IsSquare (a ^ 2 - b) → a ^ 2 - b = 1 := by
      decide
    exact key _ _ hN8 hmap
  · intro h
    set c : ℤ := (A.val : ℤ) ^ 2 - N with hc_def
    have hcast : ((c : ℤ) : ZMod (2 ^ k)) = A ^ 2 - ((N : ℤ) : ZMod (2 ^ k)) := by
      rw [hc_def]; push_cast; rw [ZMod.natCast_zmod_val]
    have hc1 : ((c : ℤ) : ZMod 8) = 1 := by
      have hh := h
      rw [← hcast, map_intCast] at hh
      exact hh
    have hcmod : c ≡ 1 [ZMOD 8] := by
      have : ((c : ℤ) : ZMod 8) = ((1 : ℤ) : ZMod 8) := by rw [hc1]; norm_num
      exact (ZMod.intCast_eq_intCast_iff c 1 8).mp this
    obtain ⟨y, hy⟩ := isSquare_mod_two_pow_of_one_mod_eight c hcmod k
    have hy2 : ((y : ℤ) : ZMod (2 ^ k)) ^ 2 = ((c : ℤ) : ZMod (2 ^ k)) := by
      have h' := (ZMod.intCast_eq_intCast_iff (y ^ 2) c (2 ^ k)).mpr hy
      push_cast at h'; exact h'
    refine ⟨(y : ZMod (2 ^ k)), ?_⟩
    rw [← hcast, ← hy2]; ring

/-- The reduction `π : ZMod 2^(k+1) → ZMod 2^k` is 2-to-1: its fibre over any `b`
is exactly the pair `{b.val, b.val + 2^k}` lifted to `ZMod 2^(k+1)`.  (Pure;
independent of `N`.) -/
theorem castHom_fiber_pair {k : ℕ} (hdvd : (2 ^ k : ℕ) ∣ 2 ^ (k + 1))
    (b : ZMod (2 ^ k)) :
    (Finset.univ.filter
        (fun A : ZMod (2 ^ (k + 1)) => ZMod.castHom hdvd (ZMod (2 ^ k)) A = b))
      = {((b.val : ℕ) : ZMod (2 ^ (k + 1))),
         ((b.val : ℕ) : ZMod (2 ^ (k + 1))) + ((2 ^ k : ℕ) : ZMod (2 ^ (k + 1)))} := by
  have : NeZero (2 ^ (k + 1)) := ⟨pow_ne_zero _ two_ne_zero⟩
  have : NeZero (2 ^ k) := ⟨pow_ne_zero _ two_ne_zero⟩
  have hπ : ∀ A : ZMod (2 ^ (k + 1)),
      ZMod.castHom hdvd (ZMod (2 ^ k)) A = ((A.val : ℕ) : ZMod (2 ^ k)) := by
    intro A; rw [ZMod.castHom_apply]; exact (ZMod.natCast_val A).symm
  ext A
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
    Finset.mem_singleton]
  constructor
  · intro hA
    rw [hπ] at hA
    have h' : ((A.val : ℕ) : ZMod (2 ^ k)) = ((b.val : ℕ) : ZMod (2 ^ k)) := by
      rw [hA, ZMod.natCast_zmod_val]
    have hbk : b.val < 2 ^ k := ZMod.val_lt b
    have hbm : b.val % 2 ^ k = b.val := Nat.mod_eq_of_lt hbk
    have hmod : A.val % 2 ^ k = b.val := by
      rw [← hbm]; exact (ZMod.natCast_eq_natCast_iff' _ _ _).mp h'
    have hAlt : A.val < 2 ^ (k + 1) := ZMod.val_lt A
    have hdm : 2 ^ k * (A.val / 2 ^ k) + A.val % 2 ^ k = A.val :=
      Nat.div_add_mod A.val (2 ^ k)
    rw [hmod] at hdm
    have hql : 2 ^ k * (A.val / 2 ^ k) < 2 ^ k * 2 := by
      have h2 : 2 ^ (k + 1) = 2 ^ k * 2 := by rw [pow_succ]
      omega
    have hq2 : A.val / 2 ^ k < 2 := lt_of_mul_lt_mul_left hql (Nat.zero_le _)
    have hq01 : A.val / 2 ^ k = 0 ∨ A.val / 2 ^ k = 1 := by
      rcases h : A.val / 2 ^ k with _ | _ | n
      · exact Or.inl rfl
      · exact Or.inr rfl
      · rw [h] at hq2; omega
    have hcase : A.val = b.val ∨ A.val = b.val + 2 ^ k := by
      rcases hq01 with hq | hq
      · rw [hq, mul_zero, zero_add] at hdm; omega
      · rw [hq, mul_one] at hdm; omega
    have hAeq : A = ((A.val : ℕ) : ZMod (2 ^ (k + 1))) := (ZMod.natCast_zmod_val A).symm
    rcases hcase with h | h
    · left; rw [hAeq, h]
    · right; rw [hAeq, h, Nat.cast_add]
  · intro hA
    rcases hA with h | h
    · rw [h, map_natCast, ZMod.natCast_zmod_val]
    · rw [h, map_add, map_natCast, map_natCast, ZMod.natCast_zmod_val, ZMod.natCast_self,
        add_zero]

/-- Recursion `C_{k+1}(N) = 2·C_k(N)` for `N ≡ 3 (mod 4)`, `k ≥ 3`.  The reduction
`π : ZMod 2^(k+1) → ZMod 2^k` sends passers to passers, each fibre is a pair
(`castHom_fiber_pair`), and both members of a fibre over a passing centre pass
(characterization, since the mod-8 value is preserved). -/
theorem passCard_succ_three {k : ℕ} (hk : 3 ≤ k) (N : ℤ) (hN : N ≡ 3 [ZMOD 4]) :
    passCard ((N : ℤ) : ZMod (2 ^ (k + 1))) = 2 * passCard ((N : ℤ) : ZMod (2 ^ k)) := by
  have hdvd : (2 ^ k : ℕ) ∣ 2 ^ (k + 1) := pow_dvd_pow 2 (Nat.le_succ k)
  have h8k : (8 : ℕ) ∣ 2 ^ k :=
    ⟨2 ^ (k - 3), by rw [show (8 : ℕ) = 2 ^ 3 from rfl, ← pow_add]; congr 1; omega⟩
  have h8k1 : (8 : ℕ) ∣ 2 ^ (k + 1) :=
    ⟨2 ^ (k + 1 - 3), by rw [show (8 : ℕ) = 2 ^ 3 from rfl, ← pow_add]; congr 1; omega⟩
  have hmem : ∀ A : ZMod (2 ^ (k + 1)),
      IsSquare (A ^ 2 - ((N : ℤ) : ZMod (2 ^ (k + 1))))
        ↔ IsSquare ((ZMod.castHom hdvd (ZMod (2 ^ k)) A) ^ 2 - ((N : ℤ) : ZMod (2 ^ k))) := by
    intro A
    have hA8 : ZMod.castHom h8k1 (ZMod 8) A
             = ZMod.castHom h8k (ZMod 8) (ZMod.castHom hdvd (ZMod (2 ^ k)) A) := by
      rw [← RingHom.comp_apply, ZMod.castHom_comp]
    have hcc : ZMod.castHom h8k1 (ZMod 8) (A ^ 2 - ((N : ℤ) : ZMod (2 ^ (k + 1))))
             = ZMod.castHom h8k (ZMod 8)
                 ((ZMod.castHom hdvd (ZMod (2 ^ k)) A) ^ 2 - ((N : ℤ) : ZMod (2 ^ k))) := by
      simp only [map_sub, map_pow, map_intCast, hA8]
    rw [pass_char_three h8k1 N hN A,
        pass_char_three h8k N hN (ZMod.castHom hdvd (ZMod (2 ^ k)) A)]
    exact iff_of_eq (by rw [hcc])
  have Hf : ∀ A ∈ (Finset.univ.filter fun A : ZMod (2 ^ (k + 1)) =>
                IsSquare (A ^ 2 - ((N : ℤ) : ZMod (2 ^ (k + 1))))),
      ZMod.castHom hdvd (ZMod (2 ^ k)) A ∈
        (Finset.univ.filter fun b : ZMod (2 ^ k) =>
            IsSquare (b ^ 2 - ((N : ℤ) : ZMod (2 ^ k)))) := by
    intro A hA
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hA ⊢
    exact (hmem A).mp hA
  have hfib : ∀ b ∈ (Finset.univ.filter fun b : ZMod (2 ^ k) =>
                IsSquare (b ^ 2 - ((N : ℤ) : ZMod (2 ^ k)))),
      ((Finset.univ.filter fun A : ZMod (2 ^ (k + 1)) =>
          IsSquare (A ^ 2 - ((N : ℤ) : ZMod (2 ^ (k + 1))))).filter
        (fun A => ZMod.castHom hdvd (ZMod (2 ^ k)) A = b)).card = 2 := by
    intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    have hset : (Finset.univ.filter fun A : ZMod (2 ^ (k + 1)) =>
          IsSquare (A ^ 2 - ((N : ℤ) : ZMod (2 ^ (k + 1))))).filter
          (fun A => ZMod.castHom hdvd (ZMod (2 ^ k)) A = b)
        = Finset.univ.filter (fun A : ZMod (2 ^ (k + 1)) =>
            ZMod.castHom hdvd (ZMod (2 ^ k)) A = b) := by
      ext A
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨_, h2⟩; exact h2
      · intro hAb
        exact ⟨(hmem A).mpr (by rw [hAb]; exact hb), hAb⟩
    rw [hset, castHom_fiber_pair hdvd b]
    have hcne : ((2 ^ k : ℕ) : ZMod (2 ^ (k + 1))) ≠ 0 := by
      intro hd2
      rw [ZMod.natCast_eq_zero_iff] at hd2
      have hle := Nat.le_of_dvd (by positivity) hd2
      have he : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
      have hp : 0 < 2 ^ k := by positivity
      omega
    apply Finset.card_pair
    intro hcontra
    apply hcne
    have hz : ((b.val : ℕ) : ZMod (2 ^ (k + 1))) + ((2 ^ k : ℕ) : ZMod (2 ^ (k + 1)))
            = ((b.val : ℕ) : ZMod (2 ^ (k + 1))) + 0 := by
      rw [add_zero]; exact hcontra.symm
    exact add_left_cancel hz
  unfold passCard
  rw [Finset.filter_congr_decidable, Finset.filter_congr_decidable]
  rw [Finset.card_eq_sum_card_fiberwise Hf, Finset.sum_const_nat hfib, Nat.mul_comm]

open scoped Classical in
theorem lift_fibre_card {k : ℕ} (hk : 1 ≤ k) (N : ℤ) (b : ZMod (2 ^ k)) :
    ((Finset.univ.filter (fun A : ZMod (2 ^ (k + 1)) =>
          IsSquare (A ^ 2 - ((N : ℤ) : ZMod (2 ^ (k + 1)))))).filter
        (fun A => ZMod.castHom (pow_dvd_pow 2 (Nat.le_succ k)) (ZMod (2 ^ k)) A = b)).card
      = if IsSquare (((b.val : ℤ) : ZMod (2 ^ (k + 1))) ^ 2 - ((N : ℤ) : ZMod (2 ^ (k + 1))))
        then 2 else 0 := by
  classical
  set N' : ZMod (2 ^ (k + 1)) := ((N : ℤ) : ZMod (2 ^ (k + 1))) with hN'
  -- переставить фильтры: сначала слой (castHom = b), потом квадратичность
  have hcomm :
      ((Finset.univ.filter (fun A : ZMod (2 ^ (k + 1)) => IsSquare (A ^ 2 - N'))).filter
          (fun A => ZMod.castHom (pow_dvd_pow 2 (Nat.le_succ k)) (ZMod (2 ^ k)) A = b))
        = ((Finset.univ.filter (fun A : ZMod (2 ^ (k + 1)) =>
              ZMod.castHom (pow_dvd_pow 2 (Nat.le_succ k)) (ZMod (2 ^ k)) A = b)).filter
            (fun A => IsSquare (A ^ 2 - N'))) := by
    ext A
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact and_comm
  rw [hcomm, castHom_fiber_pair (pow_dvd_pow 2 (Nat.le_succ k)) b]
  set B0 : ZMod (2 ^ (k + 1)) := ((b.val : ℕ) : ZMod (2 ^ (k + 1))) with hB0
  set C : ZMod (2 ^ (k + 1)) := ((2 ^ k : ℕ) : ZMod (2 ^ (k + 1))) with hC
  -- оба элемента пары имеют значение V = (↑b.val)² − N'
  have hvalB0 : B0 ^ 2 - N' = ((b.val : ℤ) : ZMod (2 ^ (k + 1))) ^ 2 - N' := by
    simp only [hB0, Int.cast_natCast]
  have hCeq : C = (2 : ZMod (2 ^ (k + 1))) ^ k := by simp only [hC, Nat.cast_pow, Nat.cast_ofNat]
  have hvalBC : (B0 + C) ^ 2 - N' = ((b.val : ℤ) : ZMod (2 ^ (k + 1))) ^ 2 - N' := by
    rw [hCeq, lift_sq_eq hk B0]; exact hvalB0
  -- C ≠ 0, поэтому B0 ≠ B0 + C
  have hcne : C ≠ 0 := by
    rw [hC]; intro hd2
    rw [ZMod.natCast_eq_zero_iff] at hd2
    have hle := Nat.le_of_dvd (by positivity) hd2
    have he : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
    have hp : 0 < 2 ^ k := by positivity
    omega
  have hne : B0 ≠ B0 + C := by
    intro h
    apply hcne
    have h2 : B0 + 0 = B0 + C := by rw [add_zero]; exact h
    exact (add_left_cancel h2).symm
  -- разбор: квадрат V или нет
  by_cases hQ : IsSquare (((b.val : ℤ) : ZMod (2 ^ (k + 1))) ^ 2 - N')
  · have H : ∀ A ∈ ({B0, B0 + C} : Finset (ZMod (2 ^ (k + 1)))),
        IsSquare (A ^ 2 - N') := by
      intro A hA
      rw [Finset.mem_insert, Finset.mem_singleton] at hA
      rcases hA with h | h
      · rw [h, hvalB0]; exact hQ
      · rw [h, hvalBC]; exact hQ
    rw [Finset.filter_true_of_mem H, Finset.card_pair hne, if_pos hQ]
  · have H : ∀ A ∈ ({B0, B0 + C} : Finset (ZMod (2 ^ (k + 1)))),
        ¬ IsSquare (A ^ 2 - N') := by
      intro A hA
      rw [Finset.mem_insert, Finset.mem_singleton] at hA
      rcases hA with h | h
      · rw [h, hvalB0]; exact hQ
      · rw [h, hvalBC]; exact hQ
    rw [Finset.filter_false_of_mem H, Finset.card_empty, if_neg hQ]

#print axioms lift_fibre_card

open scoped Classical in
theorem passCard_succ_lift {k : ℕ} (hk : 1 ≤ k) (N : ℤ) :
    passCard (((N : ℤ)) : ZMod (2 ^ (k + 1)))
      = 2 * (Finset.univ.filter (fun b : ZMod (2 ^ k) =>
            IsSquare (b ^ 2 - ((N : ℤ) : ZMod (2 ^ k))) ∧
            IsSquare (((b.val : ℤ) : ZMod (2 ^ (k + 1))) ^ 2
                        - ((N : ℤ) : ZMod (2 ^ (k + 1)))))).card := by
  -- π отображает проходящих на k+1 в проходящих на k
  have Hf : ∀ A ∈ (Finset.univ.filter fun A : ZMod (2 ^ (k + 1)) =>
                IsSquare (A ^ 2 - ((N : ℤ) : ZMod (2 ^ (k + 1))))),
      ZMod.castHom (pow_dvd_pow 2 (Nat.le_succ k)) (ZMod (2 ^ k)) A ∈
        (Finset.univ.filter fun b : ZMod (2 ^ k) =>
            IsSquare (b ^ 2 - ((N : ℤ) : ZMod (2 ^ k)))) := by
    intro A hA
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hA ⊢
    have h := pass_of_reduce (pow_dvd_pow 2 (Nat.le_succ k)) ((N : ℤ) : ZMod (2 ^ (k + 1))) A hA
    rwa [map_intCast] at h
  unfold passCard
  rw [Finset.card_eq_sum_card_fiberwise Hf,
      Finset.sum_congr rfl (fun b _ => lift_fibre_card hk N b),
      ← Finset.sum_filter, Finset.sum_const, Nat.nsmul_eq_mul, Nat.mul_comm]
  congr 1
  rw [Finset.filter_filter]

#print axioms passCard_succ_lift

open scoped Classical in
theorem passCard_succ_sub {k : ℕ} (hk : 1 ≤ k) (N : ℤ) :
    passCard ((N : ℤ) : ZMod (2 ^ (k + 1)))
      + 2 * (Finset.univ.filter (fun b : ZMod (2 ^ k) =>
          IsSquare (b ^ 2 - ((N : ℤ) : ZMod (2 ^ k))) ∧
          ¬ IsSquare (((b.val : ℤ) : ZMod (2 ^ (k + 1))) ^ 2
                        - ((N : ℤ) : ZMod (2 ^ (k + 1)))))).card
      = 2 * passCard ((N : ℤ) : ZMod (2 ^ k)) := by
  rw [passCard_succ_lift hk N, ← mul_add]
  congr 1
  unfold passCard
  rw [← Finset.filter_filter, ← Finset.filter_filter]
  exact Finset.card_filter_add_card_filter_not
    (fun b : ZMod (2 ^ k) =>
      IsSquare (((b.val : ℤ) : ZMod (2 ^ (k + 1))) ^ 2 - ((N : ℤ) : ZMod (2 ^ (k + 1)))))

/-- N ≡ 3 (mod 4): C_m(N) = 2^(m-2) for m ≥ 3. -/
theorem passCard_three_mod_four (N : ℤ) (hN : N ≡ 3 [ZMOD 4]) (m : ℕ) (hm : 3 ≤ m) :
    passCard ((N : ZMod (2 ^ m))) = 2 ^ (m - 2) := by
  induction m, hm using Nat.le_induction with
  | base => rw [passCard_three_base N hN]; norm_num
  | succ k hk ih =>
      rw [passCard_succ_three hk N hN, ih]
      have hk2 : k + 1 - 2 = (k - 2) + 1 := by omega
      rw [hk2, pow_succ]; ring

set_option maxHeartbeats 1000000 in
/-- Characterization for `N ≡ 5 (mod 8)`, level `k ≥ 5`: a center `A` passes iff
the value `A² − N` is `≡ 4 (mod 32)`.  Forward: push to `ZMod 32` and `decide`
(for `b ∈ {5,13,21,29}` the only square value of `a² − b` is `4`).  Backward:
write `A² − N = 4·d` with `d ≡ 1 (mod 8)` and lift `d` by Hensel at level `k−2`. -/
theorem pass_char_five {k : ℕ} (h32 : (32 : ℕ) ∣ 2 ^ k) (N : ℤ) (hN : N ≡ 5 [ZMOD 8])
    (A : ZMod (2 ^ k)) :
    IsSquare (A ^ 2 - ((N : ℤ) : ZMod (2 ^ k)))
      ↔ ZMod.castHom h32 (ZMod 32) (A ^ 2 - ((N : ℤ) : ZMod (2 ^ k))) = 4 := by
  have hk5 : 5 ≤ k := by
    by_contra hlt
    push_neg at hlt
    interval_cases k <;> exact absurd h32 (by decide)
  have hN32 : ZMod.castHom h32 (ZMod 32) ((N : ℤ) : ZMod (2 ^ k)) = 5
          ∨ ZMod.castHom h32 (ZMod 32) ((N : ℤ) : ZMod (2 ^ k)) = 13
          ∨ ZMod.castHom h32 (ZMod 32) ((N : ℤ) : ZMod (2 ^ k)) = 21
          ∨ ZMod.castHom h32 (ZMod 32) ((N : ℤ) : ZMod (2 ^ k)) = 29 := by
    rw [map_intCast]
    have hd : (8 : ℤ) ∣ (5 - N) := Int.modEq_iff_dvd.mp hN
    have h32' : N % 32 = 5 ∨ N % 32 = 13 ∨ N % 32 = 21 ∨ N % 32 = 29 := by omega
    rcases h32' with h | h | h | h
    · refine Or.inl ?_
      have hmod : N ≡ 5 [ZMOD 32] := Int.modEq_iff_dvd.mpr (by omega)
      have := (ZMod.intCast_eq_intCast_iff N 5 32).mpr hmod
      simpa using this
    · refine Or.inr (Or.inl ?_)
      have hmod : N ≡ 13 [ZMOD 32] := Int.modEq_iff_dvd.mpr (by omega)
      have := (ZMod.intCast_eq_intCast_iff N 13 32).mpr hmod
      simpa using this
    · refine Or.inr (Or.inr (Or.inl ?_))
      have hmod : N ≡ 21 [ZMOD 32] := Int.modEq_iff_dvd.mpr (by omega)
      have := (ZMod.intCast_eq_intCast_iff N 21 32).mpr hmod
      simpa using this
    · refine Or.inr (Or.inr (Or.inr ?_))
      have hmod : N ≡ 29 [ZMOD 32] := Int.modEq_iff_dvd.mpr (by omega)
      have := (ZMod.intCast_eq_intCast_iff N 29 32).mpr hmod
      simpa using this
  constructor
  · intro hsq
    have hmap := IsSquare.map (ZMod.castHom h32 (ZMod 32)) hsq
    rw [map_sub, map_pow] at hmap
    rw [map_sub, map_pow]
    have key : ∀ a b : ZMod 32, (b = 5 ∨ b = 13 ∨ b = 21 ∨ b = 29) →
        IsSquare (a ^ 2 - b) → a ^ 2 - b = 4 := by decide
    exact key _ _ hN32 hmap
  · intro h
    set c : ℤ := (A.val : ℤ) ^ 2 - N with hc_def
    have hcast : ((c : ℤ) : ZMod (2 ^ k)) = A ^ 2 - ((N : ℤ) : ZMod (2 ^ k)) := by
      rw [hc_def]; push_cast; rw [ZMod.natCast_zmod_val]
    have hc4 : ((c : ℤ) : ZMod 32) = 4 := by
      have hh := h
      rw [← hcast, map_intCast] at hh
      exact hh
    have hcmod : c ≡ 4 [ZMOD 32] := by
      have : ((c : ℤ) : ZMod 32) = ((4 : ℤ) : ZMod 32) := by rw [hc4]; norm_num
      exact (ZMod.intCast_eq_intCast_iff c 4 32).mp this
    obtain ⟨s, hs⟩ := Int.modEq_iff_dvd.mp hcmod
    set d : ℤ := 1 - 8 * s with hd_def
    have hcd : c = 4 * d := by rw [hd_def]; linarith [hs]
    have hd1 : d ≡ 1 [ZMOD 8] := Int.modEq_iff_dvd.mpr ⟨s, by rw [hd_def]; ring⟩
    obtain ⟨y, hy⟩ := isSquare_mod_two_pow_of_one_mod_eight d hd1 (k - 2)
    have hcsq : (2 * y) ^ 2 ≡ c [ZMOD 2 ^ k] := by
      obtain ⟨t, ht⟩ := Int.modEq_iff_dvd.mp hy
      refine Int.modEq_iff_dvd.mpr ⟨t, ?_⟩
      have hk2 : (2 : ℤ) ^ k = 4 * 2 ^ (k - 2) := by
        have he : (2 : ℤ) ^ k = 2 ^ 2 * 2 ^ (k - 2) := by rw [← pow_add]; congr 1; omega
        rw [he]; norm_num
      rw [hk2, hcd]; linear_combination (4 : ℤ) * ht
    have hy2 : ((2 * y : ℤ) : ZMod (2 ^ k)) ^ 2 = ((c : ℤ) : ZMod (2 ^ k)) := by
      have h' := (ZMod.intCast_eq_intCast_iff ((2 * y) ^ 2) c (2 ^ k)).mpr hcsq
      push_cast at h' ⊢; exact h'
    refine ⟨((2 * y : ℤ) : ZMod (2 ^ k)), ?_⟩
    rw [← hcast, ← hy2]; ring

/-- Recursion `C_{k+1}(N) = 2·C_k(N)` for `N ≡ 5 (mod 8)`, `k ≥ 5`.  Same fibre
argument as `passCard_succ_three`, but the preserved invariant is the value mod
`32` (`pass_char_five`) instead of mod `8`. -/
theorem passCard_succ_five {k : ℕ} (hk : 5 ≤ k) (N : ℤ) (hN : N ≡ 5 [ZMOD 8]) :
    passCard ((N : ℤ) : ZMod (2 ^ (k + 1))) = 2 * passCard ((N : ℤ) : ZMod (2 ^ k)) := by
  have hdvd : (2 ^ k : ℕ) ∣ 2 ^ (k + 1) := pow_dvd_pow 2 (Nat.le_succ k)
  have h32k : (32 : ℕ) ∣ 2 ^ k :=
    ⟨2 ^ (k - 5), by rw [show (32 : ℕ) = 2 ^ 5 from rfl, ← pow_add]; congr 1; omega⟩
  have h32k1 : (32 : ℕ) ∣ 2 ^ (k + 1) :=
    ⟨2 ^ (k + 1 - 5), by rw [show (32 : ℕ) = 2 ^ 5 from rfl, ← pow_add]; congr 1; omega⟩
  have hmem : ∀ A : ZMod (2 ^ (k + 1)),
      IsSquare (A ^ 2 - ((N : ℤ) : ZMod (2 ^ (k + 1))))
        ↔ IsSquare ((ZMod.castHom hdvd (ZMod (2 ^ k)) A) ^ 2 - ((N : ℤ) : ZMod (2 ^ k))) := by
    intro A
    have hA32 : ZMod.castHom h32k1 (ZMod 32) A
             = ZMod.castHom h32k (ZMod 32) (ZMod.castHom hdvd (ZMod (2 ^ k)) A) := by
      rw [← RingHom.comp_apply, ZMod.castHom_comp]
    have hcc : ZMod.castHom h32k1 (ZMod 32) (A ^ 2 - ((N : ℤ) : ZMod (2 ^ (k + 1))))
             = ZMod.castHom h32k (ZMod 32)
                 ((ZMod.castHom hdvd (ZMod (2 ^ k)) A) ^ 2 - ((N : ℤ) : ZMod (2 ^ k))) := by
      simp only [map_sub, map_pow, map_intCast, hA32]
    rw [pass_char_five h32k1 N hN A,
        pass_char_five h32k N hN (ZMod.castHom hdvd (ZMod (2 ^ k)) A)]
    exact iff_of_eq (by rw [hcc])
  have Hf : ∀ A ∈ (Finset.univ.filter fun A : ZMod (2 ^ (k + 1)) =>
                IsSquare (A ^ 2 - ((N : ℤ) : ZMod (2 ^ (k + 1))))),
      ZMod.castHom hdvd (ZMod (2 ^ k)) A ∈
        (Finset.univ.filter fun b : ZMod (2 ^ k) =>
            IsSquare (b ^ 2 - ((N : ℤ) : ZMod (2 ^ k)))) := by
    intro A hA
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hA ⊢
    exact (hmem A).mp hA
  have hfib : ∀ b ∈ (Finset.univ.filter fun b : ZMod (2 ^ k) =>
                IsSquare (b ^ 2 - ((N : ℤ) : ZMod (2 ^ k)))),
      ((Finset.univ.filter fun A : ZMod (2 ^ (k + 1)) =>
          IsSquare (A ^ 2 - ((N : ℤ) : ZMod (2 ^ (k + 1))))).filter
        (fun A => ZMod.castHom hdvd (ZMod (2 ^ k)) A = b)).card = 2 := by
    intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    have hset : (Finset.univ.filter fun A : ZMod (2 ^ (k + 1)) =>
          IsSquare (A ^ 2 - ((N : ℤ) : ZMod (2 ^ (k + 1))))).filter
          (fun A => ZMod.castHom hdvd (ZMod (2 ^ k)) A = b)
        = Finset.univ.filter (fun A : ZMod (2 ^ (k + 1)) =>
            ZMod.castHom hdvd (ZMod (2 ^ k)) A = b) := by
      ext A
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨_, h2⟩; exact h2
      · intro hAb
        exact ⟨(hmem A).mpr (by rw [hAb]; exact hb), hAb⟩
    rw [hset, castHom_fiber_pair hdvd b]
    have hcne : ((2 ^ k : ℕ) : ZMod (2 ^ (k + 1))) ≠ 0 := by
      intro hd2
      rw [ZMod.natCast_eq_zero_iff] at hd2
      have hle := Nat.le_of_dvd (by positivity) hd2
      have he : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
      have hp : 0 < 2 ^ k := by positivity
      omega
    apply Finset.card_pair
    intro hcontra
    apply hcne
    have hz : ((b.val : ℕ) : ZMod (2 ^ (k + 1))) + ((2 ^ k : ℕ) : ZMod (2 ^ (k + 1)))
            = ((b.val : ℕ) : ZMod (2 ^ (k + 1))) + 0 := by
      rw [add_zero]; exact hcontra.symm
    exact add_left_cancel hz
  unfold passCard
  rw [Finset.filter_congr_decidable, Finset.filter_congr_decidable]
  rw [Finset.card_eq_sum_card_fiberwise Hf, Finset.sum_const_nat hfib, Nat.mul_comm]

set_option maxHeartbeats 1000000 in
/-- N ≡ 5 (mod 8): base level C_5 = 4. Reduce to the representative N = 5 via the
mod-8 invariance (milestone A), then decide on the finite ring `ZMod 32`. -/
theorem passCard_five_base (N : ℤ) (hN : N ≡ 5 [ZMOD 8]) :
    passCard ((N : ZMod (2 ^ 5))) = 4 := by
  have hodd : Odd N := by
    have hd : (8 : ℤ) ∣ (5 - N) := Int.modEq_iff_dvd.mp hN
    exact Int.odd_iff.mpr (by omega)
  rw [passCard_eq_of_modEq_eight 5 N 5 hodd ⟨2, by norm_num⟩ hN]
  unfold passCard
  rw [Finset.filter_congr_decidable]
  decide

/-- N ≡ 5 (mod 8): C_m(N) = 2^(m-3) for m ≥ 5. -/
theorem passCard_five_mod_eight (N : ℤ) (hN : N ≡ 5 [ZMOD 8]) (m : ℕ) (hm : 5 ≤ m) :
    passCard ((N : ZMod (2 ^ m))) = 2 ^ (m - 3) := by
  induction m, hm using Nat.le_induction with
  | base => rw [passCard_five_base N hN]; norm_num
  | succ k hk ih =>
      rw [passCard_succ_five hk N hN, ih]
      have hk2 : k + 1 - 3 = (k - 3) + 1 := by omega
      rw [hk2, pow_succ]; ring

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

set_option maxHeartbeats 1000000 in
/-- N ≡ 1 (mod 8): odd-chain base C_5 = 8 (representative N = 1, decide on ZMod 32). -/
theorem passCard_one_five_base (N : ℤ) (hN : N ≡ 1 [ZMOD 8]) :
    passCard ((N : ZMod (2 ^ 5))) = 8 := by
  have hodd : Odd N := by
    have hd : (8 : ℤ) ∣ (1 - N) := Int.modEq_iff_dvd.mp hN
    exact Int.odd_iff.mpr (by omega)
  rw [passCard_eq_of_modEq_eight 5 N 1 hodd odd_one hN]
  unfold passCard
  rw [Finset.filter_congr_decidable]
  decide

set_option maxHeartbeats 4000000 in
/-- N ≡ 1 (mod 8): even-chain base C_6 = 8 (representative N = 1, decide on ZMod 64). -/
theorem passCard_one_six_base (N : ℤ) (hN : N ≡ 1 [ZMOD 8]) :
    passCard ((N : ZMod (2 ^ 6))) = 8 := by
  have hodd : Odd N := by
    have hd : (8 : ℤ) ∣ (1 - N) := Int.modEq_iff_dvd.mp hN
    exact Int.odd_iff.mpr (by omega)
  rw [passCard_eq_of_modEq_eight 6 N 1 hodd odd_one hN]
  unfold passCard
  rw [Finset.filter_congr_decidable]
  decide

/-- N ≡ 1 (mod 8): every passing center is odd — at the `ZMod 8` level its image is
a unit.  Even centers give `A² − N ≡ 3` or `7 (mod 8)`, neither a square.  A reusable
brick for the N ≡ 1 count, which then ranges over odd centers only. -/
theorem one_pass_image_isUnit {k : ℕ} (h8 : (8 : ℕ) ∣ 2 ^ k) (N : ℤ) (hN : N ≡ 1 [ZMOD 8])
    (A : ZMod (2 ^ k)) (hsq : IsSquare (A ^ 2 - ((N : ℤ) : ZMod (2 ^ k)))) :
    IsUnit (ZMod.castHom h8 (ZMod 8) A) := by
  have hN8 : ZMod.castHom h8 (ZMod 8) ((N : ℤ) : ZMod (2 ^ k)) = 1 := by
    rw [map_intCast]
    have := (ZMod.intCast_eq_intCast_iff N 1 8).mpr hN
    simpa using this
  have hmap := IsSquare.map (ZMod.castHom h8 (ZMod 8)) hsq
  rw [map_sub, map_pow, hN8] at hmap
  have key : ∀ a : ZMod 8, IsSquare (a ^ 2 - 1) → IsUnit a := by decide
  exact key _ hmap

/-- Sufficiency half of the 2-adic square characterization: `2^(2e)·w` with
`w ≡ 1 (mod 8)` is a square in `ZMod (2^k)` for every `k`.  If `2e ≥ k` the value
is `0`; otherwise lift `w` by Hensel at level `k − 2e` and scale by `2^e`.
Reusable brick for the N ≡ 1 count (values `A²−1` have the form `2^(2+t)·w`). -/
theorem isSquare_two_pow_mul (e : ℕ) (w : ℤ) (hw : w ≡ 1 [ZMOD 8]) (k : ℕ) :
    IsSquare (((2 ^ (2 * e) * w : ℤ) : ZMod (2 ^ k))) := by
  rcases Nat.lt_or_ge (2 * e) k with hk | hk
  · -- 2e < k: Hensel lift of w at level k − 2e, scaled by 2^e
    obtain ⟨y, hy⟩ := isSquare_mod_two_pow_of_one_mod_eight w hw (k - 2 * e)
    obtain ⟨t, ht⟩ := Int.modEq_iff_dvd.mp hy
    have hee : (2 : ℤ) ^ (2 * e) = 2 ^ e * 2 ^ e := by rw [two_mul, pow_add]
    have hpow : (2 : ℤ) ^ k = 2 ^ (2 * e) * 2 ^ (k - 2 * e) := by
      rw [← pow_add]; congr 1; omega
    have hcong : (2 ^ e * y) ^ 2 ≡ 2 ^ (2 * e) * w [ZMOD 2 ^ k] := by
      refine Int.modEq_iff_dvd.mpr ⟨t, ?_⟩
      have key : (2 ^ (2 * e) * w) - (2 ^ e * y) ^ 2 = 2 ^ (2 * e) * (w - y ^ 2) := by
        rw [hee]; ring
      rw [key, hpow, ht]; ring
    have hy2 : (((2 ^ e * y : ℤ)) : ZMod (2 ^ k)) ^ 2
             = (((2 ^ (2 * e) * w : ℤ)) : ZMod (2 ^ k)) := by
      have h' := (ZMod.intCast_eq_intCast_iff ((2 ^ e * y) ^ 2) (2 ^ (2 * e) * w) (2 ^ k)).mpr hcong
      push_cast at h' ⊢; exact h'
    exact ⟨((2 ^ e * y : ℤ) : ZMod (2 ^ k)), by rw [← hy2]; ring⟩
  · -- 2e ≥ k: the value is 0
    refine ⟨0, ?_⟩
    have hz : ((2 ^ (2 * e) * w : ℤ) : ZMod (2 ^ k)) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      exact (pow_dvd_pow 2 hk).mul_right w
    rw [hz]; ring

open scoped Classical in
theorem isSquare_two_pow_mul_rev (s : ℕ) (w : ℤ) (hw : Odd w) (k : ℕ) (hsk : s < k)
    (hsq : IsSquare (((2 ^ s * w : ℤ) : ZMod (2 ^ k)))) :
    Even s ∧ w ≡ 1 [ZMOD 2 ^ (min 3 (k - s))] := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- целый корень: из IsSquare берём r : ZMod 2^k, затем представитель R : ℤ
  obtain ⟨r, hr⟩ := hsq
  set R : ℤ := (r.val : ℤ) with hRdef
  -- (R : ZMod 2^k) = r, поэтому 2^s·w ≡ R² (mod 2^k), т.е. 2^k ∣ 2^s·w − R²
  have hRcast : ((R : ℤ) : ZMod (2 ^ k)) = r := by
    rw [hRdef]; push_cast; rw [ZMod.natCast_zmod_val]
  have hdvd : (2 ^ k : ℤ) ∣ (2 ^ s * w - R ^ 2) := by
    have h0 : (((2 ^ s * w - R ^ 2 : ℤ)) : ZMod (2 ^ k)) = 0 := by
      have e : (((2 ^ s * w - R ^ 2 : ℤ)) : ZMod (2 ^ k))
             = ((2 ^ s * w : ℤ) : ZMod (2 ^ k)) - ((R : ℤ) : ZMod (2 ^ k)) ^ 2 := by
        push_cast; ring
      rw [e, hRcast, hr]; ring    -- hr : (2^s·w cast) = r*r ; goal r*r - r^2 = 0
    rwa [ZMod.intCast_zmod_eq_zero_iff_dvd] at h0
  -- Step A: R² = 2^s · (odd).  Since s < k, also 2^(s+1) ∣ (2^s·w − R²); and
  -- 2^(s+1) ∣ (2^s·w − 2^s) because w is odd, so 2^(s+1) ∣ (2^s − R²).
  have hdvd2 : (2 : ℤ) ^ (s + 1) ∣ (2 ^ s * w - R ^ 2) :=
    dvd_trans (pow_dvd_pow 2 hsk) hdvd
  obtain ⟨u, hu⟩ := hw                        -- w = 2*u + 1
  have hw1 : (2 : ℤ) ^ (s + 1) ∣ (2 ^ s * w - 2 ^ s) :=
    ⟨u, by rw [hu, pow_succ]; ring⟩
  have hRsq : (2 : ℤ) ^ (s + 1) ∣ (2 ^ s - R ^ 2) := by
    have h := hdvd2.sub hw1
    have e : (2 ^ s * w - R ^ 2) - (2 ^ s * w - 2 ^ s) = (2 ^ s - R ^ 2 : ℤ) := by ring
    rwa [e] at h
  obtain ⟨tt, htt⟩ := hRsq                    -- 2^s − R² = 2^(s+1)·tt
  have hR2 : R ^ 2 = 2 ^ s * (1 - 2 * tt) := by
    rw [pow_succ] at htt; linear_combination -htt
  have hodd' : ¬ (2 : ℤ) ∣ (1 - 2 * tt) := by rintro ⟨c, hc⟩; omega
  have hoddne : (1 - 2 * tt : ℤ) ≠ 0 := by intro h; omega
  have h2s_ne : (2 : ℤ) ^ s ≠ 0 := pow_ne_zero s (by norm_num)
  have hRne : R ≠ 0 := by
    intro h
    apply hoddne
    have h0 : (2 : ℤ) ^ s * (1 - 2 * tt) = 0 := by rw [← hR2, h]; ring
    rcases mul_eq_zero.mp h0 with h1 | h1
    · exact absurd h1 h2s_ne
    · exact h1
  have hRne2 : R ^ 2 ≠ 0 := pow_ne_zero 2 hRne
  -- Step B: v₂(R²) = s, and v₂(R²) = v₂(R)+v₂(R); hence s is even.
  have hdvd_s : (2 : ℤ) ^ s ∣ R ^ 2 := ⟨1 - 2 * tt, hR2⟩
  have h_not : ¬ (2 : ℤ) ^ (s + 1) ∣ R ^ 2 := by
    rintro ⟨c, hc⟩
    have e : (2 : ℤ) ^ s * (2 * c) = 2 ^ s * (1 - 2 * tt) := by
      rw [← hR2, hc, pow_succ]; ring
    have h2 : (2 * c : ℤ) = 1 - 2 * tt := mul_left_cancel₀ h2s_ne e
    omega
  have hle : s ≤ padicValInt 2 (R ^ 2) := by
    rcases (padicValInt_dvd_iff (p := 2) s (R ^ 2)).mp (by exact_mod_cast hdvd_s) with h | h
    · exact absurd h hRne2
    · exact h
  have hlt : padicValInt 2 (R ^ 2) ≤ s := by
    by_contra hc; push_neg at hc
    exact h_not (by
      exact (padicValInt_dvd_iff (p := 2) (s + 1) (R ^ 2)).mpr (Or.inr (by omega)))
  have hv2eq : padicValInt 2 (R ^ 2) = s := le_antisymm hlt hle
  set a := padicValInt 2 R with ha_def
  have hv2mul : padicValInt 2 (R ^ 2) = a + a := by
    rw [pow_two, padicValInt.mul hRne hRne, ← ha_def]
  have hsaa : s = a + a := by rw [← hv2eq, hv2mul]
  have hs_even : Even s := ⟨a, hsaa⟩
  -- Step C: R = 2^a · R' with R' odd.
  have ha_dvd : (2 : ℤ) ^ a ∣ R := by
    rw [ha_def]; exact_mod_cast padicValInt_dvd (p := 2) R
  obtain ⟨R', hR'⟩ := ha_dvd
  have hR'odd : Odd R' := by
    rcases Int.even_or_odd R' with he | ho
    · exfalso
      obtain ⟨c, hc⟩ := he                    -- R' = c + c
      have hdvdR1 : (2 : ℤ) ^ (a + 1) ∣ R := ⟨c, by rw [hR', hc, pow_succ]; ring⟩
      rcases (padicValInt_dvd_iff (p := 2) (a + 1) R).mp (by exact_mod_cast hdvdR1) with h | h
      · exact hRne h
      · omega
    · exact ho
  -- Step D: R² = 2^s · R'², cancel 2^s, combine with R'² ≡ 1 (mod 8).
  have hR2' : R ^ 2 = 2 ^ s * R' ^ 2 := by
    rw [hR', mul_pow, hsaa, pow_add]; ring
  have hcancel : (2 : ℤ) ^ (k - s) ∣ (w - R' ^ 2) := by
    have hfac : (2 ^ s * w - R ^ 2 : ℤ) = 2 ^ s * (w - R' ^ 2) := by rw [hR2']; ring
    have hpk : (2 : ℤ) ^ k = 2 ^ s * 2 ^ (k - s) := by rw [← pow_add]; congr 1; omega
    have hd : (2 : ℤ) ^ s * 2 ^ (k - s) ∣ 2 ^ s * (w - R' ^ 2) := by
      rw [← hpk, ← hfac]; exact hdvd
    exact (mul_dvd_mul_iff_left h2s_ne).mp hd
  have h8 : (8 : ℤ) ∣ (R' ^ 2 - 1) := Int.eight_dvd_sq_sub_one_of_odd hR'odd
  have hM : (2 : ℤ) ^ (min 3 (k - s)) ∣ (w - 1) := by
    have hm1 : (2 : ℤ) ^ (min 3 (k - s)) ∣ (w - R' ^ 2) :=
      dvd_trans (pow_dvd_pow 2 (min_le_right 3 (k - s))) hcancel
    have h8dvd : (2 : ℤ) ^ (min 3 (k - s)) ∣ (8 : ℤ) := by
      have h := pow_dvd_pow (2 : ℤ) (min_le_left 3 (k - s))
      norm_num at h; exact h
    have hm2 : (2 : ℤ) ^ (min 3 (k - s)) ∣ (R' ^ 2 - 1) := dvd_trans h8dvd h8
    have hsum := dvd_add hm1 hm2
    rwa [show (w - R' ^ 2) + (R' ^ 2 - 1) = w - 1 from by ring] at hsum
  refine ⟨hs_even, ?_⟩
  rw [Int.modEq_iff_dvd, show (1 - w : ℤ) = -(w - 1) from by ring]
  exact dvd_neg.mpr hM


/-- Для нечётного `w`: `w ≡ 1 (mod 2^min(3,j))` ⇒ `w` — квадрат по модулю `2^j`.
При `j < 3` свидетель `y = 1`; при `j ≥ 3` — лемма Гензеля проекта. -/
theorem sq_of_one_mod (w : ℤ) (j : ℕ) (hj : w ≡ 1 [ZMOD 2 ^ (min 3 j)]) :
    ∃ y : ℤ, y ^ 2 ≡ w [ZMOD 2 ^ j] := by
  rcases Nat.lt_or_ge j 3 with h3 | h3
  · rw [min_eq_right (by omega : j ≤ 3)] at hj
    exact ⟨1, by simpa using hj.symm⟩
  · rw [min_eq_left h3] at hj
    exact isSquare_mod_two_pow_of_one_mod_eight w hj j

/-- Граничная достаточность: `2^(2e)·w` — квадрат в `ZMod 2^k`, если
`w ≡ 1 (mod 2^min(3,k-2e))`.  Обобщает `isSquare_two_pow_mul` (там `w ≡ 1 mod 8`). -/
theorem isSquare_two_pow_mul' (e : ℕ) (w : ℤ) (k : ℕ)
    (hwm : w ≡ 1 [ZMOD 2 ^ (min 3 (k - 2 * e))]) :
    IsSquare (((2 ^ (2 * e) * w : ℤ) : ZMod (2 ^ k))) := by
  rcases Nat.lt_or_ge (2 * e) k with hk | hk
  · obtain ⟨y, hy⟩ := sq_of_one_mod w (k - 2 * e) hwm
    obtain ⟨t, ht⟩ := Int.modEq_iff_dvd.mp hy
    have hee : (2 : ℤ) ^ (2 * e) = 2 ^ e * 2 ^ e := by rw [two_mul, pow_add]
    have hpow : (2 : ℤ) ^ k = 2 ^ (2 * e) * 2 ^ (k - 2 * e) := by rw [← pow_add]; congr 1; omega
    have hcong : (2 ^ e * y) ^ 2 ≡ 2 ^ (2 * e) * w [ZMOD 2 ^ k] := by
      refine Int.modEq_iff_dvd.mpr ⟨t, ?_⟩
      have key : (2 ^ (2 * e) * w) - (2 ^ e * y) ^ 2 = 2 ^ (2 * e) * (w - y ^ 2) := by
        rw [hee]; ring
      rw [key, hpow, ht]; ring
    have hy2 : (((2 ^ e * y : ℤ)) : ZMod (2 ^ k)) ^ 2
             = (((2 ^ (2 * e) * w : ℤ)) : ZMod (2 ^ k)) := by
      have h' := (ZMod.intCast_eq_intCast_iff ((2 ^ e * y) ^ 2) (2 ^ (2 * e) * w) (2 ^ k)).mpr hcong
      push_cast at h' ⊢; exact h'
    exact ⟨((2 ^ e * y : ℤ) : ZMod (2 ^ k)), by rw [← hy2]; ring⟩
  · refine ⟨0, ?_⟩
    have hz : (((2 ^ (2 * e) * w : ℤ)) : ZMod (2 ^ k)) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast
      exact (pow_dvd_pow 2 hk).mul_right w
    rw [hz]; ring

/-- **Характеризация прохождения.** Для нечётного `w`:
`2^s·w` — квадрат в `ZMod 2^k` ⟺ `k ≤ s` ∨ (`s` чётно ∧ `w ≡ 1 mod 2^min(3,k-s)`). -/
theorem isSquare_two_pow_mul_iff (s : ℕ) (w : ℤ) (hw : Odd w) (k : ℕ) :
    IsSquare (((2 ^ s * w : ℤ) : ZMod (2 ^ k)))
      ↔ (k ≤ s ∨ (Even s ∧ w ≡ 1 [ZMOD 2 ^ (min 3 (k - s))])) := by
  constructor
  · intro hsq
    rcases Nat.lt_or_ge s k with hsk | hks
    · exact Or.inr (isSquare_two_pow_mul_rev s w hw k hsk hsq)
    · exact Or.inl hks
  · rintro (hks | ⟨hse, hwm⟩)
    · refine ⟨0, ?_⟩
      have hz : (((2 ^ s * w : ℤ)) : ZMod (2 ^ k)) = 0 := by
        rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast
        exact (pow_dvd_pow 2 hks).mul_right w
      rw [hz]; ring
    · obtain ⟨e, he⟩ := hse
      have hs2e : s = 2 * e := by rw [he]; ring
      rw [hs2e]; rw [hs2e] at hwm
      exact isSquare_two_pow_mul' e w k hwm


/-- Для нечётного `a` с `a²−1 ≠ 0`: `a²−1 = 2^s·w` с нечётным `w`, где
`s = v₂(a²−1) ≥ 3` (так как `8 ∣ a²−1`). -/
theorem odd_sq_sub_one_decomp (a : ℤ) (ha : Odd a) (hane : a ^ 2 - 1 ≠ 0) :
    ∃ w : ℤ, Odd w ∧ 3 ≤ padicValInt 2 (a ^ 2 - 1)
      ∧ a ^ 2 - 1 = 2 ^ (padicValInt 2 (a ^ 2 - 1)) * w := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set s := padicValInt 2 (a ^ 2 - 1) with hs
  -- 2^s ∣ a²−1
  have hdvd : (2 : ℤ) ^ s ∣ (a ^ 2 - 1) := by
    rw [hs]; exact padicValInt_dvd (p := 2) (a ^ 2 - 1)
  obtain ⟨w, hw⟩ := hdvd
  -- w нечётно: иначе 2^(s+1) ∣ a²−1, что противоречит s = v₂
  have hwodd : Odd w := by
    rcases Int.even_or_odd w with he | ho
    · exfalso
      obtain ⟨c, hc⟩ := he
      have hdd : (2 : ℤ) ^ (s + 1) ∣ (a ^ 2 - 1) := ⟨c, by rw [hw, hc, pow_succ]; ring⟩
      rcases (padicValInt_dvd_iff (p := 2) (s + 1) (a ^ 2 - 1)).mp (by exact hdd) with h | h
      · exact hane h
      · omega
    · exact ho
  -- 3 ≤ s, из 8 ∣ a²−1
  have h3 : 3 ≤ s := by
    have h8 : (2 : ℤ) ^ 3 ∣ (a ^ 2 - 1) := by
      have h := Int.eight_dvd_sq_sub_one_of_odd ha
      norm_num; exact h
    rcases (padicValInt_dvd_iff (p := 2) 3 (a ^ 2 - 1)).mp (by exact h8) with h | h
    · exact absurd h hane
    · exact h
  exact ⟨w, hwodd, h3, hw⟩

#print axioms odd_sq_sub_one_decomp

theorem sqrt_one_mod_two_pow (j : ℕ) (hj : 3 ≤ j) (a : ℤ) (ha : (2 ^ j : ℤ) ∣ a ^ 2 - 1) :
    a ≡ 1 [ZMOD 2 ^ j] ∨ a ≡ -1 [ZMOD 2 ^ j]
      ∨ a ≡ 2 ^ (j - 1) - 1 [ZMOD 2 ^ j] ∨ a ≡ 2 ^ (j - 1) + 1 [ZMOD 2 ^ j] := by
  have hjpos : 1 ≤ j := by omega
  have h2j : (2 : ℤ) ^ j = 2 * 2 ^ (j - 1) := by rw [← pow_succ']; congr 1; omega
  -- a нечётно
  have haodd : ¬ (2 : ℤ) ∣ a := by
    intro ⟨c, hc⟩
    have h2d : (2 : ℤ) ∣ a ^ 2 - 1 := dvd_trans ⟨2 ^ (j - 1), h2j⟩ ha
    rw [hc] at h2d; obtain ⟨d, hd⟩ := h2d
    rw [show (2 * c) ^ 2 - 1 = 4 * c ^ 2 - 1 from by ring] at hd; omega
  -- из 2^(j-1) ∣ (a − r) вывести a ≡ r ∨ a ≡ r + 2^(j-1)  (mod 2^j)
  have split : ∀ r : ℤ, (2 : ℤ) ^ (j - 1) ∣ (a - r) →
      a ≡ r [ZMOD 2 ^ j] ∨ a ≡ r + 2 ^ (j - 1) [ZMOD 2 ^ j] := by
    rintro r ⟨s, hs⟩
    rcases Int.even_or_odd s with ⟨u, hu⟩ | ⟨u, hu⟩
    · left
      refine Int.modEq_iff_dvd.mpr ⟨-u, ?_⟩
      rw [hu] at hs; rw [h2j]; linear_combination -hs
    · right
      refine Int.modEq_iff_dvd.mpr ⟨-u, ?_⟩
      rw [hu] at hs; rw [h2j]; linear_combination -hs
  have hcase : a % 4 = 1 ∨ a % 4 = 3 := by
    rcases Int.even_or_odd a with h | h
    · exact absurd (by obtain ⟨c, hc⟩ := h; exact ⟨c, by omega⟩) haodd
    · obtain ⟨c, hc⟩ := h; omega
  have hprod : a ^ 2 - 1 = (a - 1) * (a + 1) := by ring
  rcases hcase with h4 | h4
  · -- a ≡ 1 (mod 4): высокая степень у (a−1)
    obtain ⟨t, ht⟩ : ∃ t, a + 1 = 2 * (2 * t + 1) := ⟨a / 4, by omega⟩
    have hdvd_prod : (2 : ℤ) ^ (j - 1) ∣ (a - 1) * (2 * t + 1) := by
      have h2 : (2 : ℤ) ^ j ∣ 2 * ((a - 1) * (2 * t + 1)) := by
        rw [show 2 * ((a - 1) * (2 * t + 1)) = (a - 1) * (a + 1) from by rw [ht]; ring, ← hprod]
        exact ha
      rw [h2j] at h2
      exact (mul_dvd_mul_iff_left (by norm_num : (2 : ℤ) ≠ 0)).mp h2
    have hcop : IsCoprime ((2 : ℤ) ^ (j - 1)) (2 * t + 1) :=
      (show IsCoprime (2 : ℤ) (2 * t + 1) from ⟨-t, 1, by ring⟩).pow_left
    have hd1 : (2 : ℤ) ^ (j - 1) ∣ (a - 1) := hcop.dvd_of_dvd_mul_right hdvd_prod
    rcases split 1 hd1 with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr (by rw [add_comm] at h; exact h)))
  · -- a ≡ 3 (mod 4): высокая степень у (a+1)
    obtain ⟨t, ht⟩ : ∃ t, a - 1 = 2 * (2 * t + 1) := ⟨(a - 3) / 4, by omega⟩
    have hdvd_prod : (2 : ℤ) ^ (j - 1) ∣ (a + 1) * (2 * t + 1) := by
      have h2 : (2 : ℤ) ^ j ∣ 2 * ((a + 1) * (2 * t + 1)) := by
        rw [show 2 * ((a + 1) * (2 * t + 1)) = (a - 1) * (a + 1) from by rw [ht]; ring, ← hprod]
        exact ha
      rw [h2j] at h2
      exact (mul_dvd_mul_iff_left (by norm_num : (2 : ℤ) ≠ 0)).mp h2
    have hcop : IsCoprime ((2 : ℤ) ^ (j - 1)) (2 * t + 1) :=
      (show IsCoprime (2 : ℤ) (2 * t + 1) from ⟨-t, 1, by ring⟩).pow_left
    have hd1 : (2 : ℤ) ^ (j - 1) ∣ (a + 1) := hcop.dvd_of_dvd_mul_right hdvd_prod
    have hd1' : (2 : ℤ) ^ (j - 1) ∣ (a - (-1)) := by rwa [show a - (-1) = a + 1 from by ring]
    rcases split (-1) hd1' with h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl (by rw [show (-1 : ℤ) + 2 ^ (j - 1) = 2 ^ (j - 1) - 1 from by ring] at h; exact h)))

#print axioms sqrt_one_mod_two_pow

theorem nonlift_iff_val {k : ℕ} (b : ZMod (2 ^ k))
    (s : ℕ) (w : ℤ) (hw : Odd w)
    (hdecomp : (b.val : ℤ) ^ 2 - 1 = 2 ^ s * w) :
    (IsSquare (b ^ 2 - ((1 : ℤ) : ZMod (2 ^ k))) ∧
     ¬ IsSquare (((b.val : ℤ) : ZMod (2 ^ (k + 1))) ^ 2 - ((1 : ℤ) : ZMod (2 ^ (k + 1)))))
      ↔ ((k ≤ s ∨ (Even s ∧ w ≡ 1 [ZMOD 2 ^ (min 3 (k - s))]))
          ∧ ¬ ((k + 1) ≤ s ∨ (Even s ∧ w ≡ 1 [ZMOD 2 ^ (min 3 (k + 1 - s))]))) := by
  haveI : NeZero (2 ^ k) := ⟨pow_ne_zero _ two_ne_zero⟩
  have e1 : b ^ 2 - ((1 : ℤ) : ZMod (2 ^ k)) = (((2 ^ s * w : ℤ)) : ZMod (2 ^ k)) := by
    rw [← hdecomp]; push_cast; rw [ZMod.natCast_zmod_val]
  have e2 : ((b.val : ℤ) : ZMod (2 ^ (k + 1))) ^ 2 - ((1 : ℤ) : ZMod (2 ^ (k + 1)))
          = (((2 ^ s * w : ℤ)) : ZMod (2 ^ (k + 1))) := by
    rw [← hdecomp]; push_cast; ring
  rw [e1, e2, isSquare_two_pow_mul_iff s w hw k, isSquare_two_pow_mul_iff s w hw (k + 1)]

theorem nonlift_imp_s_ge {k s : ℕ} (w : ℤ) (hk : 5 ≤ k)
    (h : (k ≤ s ∨ (Even s ∧ w ≡ 1 [ZMOD 2 ^ (min 3 (k - s))]))
       ∧ ¬ ((k + 1) ≤ s ∨ (Even s ∧ w ≡ 1 [ZMOD 2 ^ (min 3 (k + 1 - s))]))) :
    k - 2 ≤ s := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨hP, hnP⟩ := h
  have hmin  : min 3 (k - s)     = 3 := min_eq_left (by omega)
  have hmin1 : min 3 (k + 1 - s) = 3 := min_eq_left (by omega)
  rw [hmin] at hP
  rw [hmin1] at hnP
  rcases hP with h1 | h1
  · omega
  · exact hnP (Or.inr h1)

theorem nonlift_cases {k s : ℕ} (w : ℤ) (hk : 5 ≤ k) (hw : Odd w) (hs : k - 2 ≤ s)
    (h : (k ≤ s ∨ (Even s ∧ w ≡ 1 [ZMOD 2 ^ (min 3 (k - s))]))
       ∧ ¬ ((k + 1) ≤ s ∨ (Even s ∧ w ≡ 1 [ZMOD 2 ^ (min 3 (k + 1 - s))]))) :
    (s = k ∧ Odd k)
      ∨ (s = k - 1 ∧ Odd k ∧ ¬ (w ≡ 1 [ZMOD 4]))
      ∨ (s = k - 2 ∧ Even k ∧ w ≡ 1 [ZMOD 4] ∧ ¬ (w ≡ 1 [ZMOD 8])) := by
  obtain ⟨hP, hnP⟩ := h
  have hw2 : w ≡ 1 [ZMOD 2] := by
    obtain ⟨m, rfl⟩ := hw
    exact Int.modEq_iff_dvd.mpr ⟨-m, by ring⟩
  have hsle : s ≤ k := by
    by_contra hc; push_neg at hc
    exact hnP (Or.inl (by omega))
  have hs3 : s = k ∨ s = k - 1 ∨ s = k - 2 := by omega
  rcases hs3 with rfl | rfl | rfl
  · -- s = k  ⇒  Odd k
    refine Or.inl ⟨rfl, ?_⟩
    rcases Nat.even_or_odd s with hek | hok
    · exfalso; apply hnP; right; refine ⟨hek, ?_⟩
      rw [show s + 1 - s = 1 from by omega, show min 3 1 = 1 from by decide, pow_one]
      exact hw2
    · exact hok
  · -- s = k-1  ⇒  Odd k ∧ ¬(w ≡ 1 mod 4)
    have hEk1 : Even (k - 1) := by
      rcases hP with h1 | ⟨h1, _⟩
      · exact absurd h1 (by omega)
      · exact h1
    have hoddk : Odd k := by
      rcases Nat.even_or_odd k with hek | hok
      · exfalso; rw [Nat.even_iff] at hek; rw [Nat.even_iff] at hEk1; omega
      · exact hok
    refine Or.inr (Or.inl ⟨rfl, hoddk, ?_⟩)
    intro hw4
    apply hnP; right; refine ⟨hEk1, ?_⟩
    rw [show k + 1 - (k - 1) = 2 from by omega, show min 3 2 = 2 from by decide,
        show (2 : ℤ) ^ 2 = 4 from by norm_num]
    exact hw4
  · -- s = k-2  ⇒  Even k ∧ (w ≡ 1 mod 4) ∧ ¬(w ≡ 1 mod 8)
    have hEk2 : Even (k - 2) := by
      rcases hP with h1 | ⟨h1, _⟩
      · exact absurd h1 (by omega)
      · exact h1
    have hw4 : w ≡ 1 [ZMOD 4] := by
      rcases hP with h1 | ⟨_, h2⟩
      · exact absurd h1 (by omega)
      · rw [show k - (k - 2) = 2 from by omega, show min 3 2 = 2 from by decide,
            show (2 : ℤ) ^ 2 = 4 from by norm_num] at h2
        exact h2
    have hevk : Even k := by
      rcases Nat.even_or_odd k with hek | hok
      · exact hek
      · exfalso; rw [Nat.even_iff] at hEk2; rw [Nat.odd_iff] at hok; omega
    refine Or.inr (Or.inr ⟨rfl, hevk, hw4, ?_⟩)
    intro hw8
    apply hnP; right; refine ⟨hEk2, ?_⟩
    rw [show k + 1 - (k - 2) = 3 from by omega, show min 3 3 = 3 from by decide,
        show (2 : ℤ) ^ 3 = 8 from by norm_num]
    exact hw8

theorem nonlift_sqrt {k : ℕ} (hk : 5 ≤ k) (a : ℤ) (s : ℕ) (w : ℤ)
    (hdec : a ^ 2 - 1 = 2 ^ s * w) (hge : k - 2 ≤ s) :
    a ≡ 1 [ZMOD 2 ^ (k - 2)] ∨ a ≡ -1 [ZMOD 2 ^ (k - 2)]
      ∨ a ≡ 2 ^ (k - 3) - 1 [ZMOD 2 ^ (k - 2)]
      ∨ a ≡ 2 ^ (k - 3) + 1 [ZMOD 2 ^ (k - 2)] := by
  have hdvd : (2 : ℤ) ^ (k - 2) ∣ a ^ 2 - 1 := by
    rw [hdec]; exact (pow_dvd_pow 2 hge).mul_right w
  have hsqrt := sqrt_one_mod_two_pow (k - 2) (by omega) a hdvd
  rwa [show (k - 2) - 1 = k - 3 from by omega] at hsqrt

theorem nonlift_odd_sk1 (k : ℕ) (hk : 5 ≤ k) (a w : ℤ) (ha0 : 0 ≤ a) (ha : a < (2 : ℤ) ^ k)
    (hw : Odd w) (hw4 : ¬ w ≡ 1 [ZMOD 4])
    (hdec : a ^ 2 - 1 = (2 : ℤ) ^ (k - 1) * w) :
    a = 2 ^ (k - 2) - 1 ∨ a = 3 * 2 ^ (k - 2) + 1 := by
  have hf : (2 : ℤ) ^ (k - 2) = 2 * (2 : ℤ) ^ (k - 3) := by rw [← pow_succ']; congr 1; omega
  have h1 : (2 : ℤ) ^ (k - 1) = 4 * (2 : ℤ) ^ (k - 3) := by
    rw [show (4 : ℤ) = 2 ^ 2 from by norm_num, ← pow_add]; congr 1; omega
  have hk8 : (2 : ℤ) ^ k = 8 * (2 : ℤ) ^ (k - 3) := by
    rw [show (8 : ℤ) = 2 ^ 3 from by norm_num, ← pow_add]; congr 1; omega
  set g : ℤ := (2 : ℤ) ^ (k - 3) with hg_def
  have hg4 : (4 : ℤ) ∣ g := by
    rw [hg_def, show (4 : ℤ) = 2 ^ 2 from by norm_num]; exact pow_dvd_pow 2 (by omega)
  have hgpos : (0 : ℤ) < g := by rw [hg_def]; positivity
  have h4g : (4 : ℤ) * g ≠ 0 := by positivity
  have hw3 : w % 4 = 3 := by
    have ho : w % 2 = 1 := Int.odd_iff.mp hw
    have hn : w % 4 ≠ 1 := by simpa [Int.ModEq] using hw4
    omega
  have hdvd : (2 : ℤ) ^ (k - 1) ∣ a ^ 2 - 1 := ⟨w, hdec⟩
  have hroots := sqrt_one_mod_two_pow (k - 1) (by omega) a hdvd
  rw [show (k - 1) - 1 = k - 2 from by omega] at hroots
  rw [hf] at hroots
  rw [h1] at hroots hdec
  rcases hroots with hroot | hroot | hroot | hroot
  · exfalso
    obtain ⟨q, hq⟩ := Int.modEq_iff_dvd.mp hroot
    have ha_eq : a = 1 - 4 * g * q := by linarith
    have hw_eq : w = -2 * q + 4 * g * q ^ 2 := by
      apply mul_left_cancel₀ h4g; rw [← hdec, ha_eq]; ring
    have h2w : (2 : ℤ) ∣ w := ⟨-q + 2 * g * q ^ 2, by rw [hw_eq]; ring⟩
    rw [Int.odd_iff] at hw; omega
  · exfalso
    obtain ⟨q, hq⟩ := Int.modEq_iff_dvd.mp hroot
    have ha_eq : a = -1 - 4 * g * q := by linarith
    have hw_eq : w = 2 * q + 4 * g * q ^ 2 := by
      apply mul_left_cancel₀ h4g; rw [← hdec, ha_eq]; ring
    have h2w : (2 : ℤ) ∣ w := ⟨q + 2 * g * q ^ 2, by rw [hw_eq]; ring⟩
    rw [Int.odd_iff] at hw; omega
  · obtain ⟨q, hq⟩ := Int.modEq_iff_dvd.mp hroot
    have ha_eq : a = 2 * g - 1 - 4 * g * q := by linarith
    have hw_eq : w = g - 1 - 2 * q * (2 * g - 1) + 4 * g * q ^ 2 := by
      apply mul_left_cancel₀ h4g; rw [← hdec, ha_eq]; ring
    have hdvd4 : (4 : ℤ) ∣ (w - (2 * q - 1)) := by
      have hID : w - (2 * q - 1) = g * (1 - 2 * q) ^ 2 := by rw [hw_eq]; ring
      rw [hID]; exact Dvd.dvd.mul_right hg4 _
    have hqlt : q < 1 := by
      have h' : 4 * g * q < 4 * g * 1 := by linarith [ha0, ha_eq, hgpos]
      exact lt_of_mul_lt_mul_left h' (by positivity)
    have hqgt : -2 < q := by
      have h' : 4 * g * (-2) < 4 * g * q := by linarith [ha, hk8, ha_eq, hgpos]
      exact lt_of_mul_lt_mul_left h' (by positivity)
    have hqv : q = 0 := by omega
    left; rw [ha_eq, hqv, hf]; ring
  · obtain ⟨q, hq⟩ := Int.modEq_iff_dvd.mp hroot
    have ha_eq : a = 2 * g + 1 - 4 * g * q := by linarith
    have hw_eq : w = g + 1 - 2 * q * (2 * g + 1) + 4 * g * q ^ 2 := by
      apply mul_left_cancel₀ h4g; rw [← hdec, ha_eq]; ring
    have hdvd4 : (4 : ℤ) ∣ (w - (1 - 2 * q)) := by
      have hID : w - (1 - 2 * q) = g * (1 - 2 * q) ^ 2 := by rw [hw_eq]; ring
      rw [hID]; exact Dvd.dvd.mul_right hg4 _
    have hqlt : q < 1 := by
      have h' : 4 * g * q < 4 * g * 1 := by linarith [ha0, ha_eq, hgpos]
      exact lt_of_mul_lt_mul_left h' (by positivity)
    have hqgt : -2 < q := by
      have h' : 4 * g * (-2) < 4 * g * q := by linarith [ha, hk8, ha_eq, hgpos]
      exact lt_of_mul_lt_mul_left h' (by positivity)
    have hqv : q = -1 := by omega
    right; rw [ha_eq, hqv, hf]; ring

theorem nonlift_odd_sk (k : ℕ) (hk : 5 ≤ k) (a w : ℤ) (ha0 : 0 ≤ a) (ha : a < (2 : ℤ) ^ k)
    (hw : Odd w) (hdec : a ^ 2 - 1 = (2 : ℤ) ^ k * w) :
    a = 2 ^ (k - 1) - 1 ∨ a = 2 ^ (k - 1) + 1 := by
  have h2k : (2 : ℤ) ^ k = 2 * (2 : ℤ) ^ (k - 1) := by rw [← pow_succ']; congr 1; omega
  have hpos : (0 : ℤ) < (2 : ℤ) ^ (k - 1) := by positivity
  have hkpos : (0 : ℤ) < (2 : ℤ) ^ k := by positivity
  -- 2 ≤ 2^(k-1): без лемм о монотонности, через 2^(k-1) = 2·2^(k-2)
  have h2k1 : (2 : ℤ) ^ (k - 1) = 2 * (2 : ℤ) ^ (k - 2) := by rw [← pow_succ']; congr 1; omega
  have hpos2 : (0 : ℤ) < (2 : ℤ) ^ (k - 2) := by positivity
  have h1 : (2 : ℤ) ≤ (2 : ℤ) ^ (k - 1) := by rw [h2k1]; linarith [hpos2]
  -- единственный представитель: a ≡ r mod 2^k, 0≤r<2^k, 0≤a<2^k ⇒ a=r
  have uniq : ∀ r : ℤ, 0 ≤ r → r < (2 : ℤ) ^ k → a ≡ r [ZMOD 2 ^ k] → a = r := by
    intro r hr0 hr1 hcong
    obtain ⟨q, hq⟩ := Int.modEq_iff_dvd.mp hcong
    have hqlt : q < 1 := by
      have h' : (2 : ℤ) ^ k * q < (2 : ℤ) ^ k * 1 := by linarith [ha0, hr1, hq]
      exact lt_of_mul_lt_mul_left h' (le_of_lt hkpos)
    have hqgt : -1 < q := by
      have h' : (2 : ℤ) ^ k * (-1) < (2 : ℤ) ^ k * q := by linarith [ha, hr0, hq]
      exact lt_of_mul_lt_mul_left h' (le_of_lt hkpos)
    have : q = 0 := by omega
    rw [this] at hq; linarith
  have hdvd : (2 : ℤ) ^ k ∣ a ^ 2 - 1 := ⟨w, hdec⟩
  have hroots := sqrt_one_mod_two_pow k (by omega) a hdvd
  rcases hroots with hroot | hroot | hroot | hroot
  · -- a = 1 ⇒ w = 0
    exfalso
    have ha1 : a = 1 := uniq 1 (by norm_num) (by rw [h2k]; linarith [h1]) hroot
    rw [ha1] at hdec
    have hz : (2 : ℤ) ^ k * w = 0 := by linarith [hdec]
    rcases mul_eq_zero.mp hz with h | h
    · exact absurd h (by positivity)
    · rw [h] at hw; exact (by decide : ¬ Odd (0 : ℤ)) hw
  · -- a = 2^k - 1 ⇒ w = 2(2^{k-1}-1) чётно
    exfalso
    have hc : a ≡ 2 ^ k - 1 [ZMOD 2 ^ k] :=
      hroot.trans (Int.modEq_iff_dvd.mpr ⟨1, by ring⟩)
    have ha1 : a = 2 ^ k - 1 := uniq _ (by linarith [hkpos]) (by linarith [hkpos]) hc
    have hwe : w = 2 * (2 ^ (k - 1) - 1) := by
      apply mul_left_cancel₀ (show (2 : ℤ) ^ k ≠ 0 by positivity)
      rw [← hdec, ha1, h2k]; ring
    have h2w : (2 : ℤ) ∣ w := ⟨2 ^ (k - 1) - 1, hwe⟩
    rw [Int.odd_iff] at hw; omega
  · left
    exact uniq _ (by linarith [h1]) (by rw [h2k]; linarith [h1]) hroot
  · right
    exact uniq _ (by linarith [h1]) (by rw [h2k]; linarith [h1]) hroot

theorem nonlift_even_candidates (k : ℕ) (hk : 8 ≤ k) (he : Even k)
    (a w : ℤ) (ha0 : 0 ≤ a) (ha : a < (2 : ℤ) ^ k)
    (hw : Odd w) (hw4 : w ≡ 1 [ZMOD 4]) (hw8 : ¬ w ≡ 1 [ZMOD 8])
    (hdec : a ^ 2 - 1 = (2 : ℤ) ^ (k - 2) * w) :
    a = 3 * (2 : ℤ) ^ (k - 3) - 1 ∨ a = 5 * (2 : ℤ) ^ (k - 3) + 1 := by
  have hd : (2 : ℤ) ^ (k - 3) = 2 * (2 : ℤ) ^ (k - 4) := by
    rw [← pow_succ']; congr 1; omega
  have h2 : (2 : ℤ) ^ (k - 2) = 4 * (2 : ℤ) ^ (k - 4) := by
    rw [show (4 : ℤ) = 2 ^ 2 from by norm_num, ← pow_add]; congr 1; omega
  have hkp : (2 : ℤ) ^ k = 16 * (2 : ℤ) ^ (k - 4) := by
    rw [show (16 : ℤ) = 2 ^ 4 from by norm_num, ← pow_add]; congr 1; omega
  set e : ℤ := (2 : ℤ) ^ (k - 4) with he_def
  have he8 : (8 : ℤ) ∣ e := by
    rw [he_def, show (8 : ℤ) = 2 ^ 3 from by norm_num]; exact pow_dvd_pow 2 (by omega)
  have hepos : (0 : ℤ) < e := by rw [he_def]; positivity
  have h4e : (4 : ℤ) * e ≠ 0 := by positivity
  have hw5 : w % 8 = 5 := by
    have h4 : w % 4 = 1 := by simpa [Int.ModEq] using hw4
    have h8 : w % 8 ≠ 1 := by simpa [Int.ModEq] using hw8
    omega
  have hroots := nonlift_sqrt (by omega : 5 ≤ k) a (k - 2) w hdec (by omega)
  rw [hd] at hroots
  rw [h2] at hroots hdec
  rcases hroots with hroot | hroot | hroot | hroot
  · -- a ≡ 1 : w чётно, противоречие
    exfalso
    obtain ⟨q, hq⟩ := Int.modEq_iff_dvd.mp hroot
    have ha_eq : a = 1 - 4 * e * q := by linarith
    have hw_eq : w = -2 * q + 4 * e * q ^ 2 := by
      apply mul_left_cancel₀ h4e; rw [← hdec, ha_eq]; ring
    have h2w : (2 : ℤ) ∣ w := ⟨-q + 2 * e * q ^ 2, by rw [hw_eq]; ring⟩
    rw [Int.odd_iff] at hw; omega
  · -- a ≡ -1 : w чётно, противоречие
    exfalso
    obtain ⟨q, hq⟩ := Int.modEq_iff_dvd.mp hroot
    have ha_eq : a = -1 - 4 * e * q := by linarith
    have hw_eq : w = 2 * q + 4 * e * q ^ 2 := by
      apply mul_left_cancel₀ h4e; rw [← hdec, ha_eq]; ring
    have h2w : (2 : ℤ) ∣ w := ⟨q + 2 * e * q ^ 2, by rw [hw_eq]; ring⟩
    rw [Int.odd_iff] at hw; omega
  · -- a ≡ 2e-1 : пиннит q=-1 ⇒ a = 3·2^{k-3}-1
    obtain ⟨q, hq⟩ := Int.modEq_iff_dvd.mp hroot
    have ha_eq : a = 2 * e - 1 - 4 * e * q := by linarith
    have hw_eq : w = e - 1 - 2 * q * (2 * e - 1) + 4 * e * q ^ 2 := by
      apply mul_left_cancel₀ h4e; rw [← hdec, ha_eq]; ring
    have hdvd8 : (8 : ℤ) ∣ (w - (2 * q - 1)) := by
      have hID : w - (2 * q - 1) = e * (1 - 2 * q) ^ 2 := by rw [hw_eq]; ring
      rw [hID]; exact Dvd.dvd.mul_right he8 _
    have hqlt : q < 1 := by
      have h' : 4 * e * q < 4 * e * 1 := by linarith [ha0, ha_eq, hepos]
      exact lt_of_mul_lt_mul_left h' (by positivity)
    have hqgt : -4 < q := by
      have h' : 4 * e * (-4) < 4 * e * q := by linarith [ha, hkp, ha_eq, hepos]
      exact lt_of_mul_lt_mul_left h' (by positivity)
    have hqv : q = -1 := by omega
    left; rw [ha_eq, hqv, hd]; ring
  · -- a ≡ 2e+1 : пиннит q=-2 ⇒ a = 5·2^{k-3}+1
    obtain ⟨q, hq⟩ := Int.modEq_iff_dvd.mp hroot
    have ha_eq : a = 2 * e + 1 - 4 * e * q := by linarith
    have hw_eq : w = e + 1 - 2 * q * (2 * e + 1) + 4 * e * q ^ 2 := by
      apply mul_left_cancel₀ h4e; rw [← hdec, ha_eq]; ring
    have hdvd8 : (8 : ℤ) ∣ (w - (1 - 2 * q)) := by
      have hID : w - (1 - 2 * q) = e * (1 - 2 * q) ^ 2 := by rw [hw_eq]; ring
      rw [hID]; exact Dvd.dvd.mul_right he8 _
    have hqlt : q < 1 := by
      have h' : 4 * e * q < 4 * e * 1 := by linarith [ha0, ha_eq, hepos]
      exact lt_of_mul_lt_mul_left h' (by positivity)
    have hqgt : -4 < q := by
      have h' : 4 * e * (-4) < 4 * e * q := by linarith [ha, hkp, ha_eq, hepos]
      exact lt_of_mul_lt_mul_left h' (by positivity)
    have hqv : q = -2 := by omega
    right; rw [ha_eq, hqv, hd]; ring

#print axioms nonlift_sqrt

noncomputable def nonliftNatSet (k : ℕ) : Finset ℕ :=
  if Even k then
    if k = 6 then {9, 55}
    else {3 * 2 ^ (k - 3) - 1, 5 * 2 ^ (k - 3) + 1}
  else {2 ^ (k - 1) - 1, 2 ^ (k - 1) + 1,
    2 ^ (k - 2) - 1, 3 * 2 ^ (k - 2) + 1}

noncomputable def nonliftSet (k : ℕ) : Finset (ZMod (2 ^ k)) :=
  (nonliftNatSet k).image (fun n : ℕ => (n : ZMod (2 ^ k)))

private theorem nonliftNatSet_bounds_card (k : ℕ) (hk : 5 ≤ k) :
    (∀ n ∈ nonliftNatSet k, n < 2 ^ k) ∧
    (nonliftNatSet k).card = if Even k then 2 else 4 := by
  have hq : 4 ≤ (2 : ℕ) ^ (k - 3) := by
    calc
      4 = (2 : ℕ) ^ 2 := by norm_num
      _ ≤ 2 ^ (k - 3) := Nat.pow_le_pow_right (by decide) (by omega)
  have h1 : (2 : ℕ) ^ (k - 1) = 4 * 2 ^ (k - 3) := by
    rw [show k - 1 = (k - 3) + 2 by omega, pow_add]; ring
  have h2 : (2 : ℕ) ^ (k - 2) = 2 * 2 ^ (k - 3) := by
    rw [show k - 2 = (k - 3) + 1 by omega, pow_add]; ring
  have h3 : (2 : ℕ) ^ k = 8 * 2 ^ (k - 3) := by
    calc
      2 ^ k = (2 : ℕ) ^ ((k - 3) + 3) := congrArg (fun n : ℕ => (2 : ℕ) ^ n) (by omega)
      _ = 8 * 2 ^ (k - 3) := by rw [pow_add]; ring
  by_cases he : Even k
  · by_cases h6 : k = 6
    · subst k; norm_num [nonliftNatSet]
    · rw [nonliftNatSet, if_pos he, if_neg h6, if_pos he]
      constructor
      · intro n hn
        simp only [Finset.mem_insert, Finset.mem_singleton] at hn
        rw [h3]; rcases hn with rfl | rfl <;> omega
      · rw [Finset.card_pair (by omega)]
  · rw [nonliftNatSet, if_neg he, if_neg he, h1, h2]
    have hne1 : 4 * 2 ^ (k - 3) - 1 ≠ 4 * 2 ^ (k - 3) + 1 := by omega
    have hne2 : 4 * 2 ^ (k - 3) - 1 ≠ 2 * 2 ^ (k - 3) - 1 := by omega
    have hne3 : 4 * 2 ^ (k - 3) - 1 ≠ 3 * (2 * 2 ^ (k - 3)) + 1 := by omega
    have hne4 : 4 * 2 ^ (k - 3) + 1 ≠ 2 * 2 ^ (k - 3) - 1 := by omega
    have hne5 : 4 * 2 ^ (k - 3) + 1 ≠ 3 * (2 * 2 ^ (k - 3)) + 1 := by omega
    have hne6 : 2 * 2 ^ (k - 3) - 1 ≠ 3 * (2 * 2 ^ (k - 3)) + 1 := by omega
    constructor
    · intro n hn
      simp only [Finset.mem_insert, Finset.mem_singleton] at hn
      rw [h3]; rcases hn with rfl | rfl | rfl | rfl <;> omega
    · rw [Finset.card_insert_of_notMem (by simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using And.intro hne1 (And.intro hne2 hne3))]
      rw [Finset.card_insert_of_notMem (by simpa only [Finset.mem_insert, Finset.mem_singleton, not_or] using And.intro hne4 hne5)]
      rw [Finset.card_pair hne6]

theorem nonliftSet_card (k : ℕ) (hk : 5 ≤ k) :
    (nonliftSet k).card = if Even k then 2 else 4 := by
  obtain ⟨hb, hc⟩ := nonliftNatSet_bounds_card k hk
  rw [nonliftSet, Finset.card_image_iff.mpr]
  · exact hc
  · intro a ha b hb' hab
    have h := (ZMod.natCast_eq_natCast_iff' a b (2 ^ k)).mp hab
    simpa only [Nat.mod_eq_of_lt (hb a ha), Nat.mod_eq_of_lt (hb b hb')] using h

#print axioms nonliftSet_card

open scoped Classical in
private theorem nonlift_of_case {k s : ℕ} (hk : 5 ≤ k) (b : ZMod (2 ^ k))
    (w : ℤ) (hw : Odd w) (hd : (b.val : ℤ) ^ 2 - 1 = 2 ^ s * w)
    (hc : (s = k ∧ Odd k) ∨ (s = k - 1 ∧ Odd k ∧ ¬ w ≡ 1 [ZMOD 4]) ∨
      (s = k - 2 ∧ Even k ∧ w ≡ 1 [ZMOD 4] ∧ ¬ w ≡ 1 [ZMOD 8])) :
    IsSquare (b ^ 2 - ((1 : ℤ) : ZMod (2 ^ k))) ∧
      ¬ IsSquare (((b.val : ℤ) : ZMod (2 ^ (k + 1))) ^ 2 - ((1 : ℤ) : ZMod (2 ^ (k + 1)))) := by
  apply (nonlift_iff_val b s w hw hd).mpr
  have hw2 : w ≡ 1 [ZMOD 2] := Int.modEq_iff_dvd.mpr (by
    obtain ⟨t, ht⟩ := hw
    exact ⟨-t, by rw [ht]; ring⟩)
  rcases hc with ⟨hs, ho⟩ | ⟨hs, ho, hn4⟩ | ⟨hs, he, h4, hn8⟩
  · subst s
    refine ⟨Or.inl le_rfl, ?_⟩
    rintro (hle | ⟨hev, _⟩)
    · omega
    · exact (Nat.not_even_iff_odd.mpr ho) hev
  · subst s
    have hev : Even (k - 1) := by rw [Nat.even_iff]; have := Nat.odd_iff.mp ho; omega
    refine ⟨Or.inr ⟨hev, ?_⟩, ?_⟩
    · simpa [show k - (k - 1) = 1 by omega] using hw2
    · rintro (hle | ⟨_, h4⟩)
      · omega
      · apply hn4
        simpa [show k + 1 - (k - 1) = 2 by omega] using h4
  · subst s
    have hev : Even (k - 2) := by rw [Nat.even_iff]; have := Nat.even_iff.mp he; omega
    refine ⟨Or.inr ⟨hev, ?_⟩, ?_⟩
    · simpa [show k - (k - 2) = 2 by omega] using h4
    · rintro (hle | ⟨_, h8⟩)
      · omega
      · apply hn8
        simpa [show k + 1 - (k - 2) = 3 by omega] using h8

open scoped Classical in
private theorem nonliftSet_mem_nonlift {k : ℕ} (hk : 5 ≤ k) (h6 : k ≠ 6)
    (b : ZMod (2 ^ k)) (hb : b ∈ nonliftSet k) :
    IsSquare (b ^ 2 - ((1 : ℤ) : ZMod (2 ^ k))) ∧
      ¬ IsSquare (((b.val : ℤ) : ZMod (2 ^ (k + 1))) ^ 2 - ((1 : ℤ) : ZMod (2 ^ (k + 1)))) := by
  have apply_data (n s : ℕ) (w : ℤ) (hn : n ∈ nonliftNatSet k)
      (hw : Odd w) (hd : (n : ℤ) ^ 2 - 1 = 2 ^ s * w)
      (hc : (s = k ∧ Odd k) ∨ (s = k - 1 ∧ Odd k ∧ ¬ w ≡ 1 [ZMOD 4]) ∨
        (s = k - 2 ∧ Even k ∧ w ≡ 1 [ZMOD 4] ∧ ¬ w ≡ 1 [ZMOD 8])) :
      IsSquare ((n : ZMod (2 ^ k)) ^ 2 - ((1 : ℤ) : ZMod (2 ^ k))) ∧
        ¬ IsSquare (((((n : ZMod (2 ^ k)).val) : ℤ) : ZMod (2 ^ (k + 1))) ^ 2 - ((1 : ℤ) : ZMod (2 ^ (k + 1)))) := by
    apply nonlift_of_case hk _ w hw _ hc
    simpa only [ZMod.val_natCast_of_lt ((nonliftNatSet_bounds_card k hk).1 n hn)] using hd
  obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hb
  by_cases he : Even k
  · have hk8 : 8 ≤ k := by have := Nat.even_iff.mp he; omega
    have hq8 : (8 : ℤ) ∣ 2 ^ (k - 4) := by
      rw [show (8 : ℤ) = 2 ^ 3 from by norm_num]
      exact pow_dvd_pow 2 (by omega)
    obtain ⟨t, ht⟩ := hq8
    have hd : (2 : ℤ) ^ (k - 3) = 2 * 2 ^ (k - 4) := by
      rw [← pow_succ']; congr 1; omega
    have hs : (2 : ℤ) ^ (k - 2) = 4 * 2 ^ (k - 4) := by
      rw [show (4 : ℤ) = 2 ^ 2 by norm_num, ← pow_add]; congr 1; omega
    have hn' := hn
    simp only [nonliftNatSet, if_pos he, if_neg h6, Finset.mem_insert, Finset.mem_singleton] at hn'
    rcases hn' with rfl | rfl
    · refine apply_data _ (k - 2) (3 * (3 * (2 : ℤ) ^ (k - 4) - 1)) hn ?_ ?_ ?_
      · rw [Int.odd_iff]; omega
      · simp only [Nat.cast_sub (by positivity : 0 < 3 * 2 ^ (k - 3)), Nat.cast_mul,
          Nat.cast_pow, Nat.cast_ofNat]
        rw [hd, hs]; ring
      · right; right
        refine ⟨rfl, he, ?_, ?_⟩ <;> rw [Int.modEq_iff_dvd] <;> omega
    · refine apply_data _ (k - 2) (5 * (5 * (2 : ℤ) ^ (k - 4) + 1)) hn ?_ ?_ ?_
      · rw [Int.odd_iff]; omega
      · simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
        rw [hd, hs]; ring
      · right; right
        refine ⟨rfl, he, ?_, ?_⟩ <;> rw [Int.modEq_iff_dvd] <;> omega
  · have ho : Odd k := Nat.not_even_iff_odd.mp he
    have hq4 : (4 : ℤ) ∣ 2 ^ (k - 3) := by
      rw [show (4 : ℤ) = 2 ^ 2 from by norm_num]
      exact pow_dvd_pow 2 (by omega)
    obtain ⟨t, ht⟩ := hq4
    have h1 : (2 : ℤ) ^ (k - 1) = 4 * 2 ^ (k - 3) := by
      rw [show (4 : ℤ) = 2 ^ 2 by norm_num, ← pow_add]; congr 1; omega
    have h2 : (2 : ℤ) ^ (k - 2) = 2 * 2 ^ (k - 3) := by
      rw [← pow_succ']; congr 1; omega
    have htop : (2 : ℤ) ^ k = 8 * 2 ^ (k - 3) := by
      calc
        _ = (2 : ℤ) ^ ((k - 3) + 3) := congrArg (fun n : ℕ => (2 : ℤ) ^ n) (by omega)
        _ = _ := by rw [pow_add]; ring
    have hn' := hn
    simp only [nonliftNatSet, if_neg he, Finset.mem_insert, Finset.mem_singleton] at hn'
    rcases hn' with rfl | rfl | rfl | rfl
    · refine apply_data _ k (2 * (2 : ℤ) ^ (k - 3) - 1) hn ?_ ?_ ?_
      · exact ⟨2 ^ (k - 3) - 1, by ring⟩
      · simp only [Nat.cast_sub (by positivity : 0 < 2 ^ (k - 1)), Nat.cast_pow, Nat.cast_ofNat]
        rw [h1, htop]; ring
      · exact Or.inl ⟨rfl, ho⟩
    · refine apply_data _ k (2 * (2 : ℤ) ^ (k - 3) + 1) hn ?_ ?_ ?_
      · exact ⟨2 ^ (k - 3), by ring⟩
      · simp only [Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
        rw [h1, htop]; ring
      · exact Or.inl ⟨rfl, ho⟩
    · refine apply_data _ (k - 1) ((2 : ℤ) ^ (k - 3) - 1) hn ?_ ?_ ?_
      · rw [Int.odd_iff]; omega
      · simp only [Nat.cast_sub (by positivity : 0 < 2 ^ (k - 2)), Nat.cast_pow, Nat.cast_ofNat]
        rw [h1, h2]; ring
      · right; left
        refine ⟨rfl, ho, ?_⟩
        rw [Int.modEq_iff_dvd]; omega
    · refine apply_data _ (k - 1) (3 * (3 * (2 : ℤ) ^ (k - 3) + 1)) hn ?_ ?_ ?_
      · rw [Int.odd_iff]; omega
      · simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
        rw [h1, h2]; ring
      · right; left
        refine ⟨rfl, ho, ?_⟩
        rw [Int.modEq_iff_dvd]; omega

open scoped Classical in
set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem nonlift_set_eq (k : ℕ) (hk : 5 ≤ k) :
    (Finset.univ.filter (fun b : ZMod (2 ^ k) =>
      IsSquare (b ^ 2 - ((1 : ℤ) : ZMod (2 ^ k))) ∧
      ¬ IsSquare (((b.val : ℤ) : ZMod (2 ^ (k + 1))) ^ 2 - ((1 : ℤ) : ZMod (2 ^ (k + 1)))))) = nonliftSet k := by
  classical
  by_cases h6 : k = 6
  · subst k
    norm_num only [nonliftSet, nonliftNatSet, show Even 6 by decide, if_true,
      Finset.image_insert, Finset.image_singleton]
    decide
  haveI : NeZero (2 ^ k) := ⟨pow_ne_zero _ two_ne_zero⟩
  ext b
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hb
    have h8 : (8 : ℕ) ∣ 2 ^ k := by
      rw [show (8 : ℕ) = 2 ^ 3 by norm_num]; exact pow_dvd_pow 2 (by omega)
    have hunit := one_pass_image_isUnit h8 1 (Int.ModEq.refl 1) b hb.1
    have hcast : ZMod.castHom h8 (ZMod 8) b = (b.val : ZMod 8) := by
      rw [ZMod.castHom_apply]; exact (ZMod.natCast_val b).symm
    rw [hcast] at hunit
    have key : ∀ x : ZMod 8, IsUnit x → Odd (x.val : ℤ) := by decide
    have hodd8 := key _ hunit
    rw [ZMod.val_natCast] at hodd8
    have hodd : Odd (b.val : ℤ) := by
      have hn : (b.val % 8) % 2 = 1 := by exact_mod_cast (Int.odd_iff.mp hodd8)
      apply Int.odd_iff.mpr
      omega
    have hne : (b.val : ℤ) ^ 2 - 1 ≠ 0 := by
      intro hz
      apply hb.2
      have hz' := congrArg (fun z : ℤ => (z : ZMod (2 ^ (k + 1)))) hz
      have hzero : ((b.val : ℤ) : ZMod (2 ^ (k + 1))) ^ 2
          - ((1 : ℤ) : ZMod (2 ^ (k + 1))) = 0 := by
        push_cast at hz' ⊢; exact hz'
      rw [hzero]; exact ⟨0, by ring⟩
    obtain ⟨w, hw, _, hd⟩ := odd_sq_sub_one_decomp (b.val : ℤ) hodd hne
    set s := padicValInt 2 ((b.val : ℤ) ^ 2 - 1) with hsdef
    have hp := (nonlift_iff_val b s w hw hd).mp hb
    have hge := nonlift_imp_s_ge w hk hp
    have hc := nonlift_cases w hk hw hge hp
    have ha0 : (0 : ℤ) ≤ b.val := by positivity
    have ha : (b.val : ℤ) < (2 : ℤ) ^ k := by exact_mod_cast b.val_lt
    have mem_of_eq (n : ℕ) (hn : n ∈ nonliftNatSet k) (hnval : (b.val : ℤ) = (n : ℤ)) :
        b ∈ nonliftSet k := by
      have hn' : b.val = n := by exact_mod_cast hnval
      apply Finset.mem_image.mpr
      refine ⟨n, hn, ?_⟩
      rw [← hn']; exact ZMod.natCast_zmod_val b
    rcases hc with ⟨hs, ho⟩ | ⟨hs, ho, hw4⟩ | ⟨hs, he, hw4, hw8⟩
    · have he : ¬ Even k := Nat.not_even_iff_odd.mpr ho
      rw [hs] at hd
      rcases nonlift_odd_sk k hk (b.val : ℤ) w ha0 ha hw hd with ha' | ha'
      · apply mem_of_eq (2 ^ (k - 1) - 1)
        · simp [nonliftNatSet, he]
        · simpa only [Nat.cast_sub (show (1 : ℕ) ≤ 2 ^ (k - 1) from Nat.one_le_iff_ne_zero.mpr (by positivity)), Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] using ha'
      · apply mem_of_eq (2 ^ (k - 1) + 1)
        · simp [nonliftNatSet, he]
        · simpa only [Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] using ha'
    · have he : ¬ Even k := Nat.not_even_iff_odd.mpr ho
      rw [hs] at hd
      rcases nonlift_odd_sk1 k hk (b.val : ℤ) w ha0 ha hw hw4 hd with ha' | ha'
      · apply mem_of_eq (2 ^ (k - 2) - 1)
        · simp [nonliftNatSet, he]
        · simpa only [Nat.cast_sub (show (1 : ℕ) ≤ 2 ^ (k - 2) from Nat.one_le_iff_ne_zero.mpr (by positivity)), Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] using ha'
      · apply mem_of_eq (3 * 2 ^ (k - 2) + 1)
        · simp [nonliftNatSet, he]
        · simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] using ha'
    · have hk8 : 8 ≤ k := by have := Nat.even_iff.mp he; omega
      rw [hs] at hd
      rcases nonlift_even_candidates k hk8 he (b.val : ℤ) w ha0 ha hw hw4 hw8 hd with ha' | ha'
      · apply mem_of_eq (3 * 2 ^ (k - 3) - 1)
        · simp [nonliftNatSet, he, h6]
        · simpa only [Nat.cast_sub (show (1 : ℕ) ≤ 3 * 2 ^ (k - 3) from Nat.one_le_iff_ne_zero.mpr (by positivity)), Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] using ha'
      · apply mem_of_eq (5 * 2 ^ (k - 3) + 1)
        · simp [nonliftNatSet, he, h6]
        · simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] using ha'
  · exact nonliftSet_mem_nonlift hk h6 b


open scoped Classical in
/-- Подсчёт «неподнимающихся» проходящих центров для N = 1:
D_k = 2 (чётное k), 4 (нечётное k), при k ≥ 5.  (ЭТО 3.2b-2; доказано.) -/
theorem passCard_one_nonlift_card {k : ℕ} (hk : 5 ≤ k) :
    (Finset.univ.filter (fun b : ZMod (2 ^ k) =>
        IsSquare (b ^ 2 - ((1 : ℤ) : ZMod (2 ^ k))) ∧
        ¬ IsSquare (((b.val : ℤ) : ZMod (2 ^ (k + 1))) ^ 2
                      - ((1 : ℤ) : ZMod (2 ^ (k + 1)))))).card
      = if Even k then 2 else 4 := by
  rw [nonlift_set_eq k hk]
  exact nonliftSet_card k hk

/-- N = 1: `3·C_m = 2^(m-3) + (16 если m чётно, 20 если нечётно)` для m ≥ 5. -/
theorem passCard_one_formula (m : ℕ) (hm : 5 ≤ m) :
    3 * passCard (((1 : ℤ)) : ZMod (2 ^ m))
      = 2 ^ (m - 3) + (if Even m then 16 else 20) := by
  induction m, hm using Nat.le_induction with
  | base =>
    rw [passCard_one_five_base 1 (Int.ModEq.refl 1), if_neg (by decide : ¬ Even 5)]
    norm_num
  | succ k hk ih =>
    have hrec := passCard_succ_sub (by omega : (1 : ℕ) ≤ k) 1
    rw [passCard_one_nonlift_card (by omega : 5 ≤ k)] at hrec
    have e : (2 : ℕ) ^ (k + 1 - 3) = 2 * 2 ^ (k - 3) := by
      rw [show k + 1 - 3 = (k - 3) + 1 from by omega, pow_succ]; ring
    rcases Nat.even_or_odd k with hpar | hpar
    · have hnek1 : ¬ Even (k + 1) := by rw [Nat.even_add_one]; exact not_not.mpr hpar
      rw [if_pos hpar] at hrec ih
      rw [if_neg hnek1]
      omega
    · have hnek : ¬ Even k := by rw [Nat.not_even_iff_odd]; exact hpar
      have hek1 : Even (k + 1) := Nat.even_add_one.mpr hnek
      rw [if_neg hnek] at hrec ih
      rw [if_pos hek1]
      omega

/-- N ≡ 1 (mod 8), even m ≥ 6: 3·C_m(N) = 2^(m-3) + 16. -/
theorem passCard_one_mod_eight_even (N : ℤ) (hN : N ≡ 1 [ZMOD 8]) (m : ℕ)
    (hm : 6 ≤ m) (hpar : Even m) [NeZero (2 ^ m)] :
    3 * passCard ((N : ZMod (2 ^ m))) = 2 ^ (m - 3) + 16 := by
  have hodd : Odd N := by
    have hd : (8 : ℤ) ∣ (1 - N) := Int.modEq_iff_dvd.mp hN
    exact Int.odd_iff.mpr (by omega)
  rw [passCard_eq_of_modEq_eight m N 1 hodd odd_one hN,
      passCard_one_formula m (by omega), if_pos hpar]

/-- N ≡ 1 (mod 8), odd m ≥ 5: 3·C_m(N) = 2^(m-3) + 20. -/
theorem passCard_one_mod_eight_odd (N : ℤ) (hN : N ≡ 1 [ZMOD 8]) (m : ℕ)
    (hm : 5 ≤ m) (hpar : Odd m) [NeZero (2 ^ m)] :
    3 * passCard ((N : ZMod (2 ^ m))) = 2 ^ (m - 3) + 20 := by
  have hodd : Odd N := by
    have hd : (8 : ℤ) ∣ (1 - N) := Int.modEq_iff_dvd.mp hN
    exact Int.odd_iff.mpr (by omega)
  rw [passCard_eq_of_modEq_eight m N 1 hodd odd_one hN,
      passCard_one_formula m (by omega), if_neg (by rw [Nat.not_even_iff_odd]; exact hpar)]

/-- At least one center always passes: `A = (N+1)/2` has `A² − N = ((N−1)/2)²`.
So `C_m(N) ≥ 1` for every odd `N` and every `m`. -/
theorem one_le_passCard (N : ℤ) (hN : Odd N) (m : ℕ) :
    1 ≤ passCard ((N : ZMod (2 ^ m))) := by
  obtain ⟨j, rfl⟩ := hN
  unfold passCard
  rw [Finset.filter_congr_decidable]
  refine Finset.card_pos.mpr ⟨((j + 1 : ℤ) : ZMod (2 ^ m)), ?_⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨((j : ℤ) : ZMod (2 ^ m)), by push_cast; ring⟩

/-- Sharp uniform density π_m(N) > 1/24, i.e. 2^m < 24·C_m(N), for every odd N
and every m. The constant 1/24 is optimal (attained in the limit for N ≡ 1 mod 8).
Corollary of the four closed forms (one per residue class mod 8), with the small
levels handled by `C_m ≥ 1`. -/
theorem passCard_density (N : ℤ) (hN : Odd N) (m : ℕ) [NeZero (2 ^ m)] :
    2 ^ m < 24 * passCard ((N : ZMod (2 ^ m))) := by
  rcases Nat.lt_or_ge m 5 with hm4 | hm5
  · -- small levels (m ≤ 4): 2^m ≤ 16 < 24 ≤ 24·C_m
    have h1 := one_le_passCard N hN m
    have hb : (2 : ℕ) ^ m ≤ 16 := by
      calc (2 : ℕ) ^ m ≤ 2 ^ 4 := by apply Nat.pow_le_pow_right <;> omega
        _ = 16 := by norm_num
    omega
  · have hodd8 : N % 8 = 1 ∨ N % 8 = 3 ∨ N % 8 = 5 ∨ N % 8 = 7 := by
      have := Int.odd_iff.mp hN
      omega
    rcases hodd8 with h8 | h8 | h8 | h8
    · -- N ≡ 1 (mod 8)
      have h1m : N ≡ 1 [ZMOD 8] := Int.modEq_iff_dvd.mpr (by omega)
      have e1 : (2 : ℕ) ^ m = 2 ^ (m - 3) * 8 := by
        rw [show (8 : ℕ) = 2 ^ 3 from rfl, ← pow_add]; congr 1; omega
      rcases Nat.even_or_odd m with hpar | hpar
      · have hm6 : 6 ≤ m := by have := Nat.even_iff.mp hpar; omega
        have h := passCard_one_mod_eight_even N h1m m hm6 hpar
        omega
      · have h := passCard_one_mod_eight_odd N h1m m (by omega) hpar
        omega
    · -- N ≡ 3 (mod 8) ⟹ N ≡ 3 (mod 4)
      have h34 : N ≡ 3 [ZMOD 4] := Int.modEq_iff_dvd.mpr (by omega)
      rw [passCard_three_mod_four N h34 m (by omega)]
      have e : (2 : ℕ) ^ m = 2 ^ (m - 2) * 4 := by
        rw [show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_add]; congr 1; omega
      have hp : 0 < (2 : ℕ) ^ (m - 2) := by positivity
      omega
    · -- N ≡ 5 (mod 8)
      have h5 : N ≡ 5 [ZMOD 8] := Int.modEq_iff_dvd.mpr (by omega)
      rw [passCard_five_mod_eight N h5 m (by omega)]
      have e : (2 : ℕ) ^ m = 2 ^ (m - 3) * 8 := by
        rw [show (8 : ℕ) = 2 ^ 3 from rfl, ← pow_add]; congr 1; omega
      have hp : 0 < (2 : ℕ) ^ (m - 3) := by positivity
      omega
    · -- N ≡ 7 (mod 8) ⟹ N ≡ 3 (mod 4)
      have h34 : N ≡ 3 [ZMOD 4] := Int.modEq_iff_dvd.mpr (by omega)
      rw [passCard_three_mod_four N h34 m (by omega)]
      have e : (2 : ℕ) ^ m = 2 ^ (m - 2) * 4 := by
        rw [show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_add]; congr 1; omega
      have hp : 0 < (2 : ℕ) ^ (m - 2) := by positivity
      omega

#print axioms passCard_succ_sub
#print axioms passCard_one_mod_eight_even
#print axioms passCard_one_mod_eight_odd
#print axioms passCard_density

end DyadicShells.ClosedForms
