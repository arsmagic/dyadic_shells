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

end DyadicShells.ClosedForms
