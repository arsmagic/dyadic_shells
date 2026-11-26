/-
Proposition 16 and Corollary 17 of the paper (Version 11.11.04): the two-adic filter on
sparse-offset candidate families, assembled end to end.

MODEL.  A candidate `A = A₀ + z` with `z < 2^b` and `popcount z ≤ t` is encoded by the SET
`S ⊆ {0,…,b-1}` of the bit positions of `z`, so `popcount z = S.card` and `z = Σ_{i∈S} 2^i`
(binary expansion).  The family `F_{b,t}(A₀)` is therefore indexed by
`sparseSets b t = {S ⊆ range b : S.card ≤ t}`.  This is the definition of Hamming weight,
not an extra hypothesis.

CONTENT.
  • `sparse_pass_limit`  (Proposition 16): if passing depends only on `A mod 2^r`, then the
    pass fraction on `F_{b,t}(A₀)` tends to `1` or `0` according as `A₀` passes or not.
  • `cor17_three`, `cor17_seven`, `cor17_five`  (Corollary 17), via the gates of
    `SparseBias.lean`; and the anchor-free special cases.

Everything is over `ℕ`-valued counts and `Nat.choose`; the analytic input is
`SparseBias.choose_pred_ratio_tendsto_zero`.
-/
import Mathlib
import DyadicShells.TwoAdicExact
import ClosedForms
import SparseBias
import SparseBiasAsymp

namespace DyadicShells.SparseFamily

open Finset Filter Topology
open DyadicShells.SparseBias
open scoped Classical

/-! ### The model -/

/-- Bit-position sets of weight `≤ t` inside `{0,…,b-1}`. -/
def sparseSets (b t : ℕ) : Finset (Finset ℕ) :=
  (range (t + 1)).biUnion fun w => powersetCard w (range b)

/-- The offset `z = Σ_{i∈S} 2^i` encoded by a bit-position set. -/
def offset (S : Finset ℕ) : ℕ := ∑ i ∈ S, 2 ^ i

/-- `S` touches one of the `r` lowest bit positions. -/
abbrev Bad (r : ℕ) (S : Finset ℕ) : Prop := ∃ i ∈ S, i < r

open Classical in
/-- Number of members of the family `F_{b,t}(A₀)` whose centre passes `P`. -/
noncomputable def passCount (P : ℕ → Prop) (A₀ b t : ℕ) : ℕ :=
  ((sparseSets b t).filter fun S => P (A₀ + offset S)).card

/-- The pass fraction `P_F = #(F ∩ gate) / |F|`. -/
noncomputable def passFrac (P : ℕ → Prop) (A₀ b t : ℕ) : ℝ :=
  (passCount P A₀ b t : ℝ) / ((sparseSets b t).card : ℝ)

/-! ### Counting -/

theorem mem_sparseSets {b t : ℕ} {S : Finset ℕ} :
    S ∈ sparseSets b t ↔ S ⊆ range b ∧ S.card ≤ t := by
  constructor
  · intro h
    obtain ⟨w, hw, hS⟩ := Finset.mem_biUnion.mp h
    obtain ⟨hS1, hS2⟩ := Finset.mem_powersetCard.mp hS
    have := Finset.mem_range.mp hw
    exact ⟨hS1, by omega⟩
  · rintro ⟨h1, h2⟩
    exact Finset.mem_biUnion.mpr
      ⟨S.card, Finset.mem_range.mpr (by omega), Finset.mem_powersetCard.mpr ⟨h1, rfl⟩⟩

theorem card_sparseSets (b s : ℕ) :
    (sparseSets b s).card = ∑ w ∈ range (s + 1), b.choose w := by
  unfold sparseSets
  rw [Finset.card_biUnion]
  · simp [Finset.card_powersetCard]
  · intro x _ y _ hxy
    change Disjoint (powersetCard x (range b)) (powersetCard y (range b))
    rw [Finset.disjoint_left]
    intro S hx hy
    obtain ⟨_, hx2⟩ := Finset.mem_powersetCard.mp hx
    obtain ⟨_, hy2⟩ := Finset.mem_powersetCard.mp hy
    exact hxy (hx2.symm.trans hy2)

theorem choose_le_card (b t : ℕ) : b.choose t ≤ (sparseSets b t).card := by
  rw [card_sparseSets]
  exact Finset.single_le_sum (f := fun w => b.choose w) (fun _ _ => Nat.zero_le _)
    (Finset.mem_range.mpr (Nat.lt_succ_self t))

theorem card_pos_sparseSets (b t : ℕ) : 0 < (sparseSets b t).card :=
  Finset.card_pos.mpr ⟨∅, mem_sparseSets.mpr ⟨Finset.empty_subset _, by simp⟩⟩

/-- Unimodality on the left half: `C(b,w) ≤ C(b,j)` for `w ≤ j < b/2`. -/
theorem choose_mono_of_le_half {b w j : ℕ} (hwj : w ≤ j) (hj : j < b / 2) :
    b.choose w ≤ b.choose j := by
  induction j, hwj using Nat.le_induction with
  | base => exact le_rfl
  | succ j hwj ih =>
    exact (ih (by omega)).trans (Nat.choose_le_succ_of_lt_half_left (by omega))

/-- Members of the family containing a fixed position `i`: at most `|F_{b,t-1}|`. -/
theorem card_filter_mem_le (b t i : ℕ) (ht : 1 ≤ t) :
    ((sparseSets b t).filter fun S => i ∈ S).card ≤ (sparseSets b (t - 1)).card := by
  apply Finset.card_le_card_of_injOn (fun S => S.erase i)
  · intro S hS
    have hS' : S ∈ (sparseSets b t).filter fun S => i ∈ S := hS
    obtain ⟨hS1, hi⟩ := Finset.mem_filter.mp hS'
    obtain ⟨h1, h2⟩ := mem_sparseSets.mp hS1
    show S.erase i ∈ sparseSets b (t - 1)
    refine mem_sparseSets.mpr ⟨(Finset.erase_subset i S).trans h1, ?_⟩
    rw [Finset.card_erase_of_mem hi]
    omega
  · intro S hS T hT h
    have hS' : S ∈ (sparseSets b t).filter fun S => i ∈ S := hS
    have hT' : T ∈ (sparseSets b t).filter fun S => i ∈ S := hT
    have hSi := (Finset.mem_filter.mp hS').2
    have hTi := (Finset.mem_filter.mp hT').2
    have h' : S.erase i = T.erase i := h
    calc S = insert i (S.erase i) := (Finset.insert_erase hSi).symm
      _ = insert i (T.erase i) := by rw [h']
      _ = T := Finset.insert_erase hTi

/-- Members of the family touching the `r` lowest positions: at most `r · |F_{b,t-1}|`. -/
theorem card_bad_le (b t r : ℕ) (ht : 1 ≤ t) :
    ((sparseSets b t).filter (Bad r)).card ≤ r * (sparseSets b (t - 1)).card := by
  have hsub : (sparseSets b t).filter (Bad r) ⊆
      (range r).biUnion (fun i => (sparseSets b t).filter fun S => i ∈ S) := by
    intro S hS
    obtain ⟨hS1, hB⟩ := Finset.mem_filter.mp hS
    obtain ⟨i, hi, hir⟩ : ∃ i ∈ S, i < r := hB
    exact Finset.mem_biUnion.mpr
      ⟨i, Finset.mem_range.mpr hir, Finset.mem_filter.mpr ⟨hS1, hi⟩⟩
  calc ((sparseSets b t).filter (Bad r)).card
      ≤ ((range r).biUnion (fun i => (sparseSets b t).filter fun S => i ∈ S)).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ i ∈ range r, ((sparseSets b t).filter fun S => i ∈ S).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ i ∈ range r, (sparseSets b (t - 1)).card :=
        Finset.sum_le_sum fun i _ => card_filter_mem_le b t i ht
    _ = r * (sparseSets b (t - 1)).card := by simp

/-- `|F_{b,t-1}| ≤ t · C(b,t-1)` once `2t ≤ b`. -/
theorem card_sparseSets_pred_le (b t : ℕ) (ht : 1 ≤ t) (hb : 2 * t ≤ b) :
    (sparseSets b (t - 1)).card ≤ t * b.choose (t - 1) := by
  rw [card_sparseSets, Nat.sub_add_cancel ht]
  calc ∑ w ∈ range t, b.choose w ≤ ∑ w ∈ range t, b.choose (t - 1) :=
        Finset.sum_le_sum fun w hw =>
          choose_mono_of_le_half (by have := Finset.mem_range.mp hw; omega) (by omega)
    _ = t * b.choose (t - 1) := by simp

/-! ### Analysis: the touching fraction tends to 0 -/

theorem bad_fraction_tendsto_zero (r t : ℕ) (ht : 1 ≤ t) :
    Tendsto (fun b : ℕ =>
      (((sparseSets b t).filter (Bad r)).card : ℝ) / ((sparseSets b t).card : ℝ))
      atTop (𝓝 0) := by
  have hlim : Tendsto (fun b : ℕ =>
      ((r : ℝ) * t) * ((b.choose (t - 1) : ℝ) / (b.choose t : ℝ))) atTop (𝓝 0) := by
    simpa using (choose_pred_ratio_tendsto_zero t ht).const_mul ((r : ℝ) * t)
  refine squeeze_zero' (Eventually.of_forall fun b => by positivity) ?_ hlim
  filter_upwards [eventually_ge_atTop (2 * t)] with b hb
  have hT : (b.choose t : ℝ) ≤ ((sparseSets b t).card : ℝ) := by
    exact_mod_cast choose_le_card b t
  have hCpos : (0 : ℝ) < (b.choose t : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega)
  have hne : (b.choose t : ℝ) ≠ 0 := hCpos.ne'
  have hTpos : (0 : ℝ) < ((sparseSets b t).card : ℝ) := lt_of_lt_of_le hCpos hT
  have hbad : (((sparseSets b t).filter (Bad r)).card : ℝ)
      ≤ (r : ℝ) * ((t : ℝ) * (b.choose (t - 1) : ℝ)) := by
    exact_mod_cast (card_bad_le b t r ht).trans
      (Nat.mul_le_mul_left r (card_sparseSets_pred_le b t ht hb))
  have hrat : ((r : ℝ) * t) * ((b.choose (t - 1) : ℝ) / (b.choose t : ℝ)) * (b.choose t : ℝ)
      = (r : ℝ) * ((t : ℝ) * (b.choose (t - 1) : ℝ)) := by
    field_simp
  have hnn : (0 : ℝ) ≤ ((r : ℝ) * t) * ((b.choose (t - 1) : ℝ) / (b.choose t : ℝ)) := by
    positivity
  rw [div_le_iff₀ hTpos]
  calc (((sparseSets b t).filter (Bad r)).card : ℝ)
      ≤ (r : ℝ) * ((t : ℝ) * (b.choose (t - 1) : ℝ)) := hbad
    _ = ((r : ℝ) * t) * ((b.choose (t - 1) : ℝ) / (b.choose t : ℝ)) * (b.choose t : ℝ) :=
        hrat.symm
    _ ≤ ((r : ℝ) * t) * ((b.choose (t - 1) : ℝ) / (b.choose t : ℝ))
          * ((sparseSets b t).card : ℝ) := mul_le_mul_of_nonneg_left hT hnn

/-! ### Proposition 16 -/

/-- Away from the low `r` positions the offset does not change the residue mod `2^r`. -/
theorem mod_of_not_bad {r : ℕ} {S : Finset ℕ} (h : ¬ Bad r S) (A₀ : ℕ) :
    (A₀ + offset S) % 2 ^ r = A₀ % 2 ^ r := by
  have hd : 2 ^ r ∣ offset S := by
    show 2 ^ r ∣ ∑ i ∈ S, 2 ^ i
    apply Finset.dvd_sum
    intro i hi
    exact pow_dvd_pow 2 (by by_contra hlt; exact h ⟨i, hi, by omega⟩)
  obtain ⟨c, hc⟩ := hd
  rw [hc, Nat.add_mul_mod_self_left]

/-- **Proposition 16.** If whether `A` passes depends only on `A mod 2^r`, then for every
fixed anchor `A₀` and weight bound `t`, the pass fraction on `F_{b,t}(A₀)` tends to `1`
when `A₀` passes and to `0` when it does not. -/
theorem sparse_pass_limit (r : ℕ) (P : ℕ → Prop)
    (hP : ∀ A A' : ℕ, A % 2 ^ r = A' % 2 ^ r → (P A ↔ P A')) (A₀ t : ℕ) :
    Tendsto (fun b : ℕ => passFrac P A₀ b t) atTop (𝓝 (if P A₀ then 1 else 0)) := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · -- t = 0: the family is the single centre `A₀`
    have hs : ∀ b, sparseSets b 0 = {∅} := by
      intro b
      ext S
      rw [mem_sparseSets, Finset.mem_singleton]
      constructor
      · rintro ⟨_, h⟩
        exact Finset.card_eq_zero.mp (Nat.le_zero.mp h)
      · rintro rfl
        simp
    have hconst : ∀ b, passFrac P A₀ b 0 = if P A₀ then 1 else 0 := by
      intro b
      unfold passFrac passCount
      rw [hs]
      rw [Finset.filter_congr_decidable]
      by_cases h : P A₀
      · have hf : ∀ S ∈ ({∅} : Finset (Finset ℕ)), P (A₀ + offset S) := by
          intro S hS
          have hS' := Finset.mem_singleton.mp hS
          subst S
          simpa [offset] using h
        rw [Finset.filter_true_of_mem hf, if_pos h]
        norm_num
      · have hf : ∀ S ∈ ({∅} : Finset (Finset ℕ)), ¬ P (A₀ + offset S) := by
          intro S hS
          have hS' := Finset.mem_singleton.mp hS
          subst S
          simpa [offset] using h
        rw [Finset.filter_false_of_mem hf, if_neg h]
        norm_num
    simp only [hconst]
    exact tendsto_const_nhds
  · have hbad := bad_fraction_tendsto_zero r t ht
    have hT : ∀ b, (0 : ℝ) < ((sparseSets b t).card : ℝ) := fun b => by
      exact_mod_cast card_pos_sparseSets b t
    by_cases hA : P A₀
    · rw [if_pos hA]
      have hg : Tendsto (fun b : ℕ => 1 - (((sparseSets b t).filter (Bad r)).card : ℝ)
          / ((sparseSets b t).card : ℝ)) atTop (𝓝 1) := by
        simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hbad
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le hg tendsto_const_nhds ?_ ?_
      · intro b
        -- T ≤ good + bad
        have hsub : sparseSets b t ⊆
            ((sparseSets b t).filter fun S => P (A₀ + offset S)) ∪
              (sparseSets b t).filter (Bad r) := by
          intro S hS
          by_cases hB : Bad r S
          · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hS, hB⟩)
          · refine Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hS, ?_⟩)
            exact (hP _ _ (mod_of_not_bad hB A₀)).mpr hA
        have hnat : (sparseSets b t).card ≤ passCount P A₀ b t
            + ((sparseSets b t).filter (Bad r)).card :=
          (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
        have hreal : ((sparseSets b t).card : ℝ) ≤ (passCount P A₀ b t : ℝ)
            + (((sparseSets b t).filter (Bad r)).card : ℝ) := by exact_mod_cast hnat
        show 1 - (((sparseSets b t).filter (Bad r)).card : ℝ) / ((sparseSets b t).card : ℝ)
          ≤ passFrac P A₀ b t
        unfold passFrac
        rw [le_div_iff₀ (hT b)]
        have hne : ((sparseSets b t).card : ℝ) ≠ 0 := (hT b).ne'
        have : (1 - (((sparseSets b t).filter (Bad r)).card : ℝ) / ((sparseSets b t).card : ℝ))
            * ((sparseSets b t).card : ℝ)
            = ((sparseSets b t).card : ℝ) - (((sparseSets b t).filter (Bad r)).card : ℝ) := by
          field_simp
        rw [this]
        linarith
      · intro b
        show passFrac P A₀ b t ≤ 1
        unfold passFrac
        rw [div_le_one (hT b)]
        exact_mod_cast Finset.card_filter_le _ _
    · rw [if_neg hA]
      refine squeeze_zero (fun b => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
        (fun b => ?_) hbad
      unfold passFrac passCount
      have hsub : ((sparseSets b t).filter fun S => P (A₀ + offset S)) ⊆
          (sparseSets b t).filter (Bad r) := by
        intro S hS
        obtain ⟨hS1, hPS⟩ := Finset.mem_filter.mp hS
        refine Finset.mem_filter.mpr ⟨hS1, ?_⟩
        by_contra hB
        exact hA ((hP _ _ (mod_of_not_bad hB A₀)).mp hPS)
      exact div_le_div_of_nonneg_right (by exact_mod_cast Finset.card_le_card hsub)
        (hT b).le

/-! ### Corollary 17 -/

/-- `A` passes at level `k` for `N`: `A² − N` is a square in `ZMod (2^k)`. -/
def PassNat (k : ℕ) (N : ℤ) (A : ℕ) : Prop :=
  IsSquare ((A : ZMod (2 ^ k)) ^ 2 - ((N : ℤ) : ZMod (2 ^ k)))

private theorem eight_dvd {k : ℕ} (hk : 3 ≤ k) : (8 : ℕ) ∣ 2 ^ k := by
  have h := pow_dvd_pow (2 : ℕ) hk
  rwa [show (2 : ℕ) ^ 3 = 8 by norm_num] at h

private theorem thirtytwo_dvd {k : ℕ} (hk : 5 ≤ k) : (32 : ℕ) ∣ 2 ^ k := by
  have h := pow_dvd_pow (2 : ℕ) hk
  rwa [show (2 : ℕ) ^ 5 = 32 by norm_num] at h

private theorem zmod8_two_six (A : ℕ) :
    ((A : ZMod 8) = 2 ∨ (A : ZMod 8) = 6) ↔ A % 4 = 2 := by
  have h2 : (2 : ZMod 8) = ((2 : ℕ) : ZMod 8) := by norm_num
  have h6 : (6 : ZMod 8) = ((6 : ℕ) : ZMod 8) := by norm_num
  rw [h2, h6, ZMod.natCast_eq_natCast_iff', ZMod.natCast_eq_natCast_iff']
  omega

private theorem zmod8_zero_four (A : ℕ) :
    ((A : ZMod 8) = 0 ∨ (A : ZMod 8) = 4) ↔ A % 4 = 0 := by
  have h0 : (0 : ZMod 8) = ((0 : ℕ) : ZMod 8) := by norm_num
  have h4 : (4 : ZMod 8) = ((4 : ℕ) : ZMod 8) := by norm_num
  rw [h0, h4, ZMod.natCast_eq_natCast_iff', ZMod.natCast_eq_natCast_iff']
  omega

theorem passNat_three_iff {k : ℕ} (hk : 3 ≤ k) (N : ℤ) (hN : N ≡ 3 [ZMOD 8]) (A : ℕ) :
    PassNat k N A ↔ A % 4 = 2 := by
  have h8 := eight_dvd hk
  unfold PassNat
  rw [gate_three_mod_eight h8 N hN (A : ZMod (2 ^ k)), map_natCast]
  exact zmod8_two_six A

theorem passNat_seven_iff {k : ℕ} (hk : 3 ≤ k) (N : ℤ) (hN : N ≡ 7 [ZMOD 8]) (A : ℕ) :
    PassNat k N A ↔ A % 4 = 0 := by
  have h8 := eight_dvd hk
  unfold PassNat
  rw [gate_seven_mod_eight h8 N hN (A : ZMod (2 ^ k)), map_natCast]
  exact zmod8_zero_four A

theorem passNat_five_iff {k : ℕ} (hk : 5 ≤ k) (N : ℤ) (hN : N ≡ 5 [ZMOD 8]) (A : ℕ) :
    PassNat k N A ↔ (((A : ℤ) ^ 2 - N) % 32 = 4) := by
  have h32 := thirtytwo_dvd hk
  unfold PassNat
  rw [gate_five_mod_eight h32 N hN (A : ZMod (2 ^ k))]
  have hc : ZMod.castHom h32 (ZMod 32)
      ((A : ZMod (2 ^ k)) ^ 2 - ((N : ℤ) : ZMod (2 ^ k)))
      = (((A : ℤ) ^ 2 - N : ℤ) : ZMod 32) := by
    simp [map_sub, map_pow, map_natCast, map_intCast]
  rw [hc, show (4 : ZMod 32) = ((4 : ℤ) : ZMod 32) by norm_num,
    ZMod.intCast_eq_intCast_iff]
  simp [Int.ModEq]

/-- Squares are periodic mod 32 in `a` mod 16. -/
theorem sq_modEq_of_modEq_sixteen {a a' : ℤ} (h : a ≡ a' [ZMOD 16]) :
    a ^ 2 ≡ a' ^ 2 [ZMOD 32] := by
  obtain ⟨q, hq⟩ := Int.modEq_iff_dvd.mp h
  have ha' : a' = a + 16 * q := by linarith
  subst ha'
  exact Int.modEq_iff_dvd.mpr ⟨a * q + 8 * q ^ 2, by ring⟩

/-- **Corollary 17(1), `N ≡ 3 (mod 8)`.** -/
theorem cor17_three {k : ℕ} (hk : 3 ≤ k) (N : ℤ) (hN : N ≡ 3 [ZMOD 8]) (A₀ t : ℕ) :
    Tendsto (fun b : ℕ => passFrac (PassNat k N) A₀ b t) atTop
      (𝓝 (if A₀ % 4 = 2 then 1 else 0)) := by
  have hP : PassNat k N = fun A => A % 4 = 2 := funext fun A => propext (passNat_three_iff hk N hN A)
  rw [hP]
  have hlim := sparse_pass_limit 2 (fun A : ℕ => A % 4 = 2) (fun A A' h => by
    change A % 4 = A' % 4 at h
    rw [h]) A₀ t
  by_cases hA : A₀ % 4 = 2 <;> simpa [hA] using hlim

/-- **Corollary 17(1), `N ≡ 7 (mod 8)`.** -/
theorem cor17_seven {k : ℕ} (hk : 3 ≤ k) (N : ℤ) (hN : N ≡ 7 [ZMOD 8]) (A₀ t : ℕ) :
    Tendsto (fun b : ℕ => passFrac (PassNat k N) A₀ b t) atTop
      (𝓝 (if A₀ % 4 = 0 then 1 else 0)) := by
  have hP : PassNat k N = fun A => A % 4 = 0 := funext fun A => propext (passNat_seven_iff hk N hN A)
  rw [hP]
  have hlim := sparse_pass_limit 2 (fun A : ℕ => A % 4 = 0) (fun A A' h => by
    change A % 4 = A' % 4 at h
    rw [h]) A₀ t
  by_cases hA : A₀ % 4 = 0 <;> simpa [hA] using hlim

/-- **Corollary 17(2), `N ≡ 5 (mod 8)`.** -/
theorem cor17_five {k : ℕ} (hk : 5 ≤ k) (N : ℤ) (hN : N ≡ 5 [ZMOD 8]) (A₀ t : ℕ) :
    Tendsto (fun b : ℕ => passFrac (PassNat k N) A₀ b t) atTop
      (𝓝 (if ((A₀ : ℤ) ^ 2 - N) % 32 = 4 then 1 else 0)) := by
  have hP : PassNat k N = fun A : ℕ => ((A : ℤ) ^ 2 - N) % 32 = 4 :=
    funext fun A => propext (passNat_five_iff hk N hN A)
  rw [hP]
  have hperiod : ∀ A A' : ℕ, A % 2 ^ 4 = A' % 2 ^ 4 →
      ((((A : ℤ) ^ 2 - N) % 32 = 4) ↔ (((A' : ℤ) ^ 2 - N) % 32 = 4)) := by
    intro A A' h
    have h16 : (A : ℤ) ≡ (A' : ℤ) [ZMOD 16] := by
      show (A : ℤ) % 16 = (A' : ℤ) % 16
      simp only [show (2 : ℕ) ^ 4 = 16 by norm_num] at h
      omega
    have hsq : (A : ℤ) ^ 2 % 32 = (A' : ℤ) ^ 2 % 32 := sq_modEq_of_modEq_sixteen h16
    generalize (A : ℤ) ^ 2 = x at *
    generalize (A' : ℤ) ^ 2 = y at *
    omega
  have hlim := sparse_pass_limit 4 (fun A : ℕ => ((A : ℤ) ^ 2 - N) % 32 = 4) hperiod A₀ t
  by_cases hA : ((A₀ : ℤ) ^ 2 - N) % 32 = 4 <;>
    simpa [hA] using hlim

/-- Anchor-free family (`A₀ = 0`): the limit is `1` for `N ≡ 7` and `0` for `N ≡ 3`. -/
theorem cor17_seven_anchorfree {k : ℕ} (hk : 3 ≤ k) (N : ℤ) (hN : N ≡ 7 [ZMOD 8]) (t : ℕ) :
    Tendsto (fun b : ℕ => passFrac (PassNat k N) 0 b t) atTop (𝓝 1) := by
  simpa using cor17_seven hk N hN 0 t

theorem cor17_three_anchorfree {k : ℕ} (hk : 3 ≤ k) (N : ℤ) (hN : N ≡ 3 [ZMOD 8]) (t : ℕ) :
    Tendsto (fun b : ℕ => passFrac (PassNat k N) 0 b t) atTop (𝓝 0) := by
  simpa using cor17_three hk N hN 0 t

end DyadicShells.SparseFamily
