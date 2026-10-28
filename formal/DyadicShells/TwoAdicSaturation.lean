import Mathlib

/-!
# Two-adic square witnesses: a checked starting lemma

Source: Khachatryan v11.0.3, Proposition 4.2, and v11.5.17.

The published saturation theorem states that for odd N ≥ 3, the fraction
of A modulo 2^m such that A² - N is a square is bounded below by
2^(-(2 * v₂((N-1)/2) + 3)), uniformly in m.

This file proves an exact witness for every odd N and every 2-power modulus.
It does **not** yet establish the claimed positive uniform density:
one witness per modulus does not imply a lower bound independent of m.
See THEOREM_MAPPING.md.
-/

namespace DyadicShells

def twoAdicPass (N m A : ℕ) : Prop :=
  ∃ y : ℕ, Nat.ModEq (2 ^ m) (A ^ 2) (N + y ^ 2)

theorem odd_center_witness (k m : ℕ) :
    twoAdicPass (2 * k + 1) m (k + 1) := by
  refine ⟨k, ?_⟩
  have h : (k + 1) ^ 2 = (2 * k + 1) + k ^ 2 := by ring
  change ((k + 1) ^ 2) % (2 ^ m) = ((2 * k + 1) + k ^ 2) % (2 ^ m)
  rw [h]

theorem every_odd_has_twoAdic_witness
    (N m : ℕ) (hodd : Odd N) :
    ∃ A : ℕ, twoAdicPass N m A := by
  rcases hodd with ⟨k, rfl⟩
  exact ⟨k + 1, odd_center_witness k m⟩

/-!
## Target 3 — Proposition 4.2: uniform two-adic saturation

Source: Khachatryan v11.0.3, Proposition 4.2. For odd `N ≥ 3`, with
`π_m(N)` the proportion of `A mod 2^m` such that `A²-N` is a square modulo
`2^m`, the claim is `π_m(N) ≥ 2^(-(2v+3))` for every `m`, where
`v = v₂((N-1)/2)`.

**Milestone A** (this commit): the elementary 2-adic core — monotone
descent of squareness, `odd² ≡ 1 (mod 8)`, and the Hensel square-lifting
lemma `c ≡ 1 (mod 8) ⇒ ∀ k, ∃ y, y² ≡ c (mod 2^k)`.
-/

/-- Squareness descends: a two-adic pass at level `m+1` is a pass at level
`m` (this is the monotonicity ingredient of `π_m`). -/
theorem twoAdicPass_of_succ {N m A : ℕ} (h : twoAdicPass N (m + 1) A) :
    twoAdicPass N m A := by
  obtain ⟨y, hy⟩ := h
  refine ⟨y, ?_⟩
  rw [Nat.modEq_iff_dvd] at hy ⊢
  exact dvd_trans (by exact_mod_cast pow_dvd_pow 2 (Nat.le_succ m)) hy

/-- The square of an odd integer is `1` modulo `8`. -/
theorem odd_sq_modEq_one_eight (w : ℤ) (hw : Odd w) :
    w ^ 2 ≡ 1 [ZMOD 8] := by
  obtain ⟨j, rfl⟩ := hw
  obtain ⟨i, hi⟩ := Int.even_mul_succ_self j
  refine Int.modEq_iff_dvd.mpr ⟨-i, ?_⟩
  linear_combination (-4 : ℤ) * hi

/-- Hensel lifting of a square root, inductive core: if `c ≡ 1 (mod 8)` then
for every `j` there is an odd `y` with `y² ≡ c (mod 8·2^j)`. -/
private theorem sq_lift_aux (c : ℤ) (hc : c ≡ 1 [ZMOD 8]) :
    ∀ j : ℕ, ∃ y : ℤ, Odd y ∧ y ^ 2 ≡ c [ZMOD 8 * 2 ^ j] := by
  intro j
  induction j with
  | zero =>
    refine ⟨1, ⟨0, by ring⟩, ?_⟩
    simpa using hc.symm
  | succ j ih =>
    obtain ⟨y, hyodd, hy⟩ := ih
    obtain ⟨m, rfl⟩ := hyodd
    obtain ⟨d, hd⟩ := Int.modEq_iff_dvd.mp hy
    refine ⟨2 * m + 1 + 4 * 2 ^ j * d, ⟨m + 2 * 2 ^ j * d, by ring⟩, ?_⟩
    refine Int.modEq_iff_dvd.mpr ⟨-(m * d) - 2 ^ j * d ^ 2, ?_⟩
    have epow : (8 : ℤ) * 2 ^ (j + 1) = 16 * 2 ^ j := by rw [pow_succ]; ring
    rw [epow]
    linear_combination hd

/-- Hensel's lemma for squares modulo powers of two: if `c ≡ 1 (mod 8)` then
`c` is a square modulo `2^k` for every `k`. -/
theorem isSquare_mod_two_pow_of_one_mod_eight
    (c : ℤ) (hc : c ≡ 1 [ZMOD 8]) (k : ℕ) :
    ∃ y : ℤ, y ^ 2 ≡ c [ZMOD 2 ^ k] := by
  rcases le_or_gt 3 k with hk | hk
  · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
    obtain ⟨y, _, hy⟩ := sq_lift_aux c hc j
    refine ⟨y, ?_⟩
    have hpow : (2 : ℤ) ^ (3 + j) = 8 * 2 ^ j := by rw [pow_add]; norm_num
    rw [hpow]; exact hy
  · refine ⟨1, ?_⟩
    have hdvd : (2 : ℤ) ^ k ∣ 8 := by
      have h : (2 : ℤ) ^ k ∣ 2 ^ 3 := pow_dvd_pow 2 (by omega)
      norm_num at h; exact h
    have hc' : (8 : ℤ) ∣ c - 1 := Int.modEq_iff_dvd.mp hc.symm
    have hdc : (2 : ℤ) ^ k ∣ c - 1 := dvd_trans hdvd hc'
    simpa using Int.modEq_iff_dvd.mpr hdc

/-!
**Milestone B** (this commit): the whole residue class
`A ≡ 2^v·w + 1 (mod 2^(2v+3))` (with `w` odd) makes `A² − N` a square
modulo every `2^m`, where `N = 2·(2^v·w) + 1` (so `(N−1)/2 = 2^v·w`).
This is the integer core of Proposition 4.2's density argument.
-/

/-- Every integer `A` congruent to `A₀ = 2^v·w + 1` modulo `2^(2v+3)`
(with `w` odd) satisfies: `A² − N` is a square modulo every `2^m`, where
`N = 2·(2^v·w) + 1`. Here `v = v₂((N−1)/2)` in the intended application. -/
theorem class_passesZ (v : ℕ) (w : ℤ) (hw : Odd w) (A : ℤ)
    (hA : A ≡ 2 ^ v * w + 1 [ZMOD 2 ^ (2 * v + 3)]) (m : ℕ) :
    ∃ Y : ℤ, A ^ 2 ≡ (2 * (2 ^ v * w) + 1) + Y ^ 2 [ZMOD 2 ^ m] := by
  set N : ℤ := 2 * (2 ^ v * w) + 1 with hNdef
  have hT2 : (2 : ℤ) ^ (2 * v) = (2 ^ v) ^ 2 := by rw [mul_comm, pow_mul]
  have hT3 : (2 : ℤ) ^ (2 * v + 3) = (2 ^ v) ^ 2 * 8 := by
    rw [pow_add, hT2]; norm_num
  have hsq : A ^ 2 ≡ (2 ^ v * w + 1) ^ 2 [ZMOD 2 ^ (2 * v + 3)] := hA.pow 2
  have hAN : A ^ 2 ≡ N + (2 ^ v * w) ^ 2 [ZMOD 2 ^ (2 * v + 3)] := by
    have he : (2 ^ v * w + 1) ^ 2 = N + (2 ^ v * w) ^ 2 := by rw [hNdef]; ring
    rwa [he] at hsq
  obtain ⟨s, hs⟩ := Int.modEq_iff_dvd.mp hAN
  set c : ℤ := w ^ 2 - 8 * s with hcdef
  have hANc : A ^ 2 - N = (2 ^ v) ^ 2 * c := by
    rw [hT3] at hs; rw [hcdef]; linear_combination - hs
  have hc1 : c ≡ 1 [ZMOD 8] := by
    have hwsq : w ^ 2 ≡ 1 [ZMOD 8] := odd_sq_modEq_one_eight w hw
    have hcw : c ≡ w ^ 2 [ZMOD 8] := Int.modEq_iff_dvd.mpr ⟨s, by rw [hcdef]; ring⟩
    exact hcw.trans hwsq
  rcases le_or_lt m (2 * v) with hm | hm
  · refine ⟨0, Int.modEq_iff_dvd.mpr ?_⟩
    have hdvd : (2 : ℤ) ^ m ∣ A ^ 2 - N := by
      rw [hANc, ← hT2]; exact (pow_dvd_pow 2 hm).mul_right c
    have h2 : (N + 0 ^ 2) - A ^ 2 = -(A ^ 2 - N) := by ring
    rw [h2]; exact dvd_neg.mpr hdvd
  · obtain ⟨p, hp⟩ := Nat.exists_eq_add_of_lt hm
    obtain ⟨y0, hy0⟩ := isSquare_mod_two_pow_of_one_mod_eight c hc1 (p + 1)
    obtain ⟨t, ht⟩ := Int.modEq_iff_dvd.mp hy0
    have hM : (2 : ℤ) ^ m = (2 ^ v) ^ 2 * 2 ^ (p + 1) := by
      rw [hp, show 2 * v + p + 1 = 2 * v + (p + 1) from by ring, pow_add, hT2]
    refine ⟨2 ^ v * y0, Int.modEq_iff_dvd.mpr ⟨-t, ?_⟩⟩
    rw [hM]
    linear_combination (-1 : ℤ) * hANc + (-(2 ^ v) ^ 2 : ℤ) * ht

/-!
**Milestone C** (this commit, part 1): bridge the integer core to the
natural-number pass predicate `twoAdicPass`, and specialize to an odd `N`
via its `2`-adic decomposition `(N-1)/2 = 2^v · w` with `w` odd.
-/

/-- An integer square certificate modulo `2^m` yields a `twoAdicPass`
witness (a natural-number square root taken modulo `2^m`). -/
theorem twoAdicPass_of_intWitness {N m A : ℕ}
    (h : ∃ Y : ℤ, (A : ℤ) ^ 2 ≡ (N : ℤ) + Y ^ 2 [ZMOD 2 ^ m]) :
    twoAdicPass N m A := by
  obtain ⟨Y, hY⟩ := h
  have hpos : (0 : ℤ) < 2 ^ m := pow_pos (by norm_num) m
  refine ⟨(Y % 2 ^ m).toNat, ?_⟩
  have hynn : ((Y % 2 ^ m).toNat : ℤ) = Y % 2 ^ m :=
    Int.toNat_of_nonneg (Int.emod_nonneg Y hpos.ne')
  have hyY : ((Y % 2 ^ m).toNat : ℤ) ≡ Y [ZMOD 2 ^ m] := by
    rw [hynn, Int.modEq_iff_dvd]
    exact ⟨Y / 2 ^ m, by rw [Int.emod_def]; ring⟩
  have key : (A : ℤ) ^ 2 ≡ (N : ℤ) + ((Y % 2 ^ m).toNat : ℤ) ^ 2 [ZMOD 2 ^ m] :=
    hY.trans ((hyY.pow 2).symm.add_left (N : ℤ))
  rw [Nat.modEq_iff_dvd]
  have hd := Int.modEq_iff_dvd.mp key
  push_cast
  push_cast at hd
  exact hd

/-- Specialization to a natural odd `N` written as `N = 2·(2^v·w) + 1`
with `w` odd: every `A` in the class `A ≡ 2^v·w + 1 (mod 2^(2v+3))` passes
at every level `m`. -/
theorem twoAdicPass_of_classN (v w A m : ℕ) (hw : Odd w)
    (hA : A ≡ 2 ^ v * w + 1 [MOD 2 ^ (2 * v + 3)]) :
    twoAdicPass (2 * (2 ^ v * w) + 1) m A := by
  have hwZ : Odd (w : ℤ) := by exact_mod_cast hw
  have hAZ : (A : ℤ) ≡ 2 ^ v * w + 1 [ZMOD 2 ^ (2 * v + 3)] := by
    rw [Int.modEq_iff_dvd]
    have hnat := Nat.modEq_iff_dvd.mp hA
    push_cast at hnat ⊢
    exact hnat
  obtain ⟨Y, hY⟩ := class_passesZ v (w : ℤ) hwZ (A : ℤ) hAZ m
  exact twoAdicPass_of_intWitness ⟨Y, by push_cast; exact hY⟩

/-- Passing depends only on `A` modulo `2^m`. -/
theorem twoAdicPass_congr {N m A B : ℕ} (h : A ≡ B [MOD 2 ^ m])
    (hp : twoAdicPass N m A) : twoAdicPass N m B := by
  obtain ⟨y, hy⟩ := hp
  exact ⟨y, (h.symm.pow 2).trans hy⟩

/-!
**Milestone C** (this commit, part 2): the uniform density lower bound
(Proposition 4.2). For odd `N ≥ 3` there is `v` (namely `v₂((N-1)/2)`) with
`2^(2v+3) · #{A < 2^m : A²-N is a square mod 2^m} ≥ 2^m` for every `m`,
i.e. the pass proportion `π_m(N) ≥ 2^(-(2v+3))`, uniform in `m`.
-/

/-- **Proposition 4.2 (two-adic saturation).** For odd `N ≥ 3`, the number
of residues `A < 2^m` that two-adically pass is at least `2^(m-(2v+3))`:
`2^(2v+3) · #pass ≥ 2^m`, uniformly in `m`, where `v = v₂((N-1)/2)`. -/
open Classical in
theorem twoadic_saturation (N : ℕ) (hodd : Odd N) (h3 : 3 ≤ N) :
    ∃ v : ℕ, ∀ m : ℕ,
      2 ^ m ≤ 2 ^ (2 * v + 3) *
        ((Finset.range (2 ^ m)).filter (fun A => twoAdicPass N m A)).card := by
  classical
  obtain ⟨k, rfl⟩ := hodd
  obtain ⟨v, w, hw, hkvw⟩ := Nat.exists_eq_two_pow_mul_odd (show k ≠ 0 by omega)
  refine ⟨v, fun m => ?_⟩
  rw [hkvw]
  set S : Finset ℕ :=
    (Finset.range (2 ^ m)).filter (fun A => twoAdicPass (2 * (2 ^ v * w) + 1) m A)
    with hS
  have hdpos : 0 < (2 : ℕ) ^ (2 * v + 3) := pow_pos (by norm_num) (2 * v + 3)
  have hpass : ∀ A : ℕ, A ≡ 2 ^ v * w + 1 [MOD 2 ^ (2 * v + 3)] →
      twoAdicPass (2 * (2 ^ v * w) + 1) m A :=
    fun A hA => twoAdicPass_of_classN v w A m hw hA
  rcases le_or_gt m (2 * v + 3) with hmd | hmd
  · -- small m: a single witness suffices
    have hpA0 : twoAdicPass (2 * (2 ^ v * w) + 1) m ((2 ^ v * w + 1) % 2 ^ m) :=
      twoAdicPass_congr (Nat.mod_modEq _ _)
        (hpass _ (Nat.ModEq.refl _))
    have hmem : (2 ^ v * w + 1) % 2 ^ m ∈ S := by
      rw [hS, Finset.mem_filter]
      exact ⟨Finset.mem_range.mpr (Nat.mod_lt _ (pow_pos (by norm_num) m)), hpA0⟩
    have hS1 : 1 ≤ S.card := Finset.card_pos.mpr ⟨_, hmem⟩
    calc 2 ^ m ≤ 2 ^ (2 * v + 3) := Nat.pow_le_pow_right (by norm_num) hmd
      _ = 2 ^ (2 * v + 3) * 1 := (mul_one _).symm
      _ ≤ 2 ^ (2 * v + 3) * S.card := by gcongr
  · -- large m: an arithmetic progression of passing residues
    have hdm : 2 * v + 3 ≤ m := le_of_lt hmd
    set r : ℕ := (2 ^ v * w + 1) % 2 ^ (2 * v + 3) with hr
    have hrlt : r < 2 ^ (2 * v + 3) := Nat.mod_lt _ hdpos
    set ι : ℕ → ℕ := fun j => r + j * 2 ^ (2 * v + 3) with hι
    have hpm : 2 ^ (m - (2 * v + 3)) * 2 ^ (2 * v + 3) = 2 ^ m := by
      rw [← pow_add, Nat.sub_add_cancel hdm]
    have hmaps : ∀ j ∈ Finset.range (2 ^ (m - (2 * v + 3))), ι j ∈ S := by
      intro j hj
      rw [Finset.mem_range] at hj
      have hj1 : j + 1 ≤ 2 ^ (m - (2 * v + 3)) := hj
      rw [hS, Finset.mem_filter, Finset.mem_range]
      refine ⟨?_, ?_⟩
      · have hstep : (j + 1) * 2 ^ (2 * v + 3) ≤ 2 ^ m := by
          calc (j + 1) * 2 ^ (2 * v + 3)
                ≤ 2 ^ (m - (2 * v + 3)) * 2 ^ (2 * v + 3) :=
                  mul_le_mul_right' hj1 _
            _ = 2 ^ m := hpm
        have hlt : ι j < (j + 1) * 2 ^ (2 * v + 3) := by
          have hre : (j + 1) * 2 ^ (2 * v + 3)
              = j * 2 ^ (2 * v + 3) + 2 ^ (2 * v + 3) := by ring
          simp only [hι]; omega
        omega
      · apply hpass
        have hcong : ι j ≡ r [MOD 2 ^ (2 * v + 3)] := by
          show (r + j * 2 ^ (2 * v + 3)) % 2 ^ (2 * v + 3) = r % 2 ^ (2 * v + 3)
          rw [Nat.add_mul_mod_self_right]
        refine hcong.trans ?_
        rw [hr]; exact Nat.mod_modEq _ _
    have hinj : Set.InjOn ι ↑(Finset.range (2 ^ (m - (2 * v + 3)))) := by
      intro a _ b _ hab
      simp only [hι] at hab
      have hmul : a * 2 ^ (2 * v + 3) = b * 2 ^ (2 * v + 3) := by omega
      exact Nat.eq_of_mul_eq_mul_right hdpos hmul
    have hcard : 2 ^ (m - (2 * v + 3)) ≤ S.card := by
      have hle := Finset.card_le_card_of_injOn ι hmaps hinj
      rwa [Finset.card_range] at hle
    calc 2 ^ m = 2 ^ (m - (2 * v + 3)) * 2 ^ (2 * v + 3) := hpm.symm
      _ ≤ S.card * 2 ^ (2 * v + 3) := mul_le_mul_right' hcard _
      _ = 2 ^ (2 * v + 3) * S.card := Nat.mul_comm _ _

end DyadicShells
