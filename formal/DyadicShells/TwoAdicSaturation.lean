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
  rcases le_or_lt 3 k with hk | hk
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

end DyadicShells
