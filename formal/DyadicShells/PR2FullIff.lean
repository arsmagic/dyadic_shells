import Mathlib

/-!
# PR2 (candidate): complete odd-unit square criterion in `ZMod (2^n)`

Candidate for the two-way sharp characterization (validation only; separate from
`PR2Standalone.lean`, which is kept unchanged). For an **odd** integer `a`:

`IsSquare (a : ZMod (2^n)) ↔ a ≡ 1 [ZMOD 2^min(n,3)]`.

For `n ≥ 3` this is `a ≡ 1 (mod 8)`; for `n = 0,1,2` it is the correct weaker
congruence. Even inputs are out of scope here.

Self-contained (Mathlib only). Helpers `odd_sq_modEq_one_eight`, `sq_lift_aux`,
`isSquare_mod_two_pow_of_one_mod_eight`, `exists_int_sq`, `modEq_of_dvd` are the
base; for an actual PR they become `private` and imports are minimized. The
namespace avoids clashes with the project files during validation.

Master compatibility NOT verified (Lean toolchain for master is proxy-blocked
here); validated against pinned Mathlib v4.24.0 only.
-/

namespace DyadicShells.PR2FullIff

/-- The square of an odd integer is `1` modulo `8`. -/
theorem odd_sq_modEq_one_eight (w : ℤ) (hw : Odd w) :
    w ^ 2 ≡ 1 [ZMOD 8] := by
  obtain ⟨j, rfl⟩ := hw
  obtain ⟨i, hi⟩ := Int.even_mul_succ_self j
  refine Int.modEq_iff_dvd.mpr ⟨-i, ?_⟩
  linear_combination (-4 : ℤ) * hi

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

/-- If `c ≡ 1 (mod 8)` then `c` is a square modulo `2^k` for every `k`. -/
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

/-- Pass a congruence to a divisor of the modulus. -/
private theorem modEq_of_dvd {d m a b : ℤ} (hdm : d ∣ m) (h : a ≡ b [ZMOD m]) :
    a ≡ b [ZMOD d] :=
  Int.modEq_iff_dvd.mpr (dvd_trans hdm (Int.modEq_iff_dvd.mp h))

/-- A `ZMod (2^n)` square lifts to an integer square certificate. -/
private theorem exists_int_sq {n : ℕ} {a : ℤ}
    (h : IsSquare (a : ZMod (2 ^ n))) : ∃ y : ℤ, a ≡ y ^ 2 [ZMOD (2 : ℤ) ^ n] := by
  haveI : NeZero ((2 : ℕ) ^ n) := ⟨pow_ne_zero n (by norm_num)⟩
  obtain ⟨r, hr⟩ := h
  refine ⟨(r.val : ℤ), ?_⟩
  have hrv : ((r.val : ℤ) : ZMod (2 ^ n)) = r := by
    push_cast; exact ZMod.natCast_rightInverse r
  have key : ((a : ℤ) : ZMod (2 ^ n)) = (((r.val : ℤ) ^ 2 : ℤ) : ZMod (2 ^ n)) := by
    rw [hr]; push_cast [hrv]; ring
  have hmod : (((2 : ℕ) ^ n : ℕ) : ℤ) = (2 : ℤ) ^ n := by push_cast; ring
  have hme := (ZMod.intCast_eq_intCast_iff a ((r.val : ℤ) ^ 2) (2 ^ n)).mp key
  rwa [hmod] at hme

/-- **Complete odd-unit square criterion in `ZMod (2^n)`.** For an odd integer
`a`, `a` is a square in `ZMod (2^n)` iff `a ≡ 1 (mod 2^min(n,3))` (i.e. mod `8`
for `n ≥ 3`, and the correct weaker condition for `n ≤ 2`). -/
theorem isSquare_zmod_two_pow_iff_of_odd (a : ℤ) (n : ℕ) (ha : Odd a) :
    IsSquare (a : ZMod (2 ^ n)) ↔ a ≡ 1 [ZMOD (2 : ℤ) ^ min n 3] := by
  constructor
  · -- necessity
    intro hsq
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · subst hn0
      rw [Nat.zero_min, pow_zero]
      exact Int.modEq_one
    · obtain ⟨y, hy⟩ := exists_int_sq hsq
      have hyy : y ≡ y ^ 2 [ZMOD 2] := by
        have he : Even (y ^ 2 - y) := by
          have h := Int.even_mul_succ_self (y - 1)
          have he2 : (y - 1) * ((y - 1) + 1) = y ^ 2 - y := by ring
          rwa [he2] at h
        obtain ⟨k, hk⟩ := he
        exact Int.modEq_iff_dvd.mpr ⟨k, by linarith⟩
      have ha2 : a ≡ y [ZMOD 2] :=
        (modEq_of_dvd (dvd_pow_self 2 (by omega : n ≠ 0)) hy).trans hyy.symm
      have hyodd : Odd y := by
        rw [Int.odd_iff]
        rw [Int.odd_iff] at ha
        rw [Int.ModEq] at ha2
        omega
      have h8 : y ^ 2 ≡ 1 [ZMOD 8] := odd_sq_modEq_one_eight y hyodd
      have h8' : y ^ 2 ≡ 1 [ZMOD (2 : ℤ) ^ 3] := by
        rw [show (2 : ℤ) ^ 3 = 8 by norm_num]; exact h8
      have e1 : a ≡ y ^ 2 [ZMOD (2 : ℤ) ^ min n 3] :=
        modEq_of_dvd (pow_dvd_pow 2 (min_le_left n 3)) hy
      have e2 : y ^ 2 ≡ 1 [ZMOD (2 : ℤ) ^ min n 3] :=
        modEq_of_dvd (pow_dvd_pow 2 (min_le_right n 3)) h8'
      exact e1.trans e2
  · -- sufficiency
    intro hcong
    rcases lt_or_ge n 3 with hn | hn
    · have hmin : min n 3 = n := min_eq_left (by omega)
      rw [hmin] at hcong
      have hmod : (((2 : ℕ) ^ n : ℕ) : ℤ) = (2 : ℤ) ^ n := by push_cast; ring
      have hcong' : a ≡ 1 [ZMOD (((2 : ℕ) ^ n : ℕ) : ℤ)] := by rw [hmod]; exact hcong
      have h1 : (a : ZMod (2 ^ n)) = 1 := by
        have := (ZMod.intCast_eq_intCast_iff a 1 (2 ^ n)).mpr hcong'
        simpa using this
      rw [h1]; exact isSquare_one
    · have hmin : min n 3 = 3 := min_eq_right hn
      rw [hmin] at hcong
      have h8 : a ≡ 1 [ZMOD 8] := by
        rw [show (2 : ℤ) ^ 3 = 8 by norm_num] at hcong; exact hcong
      obtain ⟨y, hy⟩ := isSquare_mod_two_pow_of_one_mod_eight a h8 n
      refine ⟨(y : ZMod (2 ^ n)), ?_⟩
      have hmod : (((2 : ℕ) ^ n : ℕ) : ℤ) = (2 : ℤ) ^ n := by push_cast; ring
      have hmode : a ≡ y ^ 2 [ZMOD (((2 : ℕ) ^ n : ℕ) : ℤ)] := by
        rw [hmod]; exact hy.symm
      have hcast : ((a : ℤ) : ZMod (2 ^ n)) = (((y : ℤ) ^ 2 : ℤ) : ZMod (2 ^ n)) :=
        (ZMod.intCast_eq_intCast_iff _ _ _).mpr hmode
      push_cast at hcast
      rw [hcast]; ring

/-- Specialization to `n ≥ 3`: an odd `a` is a square in `ZMod (2^n)` iff
`a ≡ 1 (mod 8)`. -/
theorem isSquare_zmod_two_pow_iff_of_odd_three_le
    (a : ℤ) {n : ℕ} (hn : 3 ≤ n) (ha : Odd a) :
    IsSquare (a : ZMod (2 ^ n)) ↔ a ≡ 1 [ZMOD 8] := by
  rw [isSquare_zmod_two_pow_iff_of_odd a n ha, min_eq_right hn,
    show (2 : ℤ) ^ 3 = 8 by norm_num]

end DyadicShells.PR2FullIff
