import Mathlib

/-!
# PR 2 (self-contained): squares modulo powers of two

Standalone — depends on **Mathlib only**. Submission-ready content for
`leanprover-community/mathlib4`:
`a ≡ 1 (mod 8) ⇒ IsSquare (a : ZMod (2^n))`, via the elementary Hensel lift
`a ≡ 1 (mod 8) ⇒ ∀ k, ∃ y, y² ≡ a (mod 2^k)`.

`sq_lift_aux` (and, if Mathlib lacks it, `odd_sq_modEq_one_eight`) become
`private` in the PR. The namespace `DyadicShells.PR2Standalone` only avoids a
name clash with the project files while validating in this repo — strip it for
the Mathlib PR. Suggested home: a new file under `Mathlib/NumberTheory/` or an
existing `ZMod` squares file (ask on Zulip).

**Check first on master:** Mathlib may already have `odd_sq_modEq_one_eight`
(odd² ≡ 1 mod 8) under some name — if so, drop it and use theirs.
-/

namespace DyadicShells.PR2Standalone

/-- The square of an odd integer is `1` modulo `8`. -/
theorem odd_sq_modEq_one_eight (w : ℤ) (hw : Odd w) :
    w ^ 2 ≡ 1 [ZMOD 8] := by
  obtain ⟨j, rfl⟩ := hw
  obtain ⟨i, hi⟩ := Int.even_mul_succ_self j
  refine Int.modEq_iff_dvd.mpr ⟨-i, ?_⟩
  linear_combination (-4 : ℤ) * hi

/-- Hensel lifting of a square root, inductive core: if `c ≡ 1 (mod 8)` then for
every `j` there is an odd `y` with `y² ≡ c (mod 8·2^j)`. -/
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

/-- **Hensel's lemma for squares modulo powers of two.** If `c ≡ 1 (mod 8)` then
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

/-- **Squares in `ZMod (2^n)` via the mod-8 condition.** If `a ≡ 1 (mod 8)` then
`a` is a square in `ZMod (2^n)`, for every `n`. -/
theorem isSquare_zmod_two_pow_of_mod_eight {n : ℕ} {a : ℤ} (ha : a % 8 = 1) :
    IsSquare (a : ZMod (2 ^ n)) := by
  have hc : a ≡ 1 [ZMOD 8] := by show a % 8 = 1 % 8; omega
  obtain ⟨y, hy⟩ := isSquare_mod_two_pow_of_one_mod_eight a hc n
  refine ⟨(y : ZMod (2 ^ n)), ?_⟩
  have hmod : a ≡ y ^ 2 [ZMOD ((2 ^ n : ℕ) : ℤ)] := by push_cast; exact hy.symm
  have hcast : ((a : ℤ) : ZMod (2 ^ n)) = ((y ^ 2 : ℤ) : ZMod (2 ^ n)) :=
    (ZMod.intCast_eq_intCast_iff _ _ _).mpr hmod
  push_cast at hcast
  rw [hcast]; ring

end DyadicShells.PR2Standalone
