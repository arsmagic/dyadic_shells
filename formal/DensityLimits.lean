/-
Corollary 2 of the paper (Version 11.11.04): the two-adic pass proportion

    π_m(N) = C_m(N) / 2^m

satisfies `π_m(N) > 1/24` for every odd `N` and every `m`, its limit as `m → ∞`
is `1/4`, `1/8` or `1/24` according as `N ≡ 3 (mod 4)`, `N ≡ 5 (mod 8)` or
`N ≡ 1 (mod 8)`, and the constant `1/24` is optimal.

The strict bound is already `ClosedForms.passCard_density`; this file adds the
real-valued density, the three limits, and the sharpness statement, all read off
from the closed forms of Theorem 1.

* `passDensity_gt`        : `1/24 < π_m(N)` for odd `N` (restatement over `ℝ`).
* `tendsto_passDensity_three` / `_five` / `_one` : the three limits.
* `passDensity_sharp`     : any constant that bounds every `π_m(N)` from below is `≤ 1/24`.
-/
import Mathlib
import DyadicShells.TwoAdicExact
import ClosedForms

namespace DyadicShells.DensityLimits

open Filter Topology DyadicShells DyadicShells.ClosedForms

/-- The two-adic pass proportion `π_m(N) = C_m(N) / 2 ^ m`, as a real number. -/
noncomputable def passDensity (N : ℤ) (m : ℕ) : ℝ :=
  (passCard ((N : ZMod (2 ^ m))) : ℝ) / (2 : ℝ) ^ m

private theorem neZero_two_pow (m : ℕ) : NeZero ((2 : ℕ) ^ m) :=
  ⟨by positivity⟩

private theorem two_pow_pos_real (m : ℕ) : (0 : ℝ) < (2 : ℝ) ^ m := by positivity

/-! ### The uniform bound -/

/-- **Corollary 2, bound.** `π_m(N) > 1/24` for every odd `N` and every `m`. -/
theorem passDensity_gt (N : ℤ) (hN : Odd N) (m : ℕ) : 1 / 24 < passDensity N m := by
  haveI := neZero_two_pow m
  have h := passCard_density N hN m
  have h' : ((2 : ℕ) ^ m : ℝ) < 24 * (passCard ((N : ZMod (2 ^ m))) : ℝ) := by
    exact_mod_cast h
  have hpow : ((2 : ℕ) ^ m : ℝ) = (2 : ℝ) ^ m := by push_cast; ring
  rw [hpow] at h'
  rw [passDensity, lt_div_iff₀ (two_pow_pos_real m)]
  linarith

/-! ### The three limits -/

/-- `N ≡ 3 (mod 4)`: the density is exactly `1/4` from level 3 on. -/
theorem passDensity_eq_three (N : ℤ) (hN : N ≡ 3 [ZMOD 4]) (m : ℕ) (hm : 3 ≤ m) :
    passDensity N m = 1 / 4 := by
  have hsplit : (2 : ℝ) ^ m = (2 : ℝ) ^ (m - 2) * 4 := by
    conv_lhs => rw [show m = (m - 2) + 2 from by omega]
    rw [pow_add]; norm_num
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (m - 2) := by positivity
  rw [passDensity, passCard_three_mod_four N hN m hm]
  push_cast
  rw [hsplit]
  field_simp

/-- **Corollary 2, limit for `N ≡ 3 (mod 4)`.** -/
theorem tendsto_passDensity_three (N : ℤ) (hN : N ≡ 3 [ZMOD 4]) :
    Tendsto (passDensity N) atTop (𝓝 (1 / 4)) := by
  refine Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [eventually_ge_atTop 3] with m hm
  exact (passDensity_eq_three N hN m hm).symm

/-- `N ≡ 5 (mod 8)`: the density is exactly `1/8` from level 5 on. -/
theorem passDensity_eq_five (N : ℤ) (hN : N ≡ 5 [ZMOD 8]) (m : ℕ) (hm : 5 ≤ m) :
    passDensity N m = 1 / 8 := by
  have hsplit : (2 : ℝ) ^ m = (2 : ℝ) ^ (m - 3) * 8 := by
    conv_lhs => rw [show m = (m - 3) + 3 from by omega]
    rw [pow_add]; norm_num
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (m - 3) := by positivity
  rw [passDensity, passCard_five_mod_eight N hN m hm]
  push_cast
  rw [hsplit]
  field_simp

/-- **Corollary 2, limit for `N ≡ 5 (mod 8)`.** -/
theorem tendsto_passDensity_five (N : ℤ) (hN : N ≡ 5 [ZMOD 8]) :
    Tendsto (passDensity N) atTop (𝓝 (1 / 8)) := by
  refine Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [eventually_ge_atTop 5] with m hm
  exact (passDensity_eq_five N hN m hm).symm

/-- `N ≡ 1 (mod 8)`: the density exceeds `1/24` by at most `20 / (3 · 2^m)`.
Both parities give `3 C_m = 2^(m-3) + c` with `c ∈ {16, 20}`, hence
`π_m = 1/24 + c / (3 · 2^m)`. -/
theorem passDensity_one_sub_le (N : ℤ) (hN : N ≡ 1 [ZMOD 8]) (m : ℕ) (hm : 5 ≤ m) :
    |passDensity N m - 1 / 24| ≤ 20 / (3 * (2 : ℝ) ^ m) := by
  haveI := neZero_two_pow m
  -- `3 * C_m = 2^(m-3) + c` with `c = 16` (even `m`) or `c = 20` (odd `m`)
  obtain ⟨c, hc16, hc20, hC⟩ :
      ∃ c : ℕ, 16 ≤ c ∧ c ≤ 20 ∧
        3 * passCard ((N : ZMod (2 ^ m))) = 2 ^ (m - 3) + c := by
    rcases Nat.even_or_odd m with hpar | hpar
    · have hm6 : 6 ≤ m := by
        have := hpar.two_dvd
        omega
      exact ⟨16, le_rfl, by norm_num,
        passCard_one_mod_eight_even N hN m hm6 hpar⟩
    · exact ⟨20, by norm_num, le_rfl, passCard_one_mod_eight_odd N hN m hm hpar⟩
  -- pass to `ℝ`
  have hCR : 3 * (passCard ((N : ZMod (2 ^ m))) : ℝ) = (2 : ℝ) ^ (m - 3) + (c : ℝ) := by
    have := congrArg (fun k : ℕ => (k : ℝ)) hC
    push_cast at this
    linarith [this]
  have hsplit : (2 : ℝ) ^ m = (2 : ℝ) ^ (m - 3) * 8 := by
    conv_lhs => rw [show m = (m - 3) + 3 from by omega]
    rw [pow_add]; norm_num
  have hpos3 : (0 : ℝ) < (2 : ℝ) ^ (m - 3) := by positivity
  have hposm : (0 : ℝ) < (2 : ℝ) ^ m := two_pow_pos_real m
  -- `π_m − 1/24 = c / (3 · 2^m)`
  have hkey : passDensity N m - 1 / 24 = (c : ℝ) / (3 * (2 : ℝ) ^ m) := by
    rw [passDensity]
    field_simp
    nlinarith [hCR]
  rw [hkey, abs_of_nonneg (by positivity)]
  have hc20R : (c : ℝ) ≤ 20 := by exact_mod_cast hc20
  exact div_le_div_of_nonneg_right hc20R (by positivity)

/-- `20 / (3 · 2^m) → 0`. -/
private theorem tendsto_bound : Tendsto (fun m : ℕ => 20 / (3 * (2 : ℝ) ^ m)) atTop (𝓝 0) := by
  have h : Tendsto (fun m : ℕ => ((1 : ℝ) / 2) ^ m) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have := h.const_mul ((20 : ℝ) / 3)
  simpa using this.congr fun m => by
    rw [div_pow, one_pow]
    field_simp

/-- **Corollary 2, limit for `N ≡ 1 (mod 8)`.** -/
theorem tendsto_passDensity_one (N : ℤ) (hN : N ≡ 1 [ZMOD 8]) :
    Tendsto (passDensity N) atTop (𝓝 (1 / 24)) := by
  have hsub : Tendsto (fun m => passDensity N m - 1 / 24) atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ tendsto_bound
    filter_upwards [eventually_ge_atTop 5] with m hm
    simpa [Real.norm_eq_abs] using passDensity_one_sub_le N hN m hm
  have := hsub.add (tendsto_const_nhds (x := (1 : ℝ) / 24))
  simpa using this

/-! ### Sharpness of the constant -/

/-- **Corollary 2, sharpness.** `1/24` cannot be replaced by a larger constant:
any `c` bounding every `π_m(N)` from below satisfies `c ≤ 1/24`. Together with
`passDensity_gt` this says `inf_{N, m} π_m(N) = 1/24`, the infimum not attained. -/
theorem passDensity_sharp (c : ℝ) (h : ∀ N : ℤ, Odd N → ∀ m : ℕ, c ≤ passDensity N m) :
    c ≤ 1 / 24 :=
  ge_of_tendsto (tendsto_passDensity_one 1 (Int.ModEq.refl 1))
    (Eventually.of_forall fun m => h 1 odd_one m)

end DyadicShells.DensityLimits
