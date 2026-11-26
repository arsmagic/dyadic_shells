/-
Part 2 of the sparse-bias note (Corollary 4, arithmetic core).

Three statements over `Nat.choose` (decoupled from the binary-encoding bridge):
  • `sum_choose_sub_two_le` — ceiling: the N≡7 sparse bias never exceeds ×4.   [ESSENTIAL, easy]
  • `choose_pred_ratio_eq`  — exact: C(b,t-1)/C(b,t) = t/(b-(t-1)).             [ESSENTIAL, easy]
  • `choose_pred_ratio_tendsto_zero` — decay driving the N≡3 bias → 0.          [ITERATE, analysis]

The full Σ-ratio limits (→1 for N≡7, →0 for N≡3) assemble from these by elementary
dominated-term arguments and are left for the next iteration.
-/
import Mathlib

namespace DyadicShells.SparseBias

open Filter Topology Finset

/-- **Ceiling (N≡7 sparse bias ≤ ×4).** The shifted partial binomial sum is ≤ the
plain one, so the gate-mass ratio `Σ C(b-2,w) / Σ C(b,w)` never exceeds 1. -/
theorem sum_choose_sub_two_le (t b : ℕ) :
    ∑ w ∈ range (t + 1), ((b - 2).choose w) ≤ ∑ w ∈ range (t + 1), (b.choose w) :=
  Finset.sum_le_sum (fun w _ => Nat.choose_le_choose w (Nat.sub_le b 2))

/-- **Exact consecutive-binomial ratio.** For `1 ≤ t ≤ b`,
`C(b, t-1) / C(b, t) = t / (b - (t-1))`. -/
theorem choose_pred_ratio_eq {t b : ℕ} (ht : 1 ≤ t) (hb : t ≤ b) :
    ((b.choose (t - 1) : ℝ)) / (b.choose t) = (t : ℝ) / ((b - (t - 1) : ℕ) : ℝ) := by
  have hct : (b.choose t : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hb).ne'
  have hden : ((b - (t - 1) : ℕ) : ℝ) ≠ 0 := by
    have h1 : 1 ≤ b - (t - 1) := by omega
    exact_mod_cast Nat.one_le_iff_ne_zero.mp h1
  -- Nat identity: C(b,t) * t = C(b,t-1) * (b - (t-1))
  have hid : (b.choose t) * t = (b.choose (t - 1)) * (b - (t - 1)) := by
    have h := Nat.choose_succ_right_eq b (t - 1)
    rwa [Nat.sub_add_cancel ht] at h
  have hidR : (b.choose t : ℝ) * (t : ℝ) = (b.choose (t - 1) : ℝ) * ((b - (t - 1) : ℕ) : ℝ) := by
    exact_mod_cast hid
  field_simp
  linarith [hidR]

/-- **Decay crux.** `C(b, t-1) / C(b, t) → 0` as `b → ∞` (for `t ≥ 1`), since it
equals `t / (b - (t-1))`.  This is what drives the `N ≡ 3 (mod 8)` sparse bias to 0. -/
theorem choose_pred_ratio_tendsto_zero (t : ℕ) (ht : 1 ≤ t) :
    Tendsto (fun b : ℕ => (b.choose (t - 1) : ℝ) / (b.choose t)) atTop (𝓝 0) := by
  have hev : (fun b : ℕ => (b.choose (t - 1) : ℝ) / (b.choose t))
      =ᶠ[atTop] (fun b : ℕ => (t : ℝ) / ((b - (t - 1) : ℕ) : ℝ)) := by
    filter_upwards [eventually_ge_atTop t] with b hb using choose_pred_ratio_eq ht hb
  rw [tendsto_congr' hev]
  -- denominator (b - (t-1)) → ∞, so t / (·) → 0
  have hden : Tendsto (fun b : ℕ => ((b - (t - 1) : ℕ) : ℝ)) atTop atTop := by
    have hnat : Tendsto (fun b : ℕ => b - (t - 1)) atTop atTop :=
      Filter.tendsto_sub_atTop_nat (t - 1)
    exact tendsto_natCast_atTop_atTop.comp hnat
  exact Tendsto.div_atTop tendsto_const_nhds hden

end DyadicShells.SparseBias
