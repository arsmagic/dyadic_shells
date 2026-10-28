import Mathlib

/-!
# Weighted difference-of-squares: verified algebraic core

Source: Khachatryan, Dyadic Shells v11.5.17, DOI 10.5281/zenodo.23432486,
and v11.0.3, Proposition 3.1.

This file formalizes the **identity**, the two divisibility witnesses, the
**arbitrary-certificate soundness** (an exact square certificate `A^2 - N = t^2`
yields the explicit factorization `N = (A - t) * (A + t)`, with both cofactors
dividing `N`), and the **exact gcd factor recovery** under cross-coprimality
hypotheses `gcd(a, q) = 1` and `gcd(b, p) = 1`.

Note (per the source's warning): `gcd(a, b) = 1` does **not** by itself imply
`gcd(a, q) = gcd(b, p) = 1`; the recovery theorem states the cross-coprimality
conditions explicitly. See THEOREM_MAPPING.md.

These definitions and lemmas make no claims about RSA attack complexity.
-/

namespace DyadicShells

theorem weighted_center_decomposition
    (a b p q A t : ℤ)
    (hA : 2 * A = a * p + b * q)
    (ht : 2 * t = a * p - b * q) :
    A + t = a * p ∧ A - t = b * q := by
  constructor <;> linarith

theorem weighted_center_square_identity
    (a b p q A t : ℤ)
    (hA : 2 * A = a * p + b * q)
    (ht : 2 * t = a * p - b * q) :
    A ^ 2 - (a * b) * (p * q) = t ^ 2 := by
  obtain ⟨hp, hq⟩ := weighted_center_decomposition a b p q A t hA ht
  have hprod : (A + t) * (A - t) = (a * b) * (p * q) := by
    rw [hp, hq]
    ring
  calc
    A ^ 2 - (a * b) * (p * q) =
        (A + t) * (A - t) - (a * b) * (p * q) + t ^ 2 := by ring
    _ = t ^ 2 := by rw [hprod]; ring

theorem weighted_center_factor_witnesses
    (a b p q A t : ℤ)
    (hA : 2 * A = a * p + b * q)
    (ht : 2 * t = a * p - b * q) :
    p ∣ A + t ∧ q ∣ A - t := by
  obtain ⟨hp, hq⟩ := weighted_center_decomposition a b p q A t hA ht
  constructor
  · rw [hp]
    exact ⟨a, by ring⟩
  · rw [hq]
    exact ⟨b, by ring⟩

/-!
## Target 1 — factor recovery

Two independent strengthenings of the identity above.

* `square_certificate_*`: **arbitrary-certificate soundness**. Any exact square
  certificate `A^2 - N = t^2` (no planted multipliers required) factors `N`
  explicitly as `(A - t) * (A + t)`, and both cofactors divide `N`.
* `gcd_factor_recovery`: **exact recovery** in the planted-multiplier setting of
  Proposition 3.1, under the cross-coprimality hypotheses.
-/

/-- Arbitrary-certificate soundness: an exact square certificate for `N`
exhibits the explicit factorization `N = (A - t) * (A + t)`. -/
theorem square_certificate_factorization
    (N A t : ℤ)
    (h : A ^ 2 - N = t ^ 2) :
    N = (A - t) * (A + t) := by
  have hN : N = A ^ 2 - t ^ 2 := by linarith
  rw [hN]; ring

/-- Both cofactors of an exact square certificate divide `N`. -/
theorem square_certificate_dvd
    (N A t : ℤ)
    (h : A ^ 2 - N = t ^ 2) :
    (A - t) ∣ N ∧ (A + t) ∣ N := by
  have hfac := square_certificate_factorization N A t h
  refine ⟨⟨A + t, hfac⟩, ⟨A - t, ?_⟩⟩
  rw [hfac]; ring

/-- Exact gcd factor recovery (Proposition 3.1, planted-multiplier setting).

With `A + t = a * p`, `A - t = b * q` and `N = p * q`, the cross-coprimality
hypotheses `gcd(a, q) = 1` and `gcd(b, p) = 1` give
`gcd(A + t, N) = |p|` and `gcd(A - t, N) = |q|`.

The hypotheses are exactly those of the source; `gcd(a, b) = 1` is deliberately
**not** used, since it is insufficient. -/
theorem gcd_factor_recovery
    (a b p q A t : ℤ)
    (hA : 2 * A = a * p + b * q)
    (ht : 2 * t = a * p - b * q)
    (hcaq : Int.gcd a q = 1)
    (hcbp : Int.gcd b p = 1) :
    Int.gcd (A + t) (p * q) = p.natAbs ∧ Int.gcd (A - t) (p * q) = q.natAbs := by
  obtain ⟨hpt, hqt⟩ := weighted_center_decomposition a b p q A t hA ht
  constructor
  · rw [hpt, mul_comm a p, Int.gcd_mul_left, hcaq, mul_one]
  · rw [hqt, mul_comm b q, mul_comm p q, Int.gcd_mul_left, hcbp, mul_one]

/-!
## Target 1-A — corollary matching published Proposition 3.1

Published setting: `p, q` primes, `0 < a, b < min p q`, planted center
`2 A = a p + b q` with `t := a p - A` (so `2 t = a p - b q` holds **by
construction**, not by an extra assumption). The cross-coprimality
`gcd(a, q) = gcd(b, p) = 1` is **derived** from primality and the size bounds;
`gcd(a, b) = 1` is neither assumed nor sufficient.
-/

/-- Proposition 3.1 (planted recovery) under the published hypotheses. From
distinct-prime-style assumptions and bounds `0 < a, b < min p q`, with `t`
constructed from `A`, the exact prime factors are recovered:
`gcd(A + t, p q) = p` and `gcd(A - t, p q) = q`. -/
theorem prop31_factor_recovery
    (p q a b : ℕ) (A t : ℤ)
    (hp : p.Prime) (hq : q.Prime)
    (ha : 0 < a) (hb : 0 < b)
    (hab : a < min p q) (hbb : b < min p q)
    (hA : 2 * A = (a : ℤ) * p + (b : ℤ) * q)
    (ht : t = (a : ℤ) * p - A) :
    Int.gcd (A + t) ((p : ℤ) * q) = p ∧ Int.gcd (A - t) ((p : ℤ) * q) = q := by
  have ht2 : 2 * t = (a : ℤ) * p - (b : ℤ) * q := by rw [ht]; linarith
  have hca : Nat.Coprime a q :=
    (hq.coprime_iff_not_dvd.mpr
      (Nat.not_dvd_of_pos_of_lt ha (lt_of_lt_of_le hab (min_le_right p q)))).symm
  have hcb : Nat.Coprime b p :=
    (hp.coprime_iff_not_dvd.mpr
      (Nat.not_dvd_of_pos_of_lt hb (lt_of_lt_of_le hbb (min_le_left p q)))).symm
  have hca' : Int.gcd (a : ℤ) (q : ℤ) = 1 := by simpa [Int.gcd] using hca
  have hcb' : Int.gcd (b : ℤ) (p : ℤ) = 1 := by simpa [Int.gcd] using hcb
  obtain ⟨g1, g2⟩ :=
    gcd_factor_recovery (a : ℤ) (b : ℤ) (p : ℤ) (q : ℤ) A t hA ht2 hca' hcb'
  exact ⟨by simpa using g1, by simpa using g2⟩

/-- Nontriviality of the recovered factors: for primes `p, q` and `n = p q`,
each recovered value is a **proper** divisor, `1 < p < n` and `1 < q < n`.
Being a divisor is not enough for screening; the factor must be proper. -/
theorem prop31_recovered_proper
    (p q : ℕ) (hp : p.Prime) (hq : q.Prime) :
    1 < p ∧ p < p * q ∧ 1 < q ∧ q < p * q := by
  have hp1 := hp.one_lt
  have hq1 := hq.one_lt
  have hpp := hp.pos
  have hqp := hq.pos
  refine ⟨hp1, ?_, hq1, ?_⟩
  · exact (Nat.lt_mul_iff_one_lt_right hpp).mpr hq1
  · exact (Nat.lt_mul_iff_one_lt_left hqp).mpr hp1

/-!
## Target 1-B — general weighted certificates: soundness vs. recovery

A weighted square certificate factors the *weighted* modulus `k n`, but does
**not** by itself certify a proper factor of `n`: the acceptance test also needs
`1 < gcd(A ± t, n) < |n|`. The `n = 35, k = 3` regression below exhibits an
exact weighted square whose cofactor gcds are both trivial.
-/

/-- Weighted certificate factorization: `A² - k n = t²` factors `k n`. -/
theorem weighted_certificate_factorization (n k A t : ℤ)
    (h : A ^ 2 - k * n = t ^ 2) :
    k * n = (A - t) * (A + t) :=
  square_certificate_factorization (k * n) A t h

/-- A cofactor gcd always divides `|n|` (necessary but **not** sufficient for a
proper factor). -/
theorem gcd_dvd_modulus (A t n : ℤ) :
    Int.gcd (A + t) n ∣ n.natAbs := by
  show (A + t).natAbs.gcd n.natAbs ∣ n.natAbs
  exact Nat.gcd_dvd_right _ _

/-- Acceptance criterion: a cofactor gcd is a **proper nontrivial divisor** of
`n` exactly when it lies strictly between `1` and `|n|`. -/
theorem proper_divisor_criterion (A t n : ℤ)
    (h1 : 1 < Int.gcd (A + t) n) (h2 : Int.gcd (A + t) n < n.natAbs) :
    Int.gcd (A + t) n ∣ n.natAbs ∧ 1 < Int.gcd (A + t) n ∧
      Int.gcd (A + t) n < n.natAbs :=
  ⟨gcd_dvd_modulus A t n, h1, h2⟩

/-- Source Proposition 3.1, converse for **either** sign: every
cofactor gcd strictly between 1 and |n| is a proper divisor of |n|.
This implication holds regardless of how A and t were obtained. -/
theorem proper_divisor_criterion_either_sign (A t n : ℤ) (d : ℕ)
    (hside : d = Int.gcd (A + t) n ∨ d = Int.gcd (A - t) n)
    (hlo : 1 < d) (hhi : d < n.natAbs) :
    d ∣ n.natAbs ∧ 1 < d ∧ d < n.natAbs := by
  have hdvd : d ∣ n.natAbs := by
    rcases hside with hplus | hminus
    · rw [hplus]
      exact gcd_dvd_modulus A t n
    · rw [hminus]
      simpa [sub_eq_add_neg] using (gcd_dvd_modulus A (-t) n)
  exact ⟨hdvd, hlo, hhi⟩

/-- Regression (source handoff): an exact *weighted* square certificate need not
yield a proper factor. For `n = 35, k = 3, A = 53, t = 52` the identity holds
yet both cofactor gcds are trivial (`1` and `n = 35`). -/
example : (53 : ℤ) ^ 2 - 3 * 35 = 52 ^ 2 := by norm_num

example : Int.gcd (53 - 52 : ℤ) 35 = 1 := by decide

example : Int.gcd (53 + 52 : ℤ) 35 = 35 := by decide

end DyadicShells
