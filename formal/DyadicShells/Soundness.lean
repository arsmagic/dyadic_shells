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

end DyadicShells
