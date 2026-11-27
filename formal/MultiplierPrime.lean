/-
Proposition 12 of the paper (Version 11.11.04): a sieve prime dividing the
multiplier exactly once.

Let `ℓ` be an odd prime, `K : ℤ` with `v_ℓ(K) = 1`, and `e ≥ 2`. Then the number
of `A mod ℓ^e` for which `A² − K` is a square modulo `ℓ^e` is `ℓ^e − ℓ^(e-1)`:
exactly the centres prime to `ℓ` pass. So such a prime removes the proportion
`1/ℓ` at modulus `ℓ²` and nothing further at higher powers.

Mathlib has no "a unit square mod `p` is a square mod `p^e`" lemma, so the
elementary lifting step is proved here (`exists_sq_sub_dvd`): if `a² ≡ u
(mod p^e)` with `p ∤ u` and `p` odd, then `a' = a − t p^e` works modulo
`p^(e+1)` for the `t` solving `2 a t ≡ c (mod p)`, which exists because `2a` is
invertible mod the odd prime `p`.

* `exists_sq_sub_dvd`          : the lift, over `ℤ`.
* `isSquare_zmod_pow_of_mod_p` : its `ZMod` form.
* `passCard_multiplier_prime`  : Proposition 12.
-/
import Mathlib
import DyadicShells.TwoAdicExact

namespace DyadicShells.MultiplierPrime

open Finset DyadicShells

/-! ### Lifting a unit square from `p` to `p ^ e` (`p` odd) -/

/-- One Hensel step for an odd prime `p`: a square root of `u` modulo `p ^ e`
(with `p ∤ u`, `e ≥ 1`) lifts to one modulo `p ^ (e+1)`. -/
theorem exists_sq_sub_dvd_succ (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (u : ℤ)
    (hu : ¬ ((p : ℤ) ∣ u)) (e : ℕ) (he : 1 ≤ e) (a : ℤ) (ha : ((p : ℤ)) ^ e ∣ a ^ 2 - u) :
    ∃ a' : ℤ, ((p : ℤ)) ^ (e + 1) ∣ a' ^ 2 - u := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  -- `p ∤ a`, else `p ∣ u`
  have hpa : ¬ ((p : ℤ) ∣ a) := by
    intro h
    refine hu ?_
    have h1 : (p : ℤ) ∣ a ^ 2 := dvd_pow h (by norm_num)
    have h2 : (p : ℤ) ∣ a ^ 2 - u :=
      dvd_trans (dvd_pow_self (p : ℤ) (by omega)) ha
    simpa using dvd_sub h1 h2
  -- `2a` is invertible mod `p`
  have hp2Z : ¬ ((p : ℤ) ∣ 2) := by
    intro h
    have : p ∣ 2 := by exact_mod_cast h
    have hp_le : p ≤ 2 := Nat.le_of_dvd (by decide) this
    interval_cases p <;> simp_all
  have h2a : (((2 * a : ℤ)) : ZMod p) ≠ 0 := by
    intro h
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
    rcases hpZ.dvd_mul.mp h with h' | h'
    · exact hp2Z h'
    · exact hpa h'
  obtain ⟨c, hc⟩ := ha
  -- solve `2 a t ≡ c (mod p)`
  obtain ⟨x, hx⟩ : ∃ x : ZMod p, (((2 * a : ℤ)) : ZMod p) * x = ((c : ℤ) : ZMod p) :=
    ⟨((c : ℤ) : ZMod p) / (((2 * a : ℤ)) : ZMod p), by field_simp⟩
  set t : ℤ := (x.val : ℤ) with ht
  have htx : ((t : ℤ) : ZMod p) = x := by
    rw [ht]; push_cast; simp [ZMod.natCast_val, ZMod.cast_id]
  have hdvd : (p : ℤ) ∣ c - 2 * a * t := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [htx]
    push_cast at hx
    linear_combination -hx
  obtain ⟨d, hd⟩ := hdvd
  refine ⟨a - t * (p : ℤ) ^ e, ?_⟩
  have hexp : 2 * e = (e + 1) + (e - 1) := by omega
  have key : (a - t * (p : ℤ) ^ e) ^ 2 - u
      = (p : ℤ) ^ (e + 1) * (d + t ^ 2 * (p : ℤ) ^ (e - 1)) := by
    have hpow : ((p : ℤ) ^ e) ^ 2 = (p : ℤ) ^ (e + 1) * (p : ℤ) ^ (e - 1) := by
      rw [← pow_mul, ← pow_add]; congr 1; omega
    have hc' : a ^ 2 - u = (p : ℤ) ^ e * c := hc
    have hd' : c = (p : ℤ) * d + 2 * a * t := by linarith [hd]
    have hps : (p : ℤ) ^ e * (p : ℤ) = (p : ℤ) ^ (e + 1) := by rw [← pow_succ]
    calc (a - t * (p : ℤ) ^ e) ^ 2 - u
        = (a ^ 2 - u) - 2 * a * t * (p : ℤ) ^ e + t ^ 2 * ((p : ℤ) ^ e) ^ 2 := by ring
      _ = (p : ℤ) ^ e * c - 2 * a * t * (p : ℤ) ^ e + t ^ 2 * ((p : ℤ) ^ e) ^ 2 := by
            rw [hc']
      _ = (p : ℤ) ^ e * ((p : ℤ) * d + 2 * a * t) - 2 * a * t * (p : ℤ) ^ e
            + t ^ 2 * ((p : ℤ) ^ e) ^ 2 := by rw [← hd']
      _ = ((p : ℤ) ^ e * (p : ℤ)) * d + t ^ 2 * ((p : ℤ) ^ e) ^ 2 := by ring
      _ = (p : ℤ) ^ (e + 1) * d + t ^ 2 * ((p : ℤ) ^ (e + 1) * (p : ℤ) ^ (e - 1)) := by
            rw [hps, hpow]
      _ = (p : ℤ) ^ (e + 1) * (d + t ^ 2 * (p : ℤ) ^ (e - 1)) := by ring
  exact ⟨_, key⟩

/-- For an odd prime `p` and `p ∤ u`: a square root of `u` modulo `p` lifts to
one modulo `p ^ e`, for every `e ≥ 1`. -/
theorem exists_sq_sub_dvd (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (u : ℤ)
    (hu : ¬ ((p : ℤ) ∣ u)) (h1 : ∃ a : ℤ, (p : ℤ) ∣ a ^ 2 - u) (e : ℕ) (he : 1 ≤ e) :
    ∃ a : ℤ, ((p : ℤ)) ^ e ∣ a ^ 2 - u := by
  induction e, he using Nat.le_induction with
  | base => simpa using h1
  | succ k hk ih =>
      obtain ⟨a, ha⟩ := ih
      exact exists_sq_sub_dvd_succ p hp hp2 u hu k hk a ha

/-- `ZMod` form of the lift. -/
theorem isSquare_zmod_pow_of_mod_p (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (u : ℤ)
    (hu : ¬ ((p : ℤ) ∣ u)) (hsq : IsSquare ((u : ZMod p))) (e : ℕ) (he : 1 ≤ e)
    [NeZero (p ^ e)] :
    IsSquare ((u : ZMod (p ^ e))) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  -- an integer square root modulo `p`
  obtain ⟨r, hr⟩ := hsq
  have h1 : ∃ a : ℤ, (p : ℤ) ∣ a ^ 2 - u := by
    refine ⟨(r.val : ℤ), ?_⟩
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ZMod.natCast_val, ZMod.cast_id]
    rw [hr]; ring
  obtain ⟨a, ha⟩ := exists_sq_sub_dvd p hp hp2 u hu h1 e he
  refine ⟨((a : ℤ) : ZMod (p ^ e)), ?_⟩
  have : (((a ^ 2 - u : ℤ)) : ZMod (p ^ e)) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact_mod_cast ha
  push_cast at this
  linear_combination -this

/-! ### Proposition 12 -/

/-- **Proposition 12.** For an odd prime `p`, `K` with `v_p(K) = 1` and `e ≥ 2`,
exactly the centres prime to `p` pass: the count is `p ^ e − p ^ (e-1)`. -/
theorem passCard_multiplier_prime (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (K : ℤ)
    (hK1 : (p : ℤ) ∣ K) (hK2 : ¬ ((p : ℤ) ^ 2 ∣ K)) (e : ℕ) (he : 2 ≤ e)
    [NeZero (p ^ e)] :
    passCard ((K : ZMod (p ^ e))) = p ^ e - p ^ (e - 1) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  -- the passing centres are exactly those prime to `p`
  have key : ∀ A : ZMod (p ^ e),
      IsSquare (A ^ 2 - ((K : ℤ) : ZMod (p ^ e))) ↔ ¬ (p ∣ A.val) := by
    intro A
    set a : ℤ := (A.val : ℤ) with hadef
    have hAa : ((a : ℤ) : ZMod (p ^ e)) = A := by
      rw [hadef]; push_cast; rw [ZMod.natCast_val, ZMod.cast_id]
    have hval : ((a ^ 2 - K : ℤ) : ZMod (p ^ e)) = A ^ 2 - ((K : ℤ) : ZMod (p ^ e)) := by
      push_cast [hAa]; ring
    constructor
    · -- passing ⟹ prime to `p`
      intro hsq hdvd
      have hpa : (p : ℤ) ∣ a := by rw [hadef]; exact_mod_cast hdvd
      -- `v_p(a² − K) = 1`
      have hp2a : ((p : ℤ)) ^ 2 ∣ a ^ 2 := by
        obtain ⟨b, hb⟩ := hpa; exact ⟨b ^ 2, by rw [hb]; ring⟩
      have hnot : ¬ (((p : ℤ)) ^ 2 ∣ a ^ 2 - K) := by
        intro h
        exact hK2 (by simpa using dvd_sub hp2a h)
      -- but a square modulo `p^e`, `e ≥ 2`, forces `p² ∣ a² − K`
      rw [← hval] at hsq
      obtain ⟨r, hr⟩ := hsq
      set R : ℤ := (r.val : ℤ) with hRdef
      have hRr : ((R : ℤ) : ZMod (p ^ e)) = r := by
        rw [hRdef]; push_cast; rw [ZMod.natCast_val, ZMod.cast_id]
      have hdvd_e : ((p : ℤ)) ^ e ∣ R ^ 2 - (a ^ 2 - K) := by
        have : (((R ^ 2 - (a ^ 2 - K) : ℤ)) : ZMod (p ^ e)) = 0 := by
          push_cast at hr
          push_cast [hRr]
          rw [hr]; ring
        rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at this
        exact_mod_cast this
      -- `p ∣ a² − K` since `p ∣ a` and `p ∣ K`
      have hpu : (p : ℤ) ∣ a ^ 2 - K := dvd_sub (dvd_pow hpa (by decide)) hK1
      have hpR : (p : ℤ) ∣ R := by
        have h1 : (p : ℤ) ∣ R ^ 2 - (a ^ 2 - K) :=
          dvd_trans (dvd_pow_self (p : ℤ) (by omega)) hdvd_e
        have : (p : ℤ) ∣ R ^ 2 := by simpa using dvd_add h1 hpu
        exact hpZ.dvd_of_dvd_pow this
      have hp2R : ((p : ℤ)) ^ 2 ∣ R ^ 2 := by
        obtain ⟨b, hb⟩ := hpR; exact ⟨b ^ 2, by rw [hb]; ring⟩
      have hp2e : ((p : ℤ)) ^ 2 ∣ R ^ 2 - (a ^ 2 - K) :=
        dvd_trans (pow_dvd_pow (p : ℤ) he) hdvd_e
      exact hnot (by simpa using dvd_sub hp2R hp2e)
    · -- prime to `p` ⟹ passing
      intro hdvd
      have hpa : ¬ ((p : ℤ) ∣ a) := by
        intro h; exact hdvd (by rw [hadef] at h; exact_mod_cast h)
      have hu : ¬ ((p : ℤ) ∣ a ^ 2 - K) := by
        intro h
        exact hpa (hpZ.dvd_of_dvd_pow (by simpa using dvd_add h hK1))
      have hsqp : IsSquare (((a ^ 2 - K : ℤ)) : ZMod p) := by
        refine ⟨((a : ℤ) : ZMod p), ?_⟩
        have hKp : ((K : ℤ) : ZMod p) = 0 := by
          rw [ZMod.intCast_zmod_eq_zero_iff_dvd]; exact_mod_cast hK1
        push_cast [hKp]; ring
      have := isSquare_zmod_pow_of_mod_p p hp hp2 (a ^ 2 - K) hu hsqp e (by omega)
      rwa [hval] at this
  -- rewrite the pass set as the set of centres prime to `p`
  have hfilter : passCard ((K : ZMod (p ^ e)))
      = (Finset.univ.filter fun A : ZMod (p ^ e) => ¬ (p ∣ A.val)).card := by
    unfold passCard
    rw [Finset.filter_congr_decidable]
    exact congrArg Finset.card (Finset.filter_congr fun A _ => by
      simpa using key A)
  -- the complement has `p ^ (e-1)` elements
  have hcompl : (Finset.univ.filter fun A : ZMod (p ^ e) => (p ∣ A.val)).card
      = p ^ (e - 1) := by
    have hbij : (Finset.univ.filter fun A : ZMod (p ^ e) => (p ∣ A.val))
        = (Finset.range (p ^ (e - 1))).image
            (fun j => ((p * j : ℕ) : ZMod (p ^ e))) := by
      ext A
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
        Finset.mem_range]
      constructor
      · rintro ⟨b, hb⟩
        refine ⟨b, ?_, ?_⟩
        · have hlt : A.val < p ^ e := ZMod.val_lt A
          have hpe : p ^ e = p * p ^ (e - 1) := by
            rw [← pow_succ']; congr 1; omega
          apply (Nat.mul_lt_mul_left hp.pos).mp
          rw [← hb, ← hpe]
          exact hlt
        · rw [← hb, ZMod.natCast_val, ZMod.cast_id]
      · rintro ⟨j, hj, rfl⟩
        refine ⟨j, ?_⟩
        have hlt : p * j < p ^ e := by
          have hpe : p ^ e = p * p ^ (e - 1) := by
            rw [← pow_succ']; congr 1; omega
          rw [hpe]
          exact (Nat.mul_lt_mul_left hp.pos).mpr hj
        rw [ZMod.val_cast_of_lt hlt]
    rw [hbij, Finset.card_image_of_injOn, Finset.card_range]
    intro i hi j hj hij
    have hpe : p ^ e = p * p ^ (e - 1) := by
      rw [← pow_succ']; congr 1; omega
    have hi' : p * i < p ^ e := by
      rw [hpe]
      exact (Nat.mul_lt_mul_left hp.pos).mpr (Finset.mem_range.mp hi)
    have hj' : p * j < p ^ e := by
      rw [hpe]
      exact (Nat.mul_lt_mul_left hp.pos).mpr (Finset.mem_range.mp hj)
    have heq := congrArg ZMod.val hij
    rw [ZMod.val_natCast_of_lt hi', ZMod.val_natCast_of_lt hj'] at heq
    exact mul_left_cancel₀ hp.ne_zero heq
  -- combine
  have htot : (Finset.univ.filter fun A : ZMod (p ^ e) => ¬ (p ∣ A.val)).card
      + (Finset.univ.filter fun A : ZMod (p ^ e) => (p ∣ A.val)).card
      = p ^ e := by
    rw [add_comm, Finset.card_filter_add_card_filter_not]
    simp only [Finset.card_univ, ZMod.card]
  rw [hfilter]
  omega

end DyadicShells.MultiplierPrime
