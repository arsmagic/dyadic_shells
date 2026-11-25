/-
Target 4, milestone C (Theorem 3 of v11.7.23). The hyperbolic sieve modulo 2^e.

`hyperbolicSieveSet N k` over `ZMod M` is Hittmeir's `L_{N,M,k} = {k·x + y : x·y = N}`.
For odd `N, k` and `M = 2^e` the main identity is the doubled form of Theorem 3:

    2 * |L_{N,2^e,k}| = C_e(k·N)        (= passCard ((k·N : ZMod 2^e)))

Scheme (author's hint): reduce `k` to `1` (k is a unit mod 2^e), then map passing
half-centres `a ↦ 2a`; each fibre has exactly two elements — the fibre-pair
technique behind `passCard_succ_lift` / `lift_fibre_card` / `lift_sq_eq`. The
reduction `passCard (K at 2^(k+1)) = 2 * |S_k|` is already `passCard_succ_lift`,
so the only genuinely new step is `card_sieve_eq_halfcentres` (|L| = |S_k|).
The `/2` form is a corollary.
-/
import Mathlib
import DyadicShells.TwoAdicExact
import ClosedForms

namespace DyadicShells.HyperbolicSieve

open DyadicShells DyadicShells.ClosedForms Finset

variable {M : ℕ} [NeZero M]

/-- Hittmeir's hyperbolic sieve set `L_{N,M,k} = { k·x + y : x·y = N }` as a finset
of residues modulo `M`. -/
def hyperbolicSieveSet (N k : ZMod M) : Finset (ZMod M) :=
  (Finset.univ.filter (fun p : ZMod M × ZMod M => p.1 * p.2 = N)).image
    (fun p => k * p.1 + p.2)

/-- Membership unfolded. -/
theorem mem_hyperbolicSieveSet {N k z : ZMod M} :
    z ∈ hyperbolicSieveSet N k ↔ ∃ x y : ZMod M, x * y = N ∧ k * x + y = z := by
  classical
  simp only [hyperbolicSieveSet, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
    true_and, Prod.exists]

/-- **Lemma A (unit reduction).** A unit multiplier `k` is absorbed into `N`:
`L_{N,M,k} = L_{k·N,M,1}`. The substitution `x ↦ k·x` bijects the solution pairs. -/
theorem hyperbolicSieveSet_unit (N : ZMod M) (k : (ZMod M)ˣ) :
    hyperbolicSieveSet N (k : ZMod M) = hyperbolicSieveSet ((k : ZMod M) * N) 1 := by
  have hkk : (k : ZMod M) * ((k⁻¹ : (ZMod M)ˣ) : ZMod M) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hkk' : ((k⁻¹ : (ZMod M)ˣ) : ZMod M) * (k : ZMod M) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  ext z
  rw [mem_hyperbolicSieveSet, mem_hyperbolicSieveSet]
  constructor
  · rintro ⟨x, y, hxy, hz⟩
    refine ⟨(k : ZMod M) * x, y, ?_, ?_⟩
    · rw [mul_assoc, hxy]
    · rw [one_mul]; exact hz
  · rintro ⟨x, y, hxy, hz⟩
    rw [one_mul] at hz
    refine ⟨((k⁻¹ : (ZMod M)ˣ) : ZMod M) * x, y, ?_, ?_⟩
    · rw [mul_assoc, hxy, ← mul_assoc, hkk', one_mul]
    · rw [← mul_assoc, hkk, one_mul, hz]

/-- **Base case `e = 1`.** `L_{N,2,1} = {0}` and `C_1(N) = 2` for odd `N`.
TODO: reduce `(K : ZMod 2) = 1` from `Odd K`, then evaluate both sides. -/
theorem card_base_one (K : ℤ) (hK : Odd K) :
    2 * (hyperbolicSieveSet ((K : ℤ) : ZMod (2 ^ 1)) 1).card
      = passCard ((K : ℤ) : ZMod (2 ^ 1)) := by
  have hK1 : ((K : ℤ) : ZMod (2 ^ 1)) = 1 := by
    have h : ((K - 1 : ℤ) : ZMod (2 ^ 1)) = 0 := by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
      obtain ⟨m, hm⟩ := hK
      exact ⟨m, by rw [hm]; push_cast; ring⟩
    push_cast at h
    linear_combination h
  have hL : (hyperbolicSieveSet (1 : ZMod (2 ^ 1)) 1).card = 1 := by decide
  have hP : passCard (1 : ZMod (2 ^ 1)) = 2 := by
    unfold passCard; rw [Finset.filter_congr_decidable]; decide
  simp only [hK1, hL, hP, mul_one]

/-- **Lemma B (half-centre bijection).** For odd `K` and `k ≥ 1`, the sieve set
`L_{K,2^(k+1),1}` is in bijection with the passing half-centres at level `k` whose
lift passes at level `k+1`, via `b ↦ 2·b`. The map `a ↦ 2a` sends `ℤ/2^k` onto the
even residues mod `2^(k+1)`; `2a ∈ L ⇔ a²−K is a square mod 2^(k+1)`; and squareness
depends only on `a mod 2^k` (that is `lift_sq_eq` with shift `2^k`).
This is the one genuinely new step. -/
theorem card_sieve_eq_halfcentres {k : ℕ} (hk : 1 ≤ k) (K : ℤ) (hK : Odd K) :
    (hyperbolicSieveSet ((K : ℤ) : ZMod (2 ^ (k + 1))) 1).card
      = (Finset.univ.filter (fun b : ZMod (2 ^ k) =>
            IsSquare (b ^ 2 - ((K : ℤ) : ZMod (2 ^ k))) ∧
            IsSquare (((b.val : ℤ) : ZMod (2 ^ (k + 1))) ^ 2
                        - ((K : ℤ) : ZMod (2 ^ (k + 1)))))).card := by
  classical
  haveI : NeZero (2 ^ k) := ⟨pow_ne_zero _ two_ne_zero⟩
  haveI : NeZero (2 ^ (k + 1)) := ⟨pow_ne_zero _ two_ne_zero⟩
  have hpow : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
  refine (Finset.card_bij
    (fun (b : ZMod (2 ^ k)) (_ : b ∈ _) =>
      (2 : ZMod (2 ^ (k + 1))) * ((b.val : ℤ) : ZMod (2 ^ (k + 1)))) ?hi ?inj ?surj).symm
  case hi =>
    intro b hb
    rw [Finset.mem_filter] at hb
    obtain ⟨s, hs⟩ := hb.2.2
    rw [mem_hyperbolicSieveSet]
    refine ⟨((b.val : ℤ) : ZMod (2 ^ (k + 1))) + s,
            ((b.val : ℤ) : ZMod (2 ^ (k + 1))) - s, ?_, ?_⟩
    · linear_combination hs
    · ring
  case inj =>
    intro b1 hb1 b2 hb2 heq
    have e1 : 2 * b1.val < 2 ^ (k + 1) := by have := b1.val_lt; omega
    have e2 : 2 * b2.val < 2 ^ (k + 1) := by have := b2.val_lt; omega
    have hnat : ((2 * b1.val : ℕ) : ZMod (2 ^ (k + 1)))
        = ((2 * b2.val : ℕ) : ZMod (2 ^ (k + 1))) := by
      push_cast at heq ⊢; linear_combination heq
    rw [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt e1, Nat.mod_eq_of_lt e2] at hnat
    have hval : b1.val = b2.val := by omega
    rw [← ZMod.natCast_zmod_val b1, ← ZMod.natCast_zmod_val b2, hval]
  case surj =>
    intro z hz
    rw [mem_hyperbolicSieveSet] at hz
    obtain ⟨x, y, hxy, hz0⟩ := hz
    rw [one_mul] at hz0
    have hKunit : IsUnit ((K : ℤ) : ZMod (2 ^ (k + 1))) := by
      obtain ⟨a, ha⟩ := exists_inv_of_odd (k + 1) K hK
      exact (Units.mkOfMulEqOne ((K : ℤ) : ZMod (2 ^ (k + 1))) (a : ZMod (2 ^ (k + 1)))
        (by rw [mul_comm]; exact ha)).isUnit
    have hxyu : IsUnit (x * y) := by rw [hxy]; exact hKunit
    have hxu : IsUnit x := isUnit_of_mul_isUnit_left hxyu
    have hyu : IsUnit y := isUnit_of_mul_isUnit_right hxyu
    have hdvd2 : (2 : ℕ) ∣ 2 ^ (k + 1) := dvd_pow_self 2 (Nat.succ_ne_zero k)
    have hunit1 : ∀ u : ZMod 2, IsUnit u → u = 1 := by decide
    have hred : (ZMod.castHom hdvd2 (ZMod 2)) z = 0 := by
      rw [← hz0, map_add,
        hunit1 _ (hxu.map (ZMod.castHom hdvd2 (ZMod 2))),
        hunit1 _ (hyu.map (ZMod.castHom hdvd2 (ZMod 2)))]
      decide
    have hzeven : 2 ∣ z.val := by
      have h0 : ((z.val : ℕ) : ZMod 2) = 0 := by
        rw [ZMod.castHom_apply, ← ZMod.natCast_val] at hred; exact hred
      exact (CharP.cast_eq_zero_iff (ZMod 2) 2 z.val).mp h0
    obtain ⟨c, hc⟩ := hzeven
    have hc_lt : c < 2 ^ k := by have := z.val_lt; omega
    have hbval : ((c : ZMod (2 ^ k))).val = c := ZMod.val_natCast_of_lt hc_lt
    have hval2 : 2 * ((((c : ZMod (2 ^ k))).val : ℤ) : ZMod (2 ^ (k + 1))) = x + y := by
      rw [hbval, hz0, ← ZMod.natCast_zmod_val z, hc]; push_cast; ring
    refine ⟨(c : ZMod (2 ^ k)), ?_, ?_⟩
    · have hsq2 : IsSquare (((((c : ZMod (2 ^ k))).val : ℤ) : ZMod (2 ^ (k + 1))) ^ 2
          - ((K : ℤ) : ZMod (2 ^ (k + 1)))) := by
        refine ⟨((((c : ZMod (2 ^ k))).val : ℤ) : ZMod (2 ^ (k + 1))) - x, ?_⟩
        linear_combination x * hval2 + hxy
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_, hsq2⟩
      have hred2 := pass_of_reduce (pow_dvd_pow 2 (Nat.le_succ k))
        ((K : ℤ) : ZMod (2 ^ (k + 1)))
        ((((c : ZMod (2 ^ k))).val : ℤ) : ZMod (2 ^ (k + 1))) hsq2
      simp only [map_intCast] at hred2
      rwa [show (((((c : ZMod (2 ^ k))).val : ℤ)) : ZMod (2 ^ k)) = (c : ZMod (2 ^ k)) from by
        rw [Int.cast_natCast]; exact ZMod.natCast_zmod_val _] at hred2
    · rw [hbval, ← ZMod.natCast_zmod_val z, hc]; push_cast; ring

/-- **Core identity (doubled form) for `e = k+1 ≥ 2`, multiplier `1`.** -/
theorem two_mul_card_sieve_succ {k : ℕ} (hk : 1 ≤ k) (K : ℤ) (hK : Odd K) :
    2 * (hyperbolicSieveSet ((K : ℤ) : ZMod (2 ^ (k + 1))) 1).card
      = passCard ((K : ℤ) : ZMod (2 ^ (k + 1))) := by
  rw [card_sieve_eq_halfcentres hk K hK, passCard_succ_lift hk K]

/-- **Core identity (doubled form) for any `e ≥ 1`, multiplier `1`.** -/
theorem two_mul_card_sieve_one (K : ℤ) (hK : Odd K) (e : ℕ) (he : 1 ≤ e)
    [NeZero (2 ^ e)] :
    2 * (hyperbolicSieveSet ((K : ℤ) : ZMod (2 ^ e)) 1).card
      = passCard ((K : ℤ) : ZMod (2 ^ e)) := by
  obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
  rcases Nat.eq_zero_or_pos e' with he0 | hepos
  · subst he0; exact card_base_one K hK
  · exact two_mul_card_sieve_succ hepos K hK

/-- **Theorem 3 (doubled form).** For odd `N, k` and `e ≥ 1`,
`2 · |L_{N,2^e,k}| = C_e(k·N)`. -/
theorem two_mul_card_hyperbolicSieve (N k : ℤ) (hN : Odd N) (hk : Odd k) (e : ℕ)
    (he : 1 ≤ e) [NeZero (2 ^ e)] :
    2 * (hyperbolicSieveSet ((N : ℤ) : ZMod (2 ^ e)) ((k : ℤ) : ZMod (2 ^ e))).card
      = passCard (((k * N : ℤ)) : ZMod (2 ^ e)) := by
  have hkunit : IsUnit ((k : ℤ) : ZMod (2 ^ e)) := by
    obtain ⟨a, ha⟩ := exists_inv_of_odd e k hk
    exact (Units.mkOfMulEqOne ((k : ℤ) : ZMod (2 ^ e)) (a : ZMod (2 ^ e))
      (by rw [mul_comm]; exact ha)).isUnit
  rw [show ((k : ℤ) : ZMod (2 ^ e)) = (hkunit.unit : ZMod (2 ^ e)) from hkunit.unit_spec.symm,
      hyperbolicSieveSet_unit,
      show (hkunit.unit : ZMod (2 ^ e)) * ((N : ℤ) : ZMod (2 ^ e))
            = (((k * N : ℤ)) : ZMod (2 ^ e)) from by
        rw [hkunit.unit_spec]; push_cast; ring]
  exact two_mul_card_sieve_one (k * N) (hk.mul hN) e he

/-- **Theorem 3 (`/2` form).** `|L_{N,2^e,k}| = C_e(k·N)/2`. -/
theorem card_hyperbolicSieve_eq_half (N k : ℤ) (hN : Odd N) (hk : Odd k) (e : ℕ)
    (he : 1 ≤ e) [NeZero (2 ^ e)] :
    (hyperbolicSieveSet ((N : ℤ) : ZMod (2 ^ e)) ((k : ℤ) : ZMod (2 ^ e))).card
      = passCard (((k * N : ℤ)) : ZMod (2 ^ e)) / 2 := by
  rw [← two_mul_card_hyperbolicSieve N k hN hk e he,
      Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]

end DyadicShells.HyperbolicSieve
