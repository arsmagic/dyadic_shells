/-
Lemma 6 of the paper (Version 11.11.04): the number of squares modulo `2 ^ n`.

With `s(n) = #{squares in ZMod (2^n)}` (Stangl), we prove `s(0) = 1` and, for
`n ≥ 1`,

    6 · s(n) = 2^n + 9 − (−1)^n,

i.e. `6 s(n) = 2^n + 8` for even `n ≥ 2` and `6 s(n) = 2^n + 10` for odd `n`.

PROOF.  Everything rests on the recursion `s(n+2) = s(n) + 2^(n-1)` (`n ≥ 1`),
obtained by splitting the squares modulo `2^(n+2)` by parity:

  * an ODD residue is a square mod `2^m` (`m ≥ 3`) iff it is `≡ 1 (mod 8)`
    (`isSqMod_odd_iff`), and there are `2^(m-3)` such residues;
  * an EVEN square is divisible by `4` (`dvd_four_of_isSqMod_even`), and
    `4t` is a square mod `2^(n+2)` iff `t` is a square mod `2^n`
    (`isSqMod_four_mul_iff`, the halving step).

The two inputs from the repository are `odd_sq_modEq_one_eight` and
`isSquare_mod_two_pow_of_one_mod_eight` (Hensel lifting for `c ≡ 1 mod 8`);
the rest is elementary congruence arithmetic.
-/
import Mathlib
import DyadicShells.TwoAdicSaturation

namespace DyadicShells.SquareCount

open Finset DyadicShells

/-- `a` is a square modulo `2 ^ k`, stated with integer congruences (the form in
which the repository's two-adic lemmas are available). -/
def IsSqMod (k : ℕ) (a : ℤ) : Prop := ∃ y : ℤ, y ^ 2 ≡ a [ZMOD 2 ^ k]

open Classical in
/-- `s(k)`: the number of squares modulo `2 ^ k`, counted on the representatives
`0, …, 2^k − 1`.  `sqCard_eq_card_zmod` identifies it with the number of squares
of the ring `ZMod (2^k)`. -/
noncomputable def sqCard (k : ℕ) : ℕ :=
  ((Finset.range (2 ^ k)).filter fun a : ℕ => IsSqMod k (a : ℤ)).card

private theorem neZero_two_pow (k : ℕ) : NeZero ((2 : ℕ) ^ k) := ⟨by positivity⟩

/-! ### Bridge to `ZMod` -/

theorem isSqMod_iff_isSquare (k : ℕ) (a : ℤ) :
    IsSqMod k a ↔ IsSquare ((a : ZMod (2 ^ k))) := by
  haveI := neZero_two_pow k
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨((y : ℤ) : ZMod (2 ^ k)), ?_⟩
    have : (((y ^ 2 : ℤ)) : ZMod (2 ^ k)) = ((a : ℤ) : ZMod (2 ^ k)) := by
      rw [ZMod.intCast_eq_intCast_iff]
      exact_mod_cast hy
    push_cast at this
    rw [← this]; ring
  · rintro ⟨r, hr⟩
    refine ⟨(r.val : ℤ), ?_⟩
    have hrv : ((r.val : ℤ) : ZMod (2 ^ k)) = r := by
      push_cast; rw [ZMod.natCast_val, ZMod.cast_id]
    have : ((((r.val : ℤ) ^ 2 : ℤ)) : ZMod (2 ^ k)) = ((a : ℤ) : ZMod (2 ^ k)) := by
      push_cast [hrv]
      rw [hr]; ring
    rw [ZMod.intCast_eq_intCast_iff] at this
    exact_mod_cast this

/-- `s(k)` really is the number of squares of `ZMod (2^k)`. -/
theorem sqCard_eq_card_zmod (k : ℕ) :
    sqCard k = (Finset.univ.filter fun r : ZMod (2 ^ k) => IsSquare r).card := by
  classical
  haveI := neZero_two_pow k
  unfold sqCard
  refine Finset.card_bij' (fun a _ => ((a : ℕ) : ZMod (2 ^ k)))
    (fun r _ => r.val) ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_range] at ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have := (isSqMod_iff_isSquare k (a : ℤ)).mp ha.2
    simpa using this
  · intro r hr
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨ZMod.val_lt r, ?_⟩
    rw [isSqMod_iff_isSquare]
    have hrv : (((r.val : ℕ) : ℤ) : ZMod (2 ^ k)) = r := by
      push_cast; rw [ZMod.natCast_val, ZMod.cast_id]
    rwa [hrv]
  · intro a ha
    simp only [Finset.mem_filter, Finset.mem_range] at ha
    exact ZMod.val_cast_of_lt ha.1
  · intro r _
    rw [ZMod.natCast_val, ZMod.cast_id]

/-! ### The two structural facts -/

/-- An odd residue is a square modulo `2^m` (`m ≥ 3`) iff it is `≡ 1 (mod 8)`. -/
theorem isSqMod_odd_iff (m : ℕ) (hm : 3 ≤ m) (a : ℤ) (ha : ¬ (2 : ℤ) ∣ a) :
    IsSqMod m a ↔ a ≡ 1 [ZMOD 8] := by
  have h8 : (8 : ℤ) ∣ 2 ^ m := by
    have : (2 : ℤ) ^ 3 ∣ 2 ^ m := pow_dvd_pow 2 hm
    norm_num at this; exact this
  constructor
  · rintro ⟨y, hy⟩
    -- `y` is odd, else `a` would be even
    have hyodd : Odd y := by
      rcases Int.even_or_odd y with hev | hod
      · exfalso
        obtain ⟨c, hc⟩ := hev
        have h2 : (2 : ℤ) ∣ 2 ^ m := dvd_pow_self 2 (by omega)
        have hya := (hy.of_dvd h2)
        apply ha
        have hy2 : (2 : ℤ) ∣ y ^ 2 := by rw [hc]; exact ⟨2 * c * c, by ring⟩
        have hd := Int.ModEq.dvd hya
        simpa using dvd_add hd hy2
      · exact hod
    have h1 : y ^ 2 ≡ 1 [ZMOD 8] := odd_sq_modEq_one_eight y hyodd
    have h2 : y ^ 2 ≡ a [ZMOD 8] := hy.of_dvd h8
    exact h2.symm.trans h1
  · intro h
    obtain ⟨y, hy⟩ := isSquare_mod_two_pow_of_one_mod_eight a (by
      -- `a ≡ 1 (mod 8)`
      exact h) m
    exact ⟨y, hy⟩

/-- An even square modulo `2^m` (`m ≥ 2`) is divisible by `4`. -/
theorem dvd_four_of_isSqMod_even (m : ℕ) (hm : 2 ≤ m) (a : ℤ)
    (hsq : IsSqMod m a) (ha : (2 : ℤ) ∣ a) : (4 : ℤ) ∣ a := by
  obtain ⟨y, hy⟩ := hsq
  have h4 : (4 : ℤ) ∣ 2 ^ m := by
    have : (2 : ℤ) ^ 2 ∣ 2 ^ m := pow_dvd_pow 2 hm
    norm_num at this; exact this
  have hy4 : y ^ 2 ≡ a [ZMOD 4] := hy.of_dvd h4
  -- `y` is even
  have hyev : (2 : ℤ) ∣ y := by
    by_contra hodd
    have : Odd y := Int.odd_iff.mpr (by omega)
    have h1 : y ^ 2 ≡ 1 [ZMOD 8] := odd_sq_modEq_one_eight y this
    have h2 : y ^ 2 ≡ 1 [ZMOD 2] := h1.of_dvd (by norm_num)
    have h3 : a ≡ 1 [ZMOD 2] := by
      have h2' : y ^ 2 ≡ a [ZMOD 2] := hy.of_dvd (dvd_pow_self 2 (by omega))
      exact h2'.symm.trans h2
    rw [Int.ModEq] at h3
    omega
  obtain ⟨c, hc⟩ := hyev
  have : (4 : ℤ) ∣ y ^ 2 := ⟨c ^ 2, by rw [hc]; ring⟩
  have hd := Int.ModEq.dvd hy4
  simpa using dvd_add hd this

/-- Halving: `4t` is a square modulo `2^(k+2)` iff `t` is a square modulo `2^k`. -/
theorem isSqMod_four_mul_iff (k : ℕ) (t : ℤ) :
    IsSqMod (k + 2) (4 * t) ↔ IsSqMod k t := by
  have hpow : (2 : ℤ) ^ (k + 2) = 4 * 2 ^ k := by rw [pow_add]; ring
  constructor
  · rintro ⟨r, hr⟩
    -- `r` is even
    have h4 : (4 : ℤ) ∣ r ^ 2 := by
      have hd : (2 : ℤ) ^ (k + 2) ∣ r ^ 2 - 4 * t := Int.ModEq.dvd hr.symm
      rw [hpow] at hd
      obtain ⟨c, hc⟩ := hd
      exact ⟨t + 2 ^ k * c, by linarith [hc]⟩
    have hrev : (2 : ℤ) ∣ r := by
      rcases Int.even_or_odd r with hev | hod
      · exact hev.two_dvd
      · exfalso
        obtain ⟨j, hj⟩ := hod
        obtain ⟨c, hc⟩ := h4
        rw [hj] at hc
        have heq : 4 * (j * j + j) + 1 = 4 * c := by nlinarith [hc]
        omega
    obtain ⟨y, hy⟩ := hrev
    refine ⟨y, ?_⟩
    have hd : (2 : ℤ) ^ (k + 2) ∣ r ^ 2 - 4 * t := Int.ModEq.dvd hr.symm
    rw [hpow, hy] at hd
    obtain ⟨c, hc⟩ := hd
    refine Int.ModEq.symm (Int.modEq_iff_dvd.mpr ⟨c, ?_⟩)
    linarith [hc]
  · rintro ⟨y, hy⟩
    refine ⟨2 * y, ?_⟩
    have hd : (2 : ℤ) ^ k ∣ y ^ 2 - t := Int.ModEq.dvd hy.symm
    obtain ⟨c, hc⟩ := hd
    refine Int.ModEq.symm (Int.modEq_iff_dvd.mpr ⟨c, ?_⟩)
    rw [hpow]
    linarith [hc]

/-! ### Counting -/

/-- There are `2^(m-3)` residues `≡ 1 (mod 8)` below `2^m`, for `m ≥ 3`. -/
theorem card_one_mod_eight (m : ℕ) (hm : 3 ≤ m) :
    ((Finset.range (2 ^ m)).filter fun a : ℕ => a % 8 = 1).card = 2 ^ (m - 3) := by
  have hpow : (2 : ℕ) ^ m = 8 * 2 ^ (m - 3) := by
    conv_lhs => rw [show m = 3 + (m - 3) from by omega]
    rw [pow_add]; norm_num
  have himg : ((Finset.range (2 ^ m)).filter fun a : ℕ => a % 8 = 1)
      = (Finset.range (2 ^ (m - 3))).image (fun j => 8 * j + 1) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hlt, hmod⟩
      exact ⟨a / 8, by omega, by omega⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨by omega, by omega⟩
  rw [himg, Finset.card_image_of_injective _ (fun x y h => by omega), Finset.card_range]

/-- **The recursion** `s(k+2) = s(k) + 2^(k-1)` for `k ≥ 1`. -/
theorem sqCard_add_two (k : ℕ) (hk : 1 ≤ k) :
    sqCard (k + 2) = sqCard k + 2 ^ (k - 1) := by
  classical
  have hpowk : (2 : ℕ) ^ (k + 2) = 4 * 2 ^ k := by rw [pow_add]; ring
  set S := (Finset.range (2 ^ (k + 2))).filter fun a : ℕ => IsSqMod (k + 2) (a : ℤ) with hSdef
  -- odd part
  have hodd : (S.filter fun a : ℕ => a % 2 = 1)
      = (Finset.range (2 ^ (k + 2))).filter fun a : ℕ => a % 8 = 1 := by
    ext a
    simp only [hSdef, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨⟨hlt, hsq⟩, hpar⟩
      refine ⟨hlt, ?_⟩
      have hna : ¬ (2 : ℤ) ∣ (a : ℤ) := by omega
      have := (isSqMod_odd_iff (k + 2) (by omega) (a : ℤ) hna).mp hsq
      rw [Int.ModEq] at this
      omega
    · rintro ⟨hlt, hmod⟩
      have hna : ¬ (2 : ℤ) ∣ (a : ℤ) := by omega
      refine ⟨⟨hlt, ?_⟩, by omega⟩
      refine (isSqMod_odd_iff (k + 2) (by omega) (a : ℤ) hna).mpr ?_
      rw [Int.ModEq]
      omega
  -- even part
  have heven : (S.filter fun a : ℕ => ¬ (a % 2 = 1))
      = ((Finset.range (2 ^ k)).filter fun t : ℕ => IsSqMod k (t : ℤ)).image
          (fun t => 4 * t) := by
    ext a
    simp only [hSdef, Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨⟨hlt, hsq⟩, hpar⟩
      have ha2 : (2 : ℤ) ∣ (a : ℤ) := by omega
      have ha4 : (4 : ℤ) ∣ (a : ℤ) :=
        dvd_four_of_isSqMod_even (k + 2) (by omega) (a : ℤ) hsq ha2
      have ha4' : 4 ∣ a := by exact_mod_cast ha4
      obtain ⟨t, rfl⟩ := ha4'
      refine ⟨t, ⟨by omega, ?_⟩, rfl⟩
      have hcast : ((4 * t : ℕ) : ℤ) = 4 * (t : ℤ) := by push_cast; ring
      rw [hcast] at hsq
      exact (isSqMod_four_mul_iff k (t : ℤ)).mp hsq
    · rintro ⟨t, ⟨hlt, hsq⟩, rfl⟩
      have hcast : ((4 * t : ℕ) : ℤ) = 4 * (t : ℤ) := by push_cast; ring
      refine ⟨⟨by omega, ?_⟩, by omega⟩
      rw [hcast]
      exact (isSqMod_four_mul_iff k (t : ℤ)).mpr hsq
  -- put the two halves together
  have hcard : S.card = (S.filter fun a : ℕ => a % 2 = 1).card
      + (S.filter fun a : ℕ => ¬ (a % 2 = 1)).card :=
    (Finset.card_filter_add_card_filter_not (s := S) (fun a : ℕ => a % 2 = 1)).symm
  rw [hodd, heven, card_one_mod_eight (k + 2) (by omega),
    Finset.card_image_of_injective _ (fun x y h => by omega)] at hcard
  have hk3 : k + 2 - 3 = k - 1 := by omega
  rw [hk3] at hcard
  simpa only [sqCard, ← hSdef, add_comm] using hcard

/-! ### Closed form -/

theorem sqCard_zero : sqCard 0 = 1 := by
  rw [sqCard_eq_card_zmod]
  decide

theorem sqCard_one : sqCard 1 = 2 := by
  rw [sqCard_eq_card_zmod]
  rw [Finset.filter_congr_decidable]
  decide

theorem sqCard_two : sqCard 2 = 2 := by
  rw [sqCard_eq_card_zmod]
  rw [Finset.filter_congr_decidable]
  decide

/-- **Lemma 6, odd case.** `6 s(n) = 2^n + 10` for odd `n`. -/
theorem sqCard_odd_closed (n : ℕ) (hn : Odd n) : 6 * sqCard n = 2 ^ n + 10 := by
  obtain ⟨j, rfl⟩ := hn
  induction j with
  | zero => norm_num [sqCard_one]
  | succ i ih =>
      have hrec : sqCard (2 * (i + 1) + 1) = sqCard (2 * i + 1) + 2 ^ (2 * i + 1 - 1) := by
        have : 2 * (i + 1) + 1 = (2 * i + 1) + 2 := by ring
        rw [this]
        exact sqCard_add_two (2 * i + 1) (by omega)
      rw [hrec]
      have hpow : (2 : ℕ) ^ (2 * (i + 1) + 1) = 8 * 2 ^ (2 * i) := by
        rw [show 2 * (i + 1) + 1 = (2 * i) + 3 from by ring, pow_add]; ring
      have hpow2 : (2 : ℕ) ^ (2 * i + 1) = 2 * 2 ^ (2 * i) := by
        rw [pow_succ]; ring
      have hsub : 2 * i + 1 - 1 = 2 * i := by omega
      rw [hsub, hpow, mul_add, ih, hpow2]
      omega

/-- **Lemma 6, even case.** `6 s(n) = 2^n + 8` for even `n ≥ 2`. -/
theorem sqCard_even_closed (n : ℕ) (hn : 2 ≤ n) (hpar : Even n) :
    6 * sqCard n = 2 ^ n + 8 := by
  obtain ⟨j, rfl⟩ := hpar
  have hj : 1 ≤ j := by omega
  clear hn
  induction j, hj using Nat.le_induction with
  | base => norm_num [sqCard_two]
  | succ i hi ih =>
      have hrec : sqCard (i + 1 + (i + 1)) = sqCard (i + i) + 2 ^ (i + i - 1) := by
        have : i + 1 + (i + 1) = (i + i) + 2 := by ring
        rw [this]
        exact sqCard_add_two (i + i) (by omega)
      rw [hrec]
      have hpow : (2 : ℕ) ^ (i + 1 + (i + 1)) = 4 * 2 ^ (i + i) := by
        rw [show i + 1 + (i + 1) = (i + i) + 2 from by ring, pow_add]; ring
      have hpow2 : (2 : ℕ) ^ (i + i) = 2 * 2 ^ (i + i - 1) := by
        conv_lhs => rw [show i + i = (i + i - 1) + 1 from by omega]
        rw [pow_succ]; ring
      rw [hpow]
      omega

/-- **Lemma 6.** `6 s(n) = 2^n + 9 − (−1)^n` for `n ≥ 1`. -/
theorem sqCard_closed (n : ℕ) (hn : 1 ≤ n) :
    6 * (sqCard n : ℤ) = 2 ^ n + 9 - (-1 : ℤ) ^ n := by
  rcases Nat.even_or_odd n with hpar | hpar
  · have h := sqCard_even_closed n (by
      rcases Nat.eq_or_lt_of_le hn with h1 | h1
      · exact absurd (h1 ▸ hpar) (by decide)
      · omega) hpar
    have hsign : (-1 : ℤ) ^ n = 1 := hpar.neg_one_pow
    have := congrArg (fun k : ℕ => (k : ℤ)) h
    push_cast at this
    rw [hsign]
    linarith [this]
  · have h := sqCard_odd_closed n hpar
    have hsign : (-1 : ℤ) ^ n = -1 := hpar.neg_one_pow
    have := congrArg (fun k : ℕ => (k : ℤ)) h
    push_cast at this
    rw [hsign]
    linarith [this]

end DyadicShells.SquareCount
