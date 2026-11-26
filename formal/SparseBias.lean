/-
Low-bit gates of the two-adic square condition (Proposition 1 of the sparse-bias
note) and the binomial asymptotics behind the sparse-family bias (Corollary 4).

PART 1 (gates) is the primary target for this build cycle: it plugs directly into
`DyadicShells.ClosedForms.pass_char_three` and should be short and axiom-clean.

  N ≡ 3 (mod 8):  A²−N is a square mod 2^k  ⟺  A ≡ 2 (mod 4)   [castHom to ZMod 8 ∈ {2,6}]
  N ≡ 7 (mod 8):  A²−N is a square mod 2^k  ⟺  A ≡ 0 (mod 4)   [castHom to ZMod 8 ∈ {0,4}]

PART 2 (binomial ratio limits) is the arithmetic core of Corollary 4 (sparse
window b → ∞ at fixed Hamming weight t): the gate mass ratio → 1 (N≡7) / → 0
(N≡3). Stated over `Nat.choose` only; the binary-encoding bridge
(#{A<2^b : popcount ≤ t, A ≡ r mod 4} = Σ_{w≤t} C(b-2, w-·)) is a SEPARATE step,
not attempted here.
-/
import Mathlib
import DyadicShells.TwoAdicExact
import ClosedForms

namespace DyadicShells.SparseBias

open DyadicShells DyadicShells.ClosedForms

/-! ### Part 1 — exact low-bit gates (Proposition 1) -/

/-- **Gate, `N ≡ 3 (mod 8)`.** For `k ≥ 3`, a centre `A` passes iff `A ≡ 2 (mod 4)`,
expressed as `castHom A ∈ {2,6}` in `ZMod 8`. -/
theorem gate_three_mod_eight {k : ℕ} (h8 : (8 : ℕ) ∣ 2 ^ k) (N : ℤ) (hN : N ≡ 3 [ZMOD 8])
    (A : ZMod (2 ^ k)) :
    IsSquare (A ^ 2 - ((N : ℤ) : ZMod (2 ^ k)))
      ↔ (ZMod.castHom h8 (ZMod 8) A = 2 ∨ ZMod.castHom h8 (ZMod 8) A = 6) := by
  -- N ≡ 3 (mod 8) ⇒ N ≡ 3 (mod 4)
  have hN4 : N ≡ 3 [ZMOD 4] :=
    Int.modEq_iff_dvd.mpr (dvd_trans (by norm_num : (4 : ℤ) ∣ 8) (Int.modEq_iff_dvd.mp hN))
  -- image of N in ZMod 8 is 3
  have hNimg : ZMod.castHom h8 (ZMod 8) ((N : ℤ) : ZMod (2 ^ k)) = 3 := by
    rw [map_intCast]
    have h3 : ((N : ℤ) : ZMod 8) = ((3 : ℤ) : ZMod 8) :=
      (ZMod.intCast_eq_intCast_iff _ _ _).mpr hN
    rw [h3]; norm_num
  rw [pass_char_three h8 N hN4 A, map_sub, map_pow, hNimg]
  -- finite check over ZMod 8
  have key : ∀ a : ZMod 8, (a ^ 2 - 3 = 1 ↔ a = 2 ∨ a = 6) := by decide
  exact key _

/-- **Gate, `N ≡ 7 (mod 8)`.** For `k ≥ 3`, a centre `A` passes iff `A ≡ 0 (mod 4)`,
expressed as `castHom A ∈ {0,4}` in `ZMod 8`. -/
theorem gate_seven_mod_eight {k : ℕ} (h8 : (8 : ℕ) ∣ 2 ^ k) (N : ℤ) (hN : N ≡ 7 [ZMOD 8])
    (A : ZMod (2 ^ k)) :
    IsSquare (A ^ 2 - ((N : ℤ) : ZMod (2 ^ k)))
      ↔ (ZMod.castHom h8 (ZMod 8) A = 0 ∨ ZMod.castHom h8 (ZMod 8) A = 4) := by
  have hN4 : N ≡ 3 [ZMOD 4] := by
    have h := Int.modEq_iff_dvd.mp hN   -- 8 ∣ 7 - N
    exact Int.modEq_iff_dvd.mpr (by omega)
  have hNimg : ZMod.castHom h8 (ZMod 8) ((N : ℤ) : ZMod (2 ^ k)) = 7 := by
    rw [map_intCast]
    have h7 : ((N : ℤ) : ZMod 8) = ((7 : ℤ) : ZMod 8) :=
      (ZMod.intCast_eq_intCast_iff _ _ _).mpr hN
    rw [h7]; norm_num
  rw [pass_char_three h8 N hN4 A, map_sub, map_pow, hNimg]
  have key : ∀ a : ZMod 8, (a ^ 2 - 7 = 1 ↔ a = 0 ∨ a = 4) := by decide
  exact key _

/-- **Gate, `N ≡ 5 (mod 8)`.** The clean value form of the gate is
`A²−N ≡ 4 (mod 32)` — already established as `ClosedForms.pass_char_five`; this is
its restatement in the sparse-bias namespace, parallel to the `mod 8` gates above.
Unlike the `N ≡ 3, 7` cases, there is no `N`-uniform condition on `A mod 4`: the
surviving `A`-classes mod 16 depend on `N mod 32` (see `gate_five_count_mod32`). -/
theorem gate_five_mod_eight {k : ℕ} (h32 : (32 : ℕ) ∣ 2 ^ k) (N : ℤ) (hN : N ≡ 5 [ZMOD 8])
    (A : ZMod (2 ^ k)) :
    IsSquare (A ^ 2 - ((N : ℤ) : ZMod (2 ^ k)))
      ↔ ZMod.castHom h32 (ZMod 32) (A ^ 2 - ((N : ℤ) : ZMod (2 ^ k))) = 4 :=
  pass_char_five h32 N hN A

/-- The `N ≡ 5 (mod 8)` gate selects exactly **four** residues mod 32, i.e. exactly
**two classes mod 16** (density `1/8`). Decidable: for every `n : ZMod 32` with
`n ∈ {5,13,21,29}` (the image of `N ≡ 5 (mod 8)`), `#{a : a²−n = 4} = 4`. -/
theorem gate_five_count_mod32 (n : ZMod 32) (hn : n = 5 ∨ n = 13 ∨ n = 21 ∨ n = 29) :
    (Finset.univ.filter (fun a : ZMod 32 => a ^ 2 - n = 4)).card = 4 := by
  rcases hn with h | h | h | h <;> subst h <;> decide

/-- The image of `N ≡ 5 (mod 8)` in `ZMod 32` is one of `{5,13,21,29}`, so
`gate_five_count_mod32` applies to any such `N`. -/
theorem castHom_N_five_cases {k : ℕ} (h32 : (32 : ℕ) ∣ 2 ^ k) (N : ℤ) (hN : N ≡ 5 [ZMOD 8]) :
    ZMod.castHom h32 (ZMod 32) ((N : ℤ) : ZMod (2 ^ k)) = 5
      ∨ ZMod.castHom h32 (ZMod 32) ((N : ℤ) : ZMod (2 ^ k)) = 13
      ∨ ZMod.castHom h32 (ZMod 32) ((N : ℤ) : ZMod (2 ^ k)) = 21
      ∨ ZMod.castHom h32 (ZMod 32) ((N : ℤ) : ZMod (2 ^ k)) = 29 := by
  rw [map_intCast]
  -- N ≡ 5 (mod 8) ⇒ N % 32 ∈ {5,13,21,29}; push to ZMod 32 and decide the four cases
  have h8 : (8 : ℤ) ∣ (5 - N) := Int.modEq_iff_dvd.mp hN
  have hcases : N ≡ 5 [ZMOD 32] ∨ N ≡ 13 [ZMOD 32] ∨ N ≡ 21 [ZMOD 32] ∨ N ≡ 29 [ZMOD 32] := by
    rcases (by omega : N % 32 = 5 ∨ N % 32 = 13 ∨ N % 32 = 21 ∨ N % 32 = 29) with h|h|h|h <;>
      [exact Or.inl (Int.modEq_iff_dvd.mpr (by omega));
       exact Or.inr (Or.inl (Int.modEq_iff_dvd.mpr (by omega)));
       exact Or.inr (Or.inr (Or.inl (Int.modEq_iff_dvd.mpr (by omega))));
       exact Or.inr (Or.inr (Or.inr (Int.modEq_iff_dvd.mpr (by omega))))]
  rcases hcases with h | h | h | h
  · exact Or.inl (by rw [(ZMod.intCast_eq_intCast_iff _ _ _).mpr h]; norm_num)
  · exact Or.inr (Or.inl (by rw [(ZMod.intCast_eq_intCast_iff _ _ _).mpr h]; norm_num))
  · exact Or.inr (Or.inr (Or.inl (by rw [(ZMod.intCast_eq_intCast_iff _ _ _).mpr h]; norm_num)))
  · exact Or.inr (Or.inr (Or.inr (by rw [(ZMod.intCast_eq_intCast_iff _ _ _).mpr h]; norm_num)))

/-! ### N ≡ 1 (mod 8): no finite-level gate (Observation 3, now a theorem)

Unlike `N ≡ 3, 5, 7 (mod 8)`, the `N ≡ 1` passing set is NOT a finite union of
residue classes mod `2^j`: its saturation density is `1/24`, which is not dyadic.
Operationally, a finite gate at level `j` would force `C_{m+1} = 2·C_m` for all
`m ≥ j`; we show `C_{m+1} ≠ 2·C_m` for every `m ≥ 5`, directly from the proved
closed forms `passCard_one_mod_eight_even/odd`. -/

/-- For `N ≡ 1 (mod 8)` and `m ≥ 5`, the pass count does NOT exactly double from
level `m` to `m+1` (the residual constants 16 vs 20 break exact doubling). -/
theorem passCard_one_succ_ne_two_mul (N : ℤ) (hN : N ≡ 1 [ZMOD 8]) (m : ℕ) (hm : 5 ≤ m) :
    passCard ((N : ℤ) : ZMod (2 ^ (m + 1))) ≠ 2 * passCard ((N : ℤ) : ZMod (2 ^ m)) := by
  intro hEq
  have hmul : 3 * passCard ((N : ℤ) : ZMod (2 ^ (m + 1)))
            = 2 * (3 * passCard ((N : ℤ) : ZMod (2 ^ m))) := by rw [hEq]; ring
  have e1 : (m + 1) - 3 = m - 2 := by omega
  have e2 : (2 : ℕ) ^ (m - 2) = 2 * 2 ^ (m - 3) := by
    rw [← pow_succ']; congr 1; omega
  rcases Nat.even_or_odd m with hpar | hpar
  · -- m even (⇒ m ≥ 6), m+1 odd
    have hm6 : 6 ≤ m := by rcases hpar with ⟨r, hr⟩; omega
    rw [passCard_one_mod_eight_odd N hN (m + 1) (by omega) (Even.add_one hpar),
        passCard_one_mod_eight_even N hN m hm6 hpar, e1, e2] at hmul
    omega
  · -- m odd (≥5), m+1 even (≥6)
    rw [passCard_one_mod_eight_even N hN (m + 1) (by omega) (Odd.add_one hpar),
        passCard_one_mod_eight_odd N hN m hm hpar, e1, e2] at hmul
    omega

/-- **No finite-level gate for `N ≡ 1 (mod 8)`.** For every candidate level `j`
there is an `m ≥ j` at which doubling fails, so survival is not determined by
`A mod 2^j` for any fixed `j` — in sharp contrast to `N ≡ 3, 5, 7`. -/
theorem no_finite_gate_one_mod_eight (N : ℤ) (hN : N ≡ 1 [ZMOD 8]) (j : ℕ) :
    ∃ m, j ≤ m ∧ passCard ((N : ℤ) : ZMod (2 ^ (m + 1))) ≠ 2 * passCard ((N : ℤ) : ZMod (2 ^ m)) :=
  ⟨max j 5, le_max_left _ _, passCard_one_succ_ne_two_mul N hN _ (le_max_right _ _)⟩

/-
### Part 2 — binomial ratio limits (Corollary 4, arithmetic core) — NEXT ITERATION

Kept out of the live (sorry-free) file until proved.  Statements to formalize next,
over `Nat.choose` only (the binary-encoding bridge is a separate step):

  binSum t b := ∑ w ∈ Finset.range (t+1), (b.choose w : ℝ)

  -- N ≡ 7 sparse survival → 1
  theorem gate_ratio_tendsto_one (t : ℕ) :
      Tendsto (fun b : ℕ => binSum t (b - 2) / binSum t b) atTop (𝓝 1)

  -- N ≡ 3 sparse survival → 0
  theorem gate_ratio_shift_tendsto_zero (t : ℕ) :
      Tendsto (fun b : ℕ => (∑ w ∈ Finset.range (t+1), ((b-2).choose (w-1) : ℝ)) / binSum t b)
        atTop (𝓝 0)

Strategy: `binSum t b` is a polynomial in `b` of degree `t` with leading coefficient
`1/t!` (since `C(b,w) ~ b^w/w!`).  Hence `binSum t (b-2)/binSum t b → 1`, and the
shifted numerator (degree `t-1`) over `binSum t b` (degree `t`) → 0.
-/

end DyadicShells.SparseBias
