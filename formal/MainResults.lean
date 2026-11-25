/-
Dyadic Shells — statement-only file (DRAFT, must be compiled with `lake build`).

Mirrors the pattern of anthropics/formal-math `eth/MainResults.lean`:
this file has DEFINITIONS ONLY — no `theorem`, no proof. It imports Mathlib
and nothing else, so it can be read and compiled on its own. The point is to
make the human-equivalence-review surface ONE short, self-contained file:
whoever reads it knows exactly what the published Propositions 3.1 / 4.1 / 4.2
and the Target-4 milestone claim, with no dependence on the proof development.

The six `Prop`-valued definitions below are the claims:
  * `Prop31`  — soundness / factor recovery (published v11.0.3, Proposition 3.1).
  * `Prop41`  — exact quadratic-residue sieve count (Proposition 4.1).
  * `Prop42`  — uniform two-adic saturation lower bound (Proposition 4.2).
  * `Target4MilestoneA` — the `N mod 8` reduction of the exact two-adic count.
  * `Target4MilestoneB` — the exact closed forms for every odd residue class.
  * `Target4MilestoneC` — Hittmeir's hyperbolic-sieve identity mod `2^e`.

The inlined predicates `TwoAdicPass`, `PassingCenters`, `PassCard` are COPIES of
the definitions used in the proof files (`TwoAdicSaturation.lean`,
`QRSieve.lean`, `TwoAdicExact.lean`). They are written here against Mathlib
alone so that this file stands by itself. Each is definitionally equal to its
proof-side counterpart; `Solution.lean` discharges the claims by applying the
already-proved theorems (see the note there).
-/
import Mathlib

namespace DyadicShellsStatements

open Finset

/-! ### Inlined predicates (copies of the proof-side definitions) -/

/-- Copy of `DyadicShells.twoAdicPass`: `A` is a two-adic pass at level `m` for
`N` iff `A² ≡ N + y² (mod 2^m)` for some `y`. -/
def TwoAdicPass (N m A : ℕ) : Prop :=
  ∃ y : ℕ, Nat.ModEq (2 ^ m) (A ^ 2) (N + y ^ 2)

open Classical in
/-- Copy of `DyadicShells.passingCenters`: centers `A` with `A² − N` a square.
`Classical` matches the proof-side definition's decidability instance. -/
noncomputable def PassingCenters
    (F : Type*) [CommRing F] [Fintype F] [DecidableEq F] (N : F) : Finset F :=
  Finset.univ.filter (fun A => IsSquare (A ^ 2 - N))

open Classical in
/-- Copy of `DyadicShells.passCard`: number of residues `A mod n` with `A² − N`
a square mod `n`. -/
noncomputable def PassCard {n : ℕ} [NeZero n] (N : ZMod n) : ℕ :=
  (Finset.univ.filter fun A : ZMod n => IsSquare (A ^ 2 - N)).card

/-! ### The claims -/

/-- **Proposition 3.1 (soundness / factor recovery).** For primes `p, q`,
positive multipliers `a, b < min p q`, an anchored center `2A = a·p + b·q`, and
`t = a·p − A`, the exact gcds recover the factors:
`gcd(A + t, p·q) = p` and `gcd(A − t, p·q) = q`. -/
def Prop31 : Prop :=
  ∀ (p q a b : ℕ) (A t : ℤ),
    p.Prime → q.Prime → 0 < a → 0 < b → a < min p q → b < min p q →
    2 * A = (a : ℤ) * p + (b : ℤ) * q → t = (a : ℤ) * p - A →
    Int.gcd (A + t) ((p : ℤ) * q) = p ∧ Int.gcd (A - t) ((p : ℤ) * q) = q

/-- **Proposition 4.1 (exact QR sieve count).** In every finite field of odd
characteristic, for every nonzero `N`, the inclusive square-or-zero pass count
is exactly `(|F| + χ(N))/2`, where `χ` is the quadratic character. -/
def Prop41 : Prop :=
  ∀ (F : Type*) [Field F] [Fintype F] [DecidableEq F],
    ringChar F ≠ 2 → ∀ (N : F), N ≠ 0 →
      ((PassingCenters F N).card : ℤ)
        = ((Fintype.card F : ℤ) + quadraticChar F N) / 2

open Classical in
/-- **Proposition 4.2 (uniform two-adic saturation).** For odd `N ≥ 3` there is
`v` (namely `v₂((N−1)/2)`) such that for every level `m` the number of passing
residues below `2^m` is at least `2^(m−(2v+3))`, i.e. `π_m(N) ≥ 2^(−(2v+3))`. -/
def Prop42 : Prop :=
  ∀ (N : ℕ), Odd N → 3 ≤ N →
    ∃ v : ℕ, ∀ m : ℕ,
      2 ^ m ≤ 2 ^ (2 * v + 3) *
        ((Finset.range (2 ^ m)).filter (fun A => TwoAdicPass N m A)).card

/-- **Target 4, milestone A (`N mod 8` reduction).** For odd integers
`N ≡ N' (mod 8)`, the two-adic pass counts modulo `2^m` coincide, for every
`m`. (Companion: `PassCard` is invariant under multiplication by a unit square.) -/
def Target4MilestoneA : Prop :=
  ∀ (m : ℕ) [NeZero (2 ^ m)] (N N' : ℤ),
    Odd N → Odd N' → N ≡ N' [ZMOD 8] →
      PassCard ((N : ℤ) : ZMod (2 ^ m)) = PassCard ((N' : ℤ) : ZMod (2 ^ m))

/-- **Target 4, milestone B (closed forms for the residue representatives).**
The exact two-adic pass count `C_m = PassCard` for every odd `N`, by class mod 8:
`N ≡ 3 (mod 4)` ⇒ `C_m = 2^(m-2)` (`m ≥ 3`, covers `N ≡ 3, 7 (mod 8)`);
`N ≡ 5 (mod 8)` ⇒ `C_m = 2^(m-3)` (`m ≥ 5`); `N ≡ 1 (mod 8)` ⇒
`3·C_m = 2^(m-3) + 16` for even `m ≥ 6` and `3·C_m = 2^(m-3) + 20` for odd
`m ≥ 5`; and the sharp unconditional density `2^m < 24·C_m` for every odd `N`. -/
def Target4MilestoneB : Prop :=
  (∀ (N : ℤ) (m : ℕ) [NeZero (2 ^ m)], N ≡ 3 [ZMOD 4] → 3 ≤ m →
      PassCard ((N : ℤ) : ZMod (2 ^ m)) = 2 ^ (m - 2)) ∧
  (∀ (N : ℤ) (m : ℕ) [NeZero (2 ^ m)], N ≡ 5 [ZMOD 8] → 5 ≤ m →
      PassCard ((N : ℤ) : ZMod (2 ^ m)) = 2 ^ (m - 3)) ∧
  (∀ (N : ℤ) (m : ℕ) [NeZero (2 ^ m)], N ≡ 1 [ZMOD 8] → 6 ≤ m → Even m →
      3 * PassCard ((N : ℤ) : ZMod (2 ^ m)) = 2 ^ (m - 3) + 16) ∧
  (∀ (N : ℤ) (m : ℕ) [NeZero (2 ^ m)], N ≡ 1 [ZMOD 8] → 5 ≤ m → Odd m →
      3 * PassCard ((N : ℤ) : ZMod (2 ^ m)) = 2 ^ (m - 3) + 20) ∧
  (∀ (N : ℤ) (m : ℕ) [NeZero (2 ^ m)], Odd N →
      2 ^ m < 24 * PassCard ((N : ℤ) : ZMod (2 ^ m)))

/-- Copy of `DyadicShells.HyperbolicSieve.hyperbolicSieveSet`: Hittmeir's
hyperbolic sieve set `L_{N,M,k} = { k·x + y : x·y = N }` as a finset of residues. -/
def HyperbolicSieveSet {M : ℕ} [NeZero M] (N k : ZMod M) : Finset (ZMod M) :=
  (Finset.univ.filter (fun p : ZMod M × ZMod M => p.1 * p.2 = N)).image
    (fun p => k * p.1 + p.2)

/-- **Target 4, milestone C (Theorem 3, doubled form).** For odd `N, k` and
`e ≥ 1`, twice the size of Hittmeir's hyperbolic sieve set `L_{N,2^e,k}` equals
the exact two-adic pass count `C_e(k·N) = PassCard`, i.e. `2·|L| = C_e(k·N)`
(equivalently `|L| = C_e(k·N)/2`). -/
def Target4MilestoneC : Prop :=
  ∀ (N k : ℤ) (e : ℕ) [NeZero (2 ^ e)], Odd N → Odd k → 1 ≤ e →
    2 * (HyperbolicSieveSet ((N : ℤ) : ZMod (2 ^ e)) ((k : ℤ) : ZMod (2 ^ e))).card
      = PassCard (((k * N : ℤ)) : ZMod (2 ^ e))

end DyadicShellsStatements
