# Formal verification status — Dyadic Shells

**Mathematical author:** Arsen A. Khachatryan (SibarS Labs; ORCID 0009-0006-7629-3833).

## Target 1: Soundness and factor recovery

**Mathematical status: Lean-proved.** The full soundness/recovery claims of
v11.0.3 Proposition 3.1 are covered by `DyadicShells/Soundness.lean`,
including both signs in the converse; see `THEOREM_MAPPING.md`.

- [x] Weighted difference-of-squares identity and factor divisibility.
- [x] Arbitrary exact-square factorization (`k=1`).
- [x] Planted-factor recovery under explicitly derived cross-coprimality.
- [x] Corollary from published prime and multiplier bounds, with `t` constructed.
- [x] Properness of the recovered prime factors.
- [x] General weighted certificate distinguishes factorization of `k*n`
      from recovery of a proper divisor of `n`.
- [x] Both signs of the converse: `d = gcd(A ± t, n)` and
      `1 < d < |n|` imply `d` is a proper divisor of `|n|`.
- [x] Concrete counterexample `n=35,k=3,A=53,t=52` is checked.
- [x] Technical comparison with the **published PDF**, v11.0.3,
      p. 3, Proposition 3.1 and Definition 3.2 (2026-10-28).
- [x] Lean 4.24.0 and pinned Mathlib v4.24.0: successful CI and axiom audit
      (baseline: [run #16](https://github.com/arsmagic/dyadic_shells/actions/runs/40663159966)).
- [x] The formal project and proof files are present on `main`.
- [ ] External, independent human mathematical peer review (recommended
      before a new formal-verification paper; **not** a Lean proof gap).

### Source-to-code fidelity

The source assumes `n=p*q` for distinct odd primes `p,q`, and
coprime positive odd multipliers `a,b < min(p,q)`, with a planted
anchored center satisfying `a*p+b*q=2*A`. The Lean corollary proves
factor recovery for **all** primes `p,q` and positive `a,b` within
these bounds given `2*A=a*p+b*q`, a mathematically *stronger* statement:
the source's distinctness, oddness, `gcd(a,b)=1`, and anchored-center
membership are not needed for the algebraic recovery implication.
The source's `t=(a*p-b*q)/2` is encoded as `t=a*p-A`.
The converse is formalized for both `A+t` and `A-t`, including the
explicit proper-divisor bounds. This is a technical equivalence review,
**not** an independent published referee report.

### Machine proof and axiom policy

GitHub Actions runs `lake build`, the `#print axioms` report from
`DyadicShells/AxiomAudit.lean`, and rejects `sorry`/`admit`.
The baseline axiom audit (run #16) listed only `propext`,
`Classical.choice`, and `Quot.sound`, with no `sorryAx`
or `Lean.ofReduceBool`. The new both-sign corollary is included in the
same automated audit in subsequent builds.
Source and diagnostics: [Lean workflow](https://github.com/arsmagic/dyadic_shells/actions/workflows/lean-formal.yml).

## Target 2: Exact quadratic-residue sieve count

**Mathematical status: Lean-proved.** The exact square-or-zero sieve
pass count of v11.0.3 Proposition 4.1 is formalized in
`DyadicShells/QRSieve.lean`, in a form valid for **every** finite field
of odd characteristic and **every** `N ≠ 0` — strictly more general than
the source's prime-field statement; see `THEOREM_MAPPING.md`.

- [x] Difference-of-squares conic parametrization `qrPairsEquivNonzero`
      (`|F|−1` solution pairs for `N ≠ 0`, characteristic ≠ 2).
- [x] Zero-center count `qr_zero_center_count` via Mathlib
      `quadraticChar_card_sqrts`.
- [x] Exact character sum `∑_A χ(A²−N) = −1` (`qr_quadratic_character_sum`).
- [x] Pointwise inclusive square-or-zero indicator identity
      `2·1_{IsSquare z} = 1 + χ(z) + 1_{z=0}`.
- [x] Exact count `2·#pass = |F| + χ(N)` and `#pass = (|F|+χ(N))/2`
      (`qr_exact_pass_count_double`, `qr_exact_pass_count`); the zero
      residue is counted as passing, as the source requires.
- [x] Lean 4.24.0 and pinned Mathlib v4.24.0: successful CI build and
      axiom audit
      ([run #35](https://github.com/arsmagic/dyadic_shells/actions/runs/40697899551),
      commit `2e03d72`).
- [ ] External, independent human mathematical peer review (recommended;
      **not** a Lean proof gap).

### Machine proof and axiom policy (Target 2)

The axiom audit for run #35 lists all five Target 2 declarations
(`qr_zero_center_count`, `qrPairs_count_as_character_sum`,
`qr_quadratic_character_sum`, `qr_exact_pass_count_double`,
`qr_exact_pass_count`) as depending only on `propext`,
`Classical.choice`, and `Quot.sound`, with no `sorryAx` or
`Lean.ofReduceBool`; `sorry`/`admit` are rejected in the same run.
No equidistribution, independent-filter, or probabilistic hypothesis is
introduced.

## Remaining research targets

- [ ] **Target 3** — full Proposition 4.2: uniform two-adic saturation bound.
- [ ] Author approval for any **new DOI or external manuscript**.

**Targets 1 and 2 are Lean-proved; Target 3 is not yet verified — do not
report it as complete.** Experimental performance, FP-MITM complexity, and
novelty are outside the scope of these formal proofs.

AI assistance was used in preparing the formalization; the mathematical
author remains responsible for claims in any later scientific publication.
