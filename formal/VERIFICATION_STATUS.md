# Verification status

- [x] Branch opened for isolated work; no changes to main.
- [x] Lean/mathlib configuration and initial source modules committed.
- [x] The initial partial-formalization modules compile with `lake build` in GitHub Actions, run 40651327555 (2026-10-28).
- [x] **Proposition 3.1 factor recovery — Lean-proved (T1-A / T1-B / T1-C)**. Green CI run 40660521229 (#14): `lake build` (Lean 4.24.0 / Mathlib v4.24.0), the "Axiom audit" step (prints `#print axioms`, fails on `sorryAx`/`ofReduceBool`), and "Reject proof holes" all passed; no `sorry`/`admit`. Theorems in `DyadicShells/Soundness.lean`: `square_certificate_factorization`, `square_certificate_dvd`, `gcd_factor_recovery`, `prop31_factor_recovery`, `prop31_recovered_proper`, `weighted_certificate_factorization`, `gcd_dvd_modulus`, `proper_divisor_criterion`, plus the `n=35,k=3,A=53,t=52` regression `example`s. *Equivalence-to-published-prose review still pending (checkbox below).*
- [ ] Full published Proposition 4.1 exact finite-field count proved.
- [ ] Full published Proposition 4.2 uniform 2-adic density bound proved.
- [ ] Independent reviewer validates theorem mapping (incl. Prop 3.1 above).
- [ ] Author approves publication or merge.

**Do not report “three theorems Lean verified”.** As of CI run #14, the
Proposition 3.1 factor-recovery statements (T1-A/B/C) are code-proved under Lean
4.24.0 and pinned Mathlib v4.24.0 with no proof holes; **Propositions 4.1 and
4.2 remain unproved**, and independent equivalence-to-prose review for all
targets is still open. `#print axioms` is run in CI (the audit step below), not
locally — the Lean toolchain host is blocked by the build environment's proxy
policy — and its output is recorded verbatim: only the standard Mathlib axioms
(`propext`, `Classical.choice`, `Quot.sound`) appear.
No `sorry` or `admit` is used.

## Axiom audit (T1-C)

A dedicated CI step runs `lake env lean DyadicShells/AxiomAudit.lean`, which
`#print axioms` for every named Target 1 theorem, prints the list to the build
log, and **fails the build if `sorryAx` or `ofReduceBool` appears**. Captured
verbatim from CI run 40660521229 (#14), step "Axiom audit":

| Theorem | Axioms |
|---|---|
| `weighted_center_decomposition` | propext, Classical.choice, Quot.sound |
| `weighted_center_square_identity` | propext, Classical.choice, Quot.sound |
| `weighted_center_factor_witnesses` | propext, Classical.choice, Quot.sound |
| `square_certificate_factorization` | propext, Classical.choice, Quot.sound |
| `square_certificate_dvd` | propext, Classical.choice, Quot.sound |
| `gcd_factor_recovery` | propext, Classical.choice, Quot.sound |
| `prop31_factor_recovery` | propext, Classical.choice, Quot.sound |
| `prop31_recovered_proper` | propext, Classical.choice, Quot.sound |
| `weighted_certificate_factorization` | propext, Classical.choice, Quot.sound |
| `gcd_dvd_modulus` | propext |
| `proper_divisor_criterion` | propext |

Only standard Lean/Mathlib axioms appear; **no `sorryAx`, custom `axiom`, or
`Lean.ofReduceBool`** (the numeric regression uses `decide`, not
`native_decide`). The "Reject proof holes" step additionally confirms no
`sorry`/`admit` in source. The step's own guard (`grep -Eq
'sorryAx|ofReduceBool'`) would fail the build on any proof-hole or
compiled-decision axiom; run #14 passed it.

Human author: Arsen A. Khachatryan; research affiliation: SibarS Labs.
AI-assisted drafting and formalization; scientific responsibility
remains with the author.
