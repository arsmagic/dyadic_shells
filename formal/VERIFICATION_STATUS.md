# Verification status

- [x] Branch opened for isolated work; no changes to main.
- [x] Lean/mathlib configuration and initial source modules committed.
- [x] The initial partial-formalization modules compile with `lake build` in GitHub Actions, run 40651327555 (2026-10-28).
- [x] **Proposition 3.1 factor recovery — Lean-proved** (gcd recovery under cross-coprimality + arbitrary-certificate soundness). CI run 40654330134 (#8) green, "Reject proof holes" step passed, no `sorry`/`admit`/`axiom`. Theorems: `square_certificate_factorization`, `square_certificate_dvd`, `gcd_factor_recovery` in `DyadicShells/Soundness.lean`. *Equivalence-to-published-prose review still pending (checkbox below).*
- [ ] Full published Proposition 4.1 exact finite-field count proved.
- [ ] Full published Proposition 4.2 uniform 2-adic density bound proved.
- [ ] Independent reviewer validates theorem mapping (incl. Prop 3.1 above).
- [ ] Author approves publication or merge.

**Do not report “three theorems Lean verified”.** As of CI run #8, the
Proposition 3.1 factor-recovery statements are code-proved under Lean 4.24.0 and
pinned Mathlib v4.24.0 with no proof holes; **Propositions 4.1 and 4.2 remain
unproved**, and independent equivalence-to-prose review for all targets is still
open. `#print axioms` was not run locally (the Lean toolchain host is blocked by
the build environment's proxy policy); the "Reject proof holes" grep confirms no
`sorry`/`admit`/`axiom`/`unsafe`, so no `sorryAx` is introduced — only the
standard Mathlib axioms (`propext`, `Classical.choice`, `Quot.sound`) are relied
on via `ring`/`linarith`/`Int.gcd_mul_left`.
No `sorry` or `admit` is used.

Human author: Arsen A. Khachatryan; research affiliation: SibarS Labs.
AI-assisted drafting and formalization; scientific responsibility
remains with the author.
