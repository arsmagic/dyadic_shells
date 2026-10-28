# Verification status

- [x] Branch opened for isolated work; no changes to main.
- [x] Lean/mathlib configuration and initial source modules committed.
- [x] The initial partial-formalization modules compile with `lake build` in GitHub Actions, run 40651327555 (2026-10-28).
- [x] **Proposition 3.1 factor recovery — Lean-proved (T1-A / T1-B / T1-C)**. Green CI run 40658098732 (#11): `lake build` (Lean 4.24.0 / Mathlib v4.24.0), "Reject proof holes", and the imported axiom-audit module all passed; no `sorry`/`admit`. Theorems in `DyadicShells/Soundness.lean`: `square_certificate_factorization`, `square_certificate_dvd`, `gcd_factor_recovery`, `prop31_factor_recovery`, `prop31_recovered_proper`, `weighted_certificate_factorization`, `gcd_dvd_modulus`, `proper_divisor_criterion`, plus the `n=35,k=3,A=53,t=52` regression `example`s. *Equivalence-to-published-prose review still pending (checkbox below).*
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

## Axiom audit (T1-C)

`DyadicShells/AxiomAudit.lean` runs `#print axioms` for every named Target 1
theorem and is imported into the build, so the axiom list is emitted in the
GitHub Actions log of every run. Expected (and no other): `propext`,
`Classical.choice`, `Quot.sound`. The numeric regression uses `decide`, not
`native_decide`, so `Lean.ofReduceBool` must not appear; the "Reject proof
holes" step confirms no `sorry`/`admit`.

The printed list is visible in the Actions build log (step "Run
leanprover/lean-action"). The CI log artifact is served from a storage host not
reachable by the automated environment, so the verbatim output should be read
from the GitHub Actions web UI and pasted here by the author/reviewer.

Human author: Arsen A. Khachatryan; research affiliation: SibarS Labs.
AI-assisted drafting and formalization; scientific responsibility
remains with the author.
