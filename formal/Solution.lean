/-
Dyadic Shells — Solution file (DRAFT). Proves the four theorems of `Challenge.lean`
— i.e. the four propositions of `MainResults.lean` — from the existing proof
development. The comparator checks that the theorem TYPES here are identical to
those in `Challenge.lean`.

IMPORTANT (the one real engineering task). Each proof applies an already-proved
theorem from the proof files. For `prop31` / `prop42` / `target4MilestoneA` the
inlined statement predicates are written to be definitionally equal to their
proof-side counterparts, so the direct term should type-check. For `prop41` the
inlined `PassingCenters` must match `DyadicShells.passingCenters` up to the
`Classical` decidability instance; if the direct term is rejected, close it with
`by simpa [DyadicShellsStatements.PassingCenters, DyadicShells.passingCenters]
using DyadicShells.qr_exact_pass_count h2 N hN` (and similarly for the others).
The exact glue is only knowable under `lake build`.
-/
import MainResults
import DyadicShells.Soundness
import DyadicShells.QRSieve
import DyadicShells.TwoAdicSaturation
import DyadicShells.TwoAdicExact

theorem DyadicShellsStatements.prop31 : DyadicShellsStatements.Prop31 :=
  fun p q a b A t hp hq ha hb hab hbb hA ht =>
    DyadicShells.prop31_factor_recovery p q a b A t hp hq ha hb hab hbb hA ht

theorem DyadicShellsStatements.prop41 : DyadicShellsStatements.Prop41 :=
  fun F _ _ _ h2 N hN => DyadicShells.qr_exact_pass_count h2 N hN

theorem DyadicShellsStatements.prop42 : DyadicShellsStatements.Prop42 :=
  fun N hodd h3 => DyadicShells.twoadic_saturation N hodd h3

theorem DyadicShellsStatements.target4MilestoneA :
    DyadicShellsStatements.Target4MilestoneA :=
  fun m _ N N' hN hN' h8 =>
    DyadicShells.passCard_eq_of_modEq_eight m N N' hN hN' h8
