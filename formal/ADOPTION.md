# Adopting the `anthropics/formal-math/eth` formalization pattern in `dyadic_shells`

Goal: close the one open item in `VERIFICATION_STATUS.md` — *"external, independent
human mathematical peer review"* — **procedurally**, by shrinking and hardening the
surface a human (or a second machine) has to trust, the way the ETH formalization does.

This is not about the ETH *result* (irrelevant to factorization) — only its
*method of presentation*, which is state-of-the-art and directly applicable.

> **Status of this kit.** The `.lean` files are DRAFTS. They could not be compiled
> in the environment that produced them (no Lean toolchain + a full Mathlib build).
> Statements were transcribed from the actual signatures in your proof files, but
> every file must pass `lake build` on your pinned toolchain before use, and the
> `Solution.lean` glue (see below) is the part most likely to need adjustment.

## Gap analysis: your repo vs. the `eth/` reference

| `eth/` element | `dyadic_shells/formal` today | Verdict |
|---|---|---|
| Mathlib-only, **definitions-only** statement file (`MainResults.lean`) — the entire human-check surface | statements live inside the proof files, which import your own machinery | **MISSING** — the biggest gap |
| `Challenge.lean`: headline theorems as `sorry`, importing the statement file alone | — | **MISSING** |
| `Solution.lean`: proves theorems whose **types are identical** to `Challenge.lean` | proofs are the in-place theorems; no challenge/solution split | **MISSING** |
| `comparator.json` + **second independent kernel** (`nanoda`) | CI runs `lake build` + axiom audit + `sorry`/`admit` rejection, single kernel | **PARTIAL** — no second kernel |
| `proof/PaperIndex.lean`: **type-checked** alias map, differences noted | `THEOREM_MAPPING.md` — prose only; names can rot silently | **PARTIAL** |
| `scripts/PrintAxioms.lean` | `DyadicShells/AxiomAudit.lean` | **PRESENT** ✓ |
| Appendix in the PDF that **prints the statement file verbatim** and lists its differences from the printed statements | source-to-code notes exist in `THEOREM_MAPPING.md` | **PARTIAL** |
| Explicit caveat: *the machine checks the proofs, not that the statements say what the paper says* | already stated ("machine verification, not external human peer review") | **PRESENT** ✓ |

You are already ~half-way there. The decisive missing piece is the **separated,
Mathlib-only statement surface** (`MainResults` + `Challenge`/`Solution` split),
which is exactly what converts "a human must read the whole development" into
"a human reads one short file, and a machine guarantees the proofs match it."

## Why this closes your open review item

The ETH repo's own README is blunt: Lean checks the proofs, *"no machine checks
that this file says what the paper says; the file is kept short so that a reader
can check this."* That is your Target-1/2/3 open checkbox, verbatim. The pattern
makes the only remaining human task *small and bounded*:

1. the statement file imports Mathlib and nothing else, so reading it needs no
   knowledge of your proofs;
2. the comparator proves the solution against those exact types;
3. a second kernel (`nanoda`) re-checks independently;
4. the PDF appendix prints the statement file, so a referee compares paper↔Lean
   on one page.

A referee's residual job shrinks to: *does `MainResults.lean` state Propositions
3.1 / 4.1 / 4.2?* — a few minutes, not a full audit.

## Files in this kit (target paths under `formal/`)

- `formal/MainResults.lean` — Mathlib-only, definitions-only; the four claims
  (`Prop31`, `Prop41`, `Prop42`, `Target4MilestoneA`) with inlined copies of
  `twoAdicPass` / `passingCenters` / `passCard`.
- `formal/Challenge.lean` — the four claims as `theorem … := sorry`.
- `formal/Solution.lean` — proves the identical types from your existing theorems.
- `formal/comparator.json` — comparator config naming the four theorems and the
  three permitted axioms, `enable_nanoda: true`.
- `formal/PaperIndex.lean` — type-checked `alias` map (companion to, not a
  replacement for, `THEOREM_MAPPING.md`).
- `ci-nanoda-snippet.yml` — the second-kernel CI step.

## Step-by-step plan

1. **Add `MainResults.lean`** and get it to `lake build` by itself (imports only
   Mathlib). Fix any Mathlib name drift at your pin (`v4.24.0`): e.g. confirm
   `quadraticChar`, `Int.ModEq`/`[ZMOD _]`, `IsSquare` spellings.
2. **Add `Challenge.lean`** (`sorry`s) — should build immediately.
3. **Add `Solution.lean`** — this is the real work. Each proof applies an existing
   theorem; the inlined predicates are written to be definitionally equal to yours.
   If a direct term is rejected (most likely `prop41`, over the `Classical`
   decidability instance on `IsSquare`), close it with a one-line
   `by simpa [DyadicShellsStatements.PassingCenters, DyadicShells.passingCenters]
   using …`. Build `Solution`, then run `#print axioms` on the four theorems — they
   must show only `propext, Classical.choice, Quot.sound`.
4. **Add `PaperIndex.lean`** — pure aliases; builds iff every referenced name still
   exists (that is the point).
5. **Wire the second kernel.** This is the one step with a real cost: the Palomar
   comparator + `nanoda` + `lean4export` in the ETH repo run on Lean `v4.33.1`.
   Your repo is pinned to `v4.24.0`. Either (a) build `nanoda`/`lean4export` matched
   to `v4.24.0`, or (b) bump your Mathlib/Lean pin and repair any proof breakage
   (non-trivial — budget time). Do **not** claim a second-kernel guarantee until
   this actually runs green. `ci-nanoda-snippet.yml` is a scaffold, not drop-in.
6. **Add the PDF appendix.** In the next version (e.g. 11.7.x), add an appendix that
   prints `MainResults.lean` verbatim and lists, in a short table, every point where
   the Lean statement differs from the printed Proposition (you already have this
   prose in `THEOREM_MAPPING.md` — move the delta list into the paper). This is the
   cheapest high-value win and needs no toolchain work.

## Honest scope

- This does **not** add any mathematics or novelty. It raises the *credibility and
  legibility* of what you already proved — which, for a PhD-by-published-works
  defense built on machine-checked propositions, is the differentiator.
- It does **not** touch factorization complexity, FP-MITM crossovers, or any
  practical/cryptographic claim — all of which remain outside the formal proofs,
  as your ledger already states.
- Per your standing rule, no AI vendor/model is named in any of these files or in
  the AI-use disclosure; refer generically to "AI tools".
