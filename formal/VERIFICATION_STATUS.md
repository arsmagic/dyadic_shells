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

## Remaining research targets

- [ ] **Target 2** — full Proposition 4.1: exact odd-prime QR sieve pass count.
- [ ] **Target 3** — full Proposition 4.2: uniform two-adic saturation bound.
- [ ] Author approval for any **new DOI or external manuscript**.

**Do not report that all three targets are verified.** Experimental
performance, FP-MITM complexity, and novelty are outside Target 1.

AI assistance was used in preparing the formalization; the mathematical
author remains responsible for claims in any later scientific publication.
