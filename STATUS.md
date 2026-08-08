# Artifact status — requested badges

This artifact accompanies the OOPSLA 2026 paper *Tracking Borrows with
Regular Expressions*. We apply for all four badges:

- **Artifact Available**
- **Artifact Evaluated — Functional**
- **Artifact Evaluated — Reusable**
- **Results Reproduced**

## Why we believe the artifact qualifies

**Available.** The artifact is released under the Apache-2.0 licence (see
[`LICENSE`](LICENSE)) and is archived at a permanent, publicly accessible
location on Zenodo, DOI:
[10.5281/zenodo.XXXXXXX](https://doi.org/10.5281/zenodo.XXXXXXX).

**Functional.** The artifact is *documented, consistent, complete, and
exercisable*. It is the complete Lean 4 development described in the paper:
the language, regex library, small-step semantics, relational and algorithmic
type systems, the machine-checked soundness proof, the parser/translator, and
the full test suite. Verification and validation evidence:

- `lake build` re-checks every definition and proof with the Lean kernel and
  completes with **zero errors**.
- The development contains **zero `sorry` and zero `axiom`** declarations
  (a one-line check is given in [`ARTIFACT.md`](ARTIFACT.md)).
- `#print axioms` on the top-level theorem `type_soundness` reports only the
  three standard Lean/mathlib axioms (`propext`, `Classical.choice`,
  `Quot.sound`) — and crucially **not** `sorryAx`.

**Reusable.** Beyond functional, the artifact is *carefully documented and
clearly organised* for reuse: a paper-to-artifact correspondence table, a
prose metatheory overview ([`metatheory.md`](metatheory.md)), the AI
configuration and representative development prompts
([`CLAUDE.md`](CLAUDE.md), [`PROMPTS.md`](PROMPTS.md)), a modular
one-lemma-per-case proof structure, and the vector/enum extensions that serve
as worked templates for extending the type system. It is released under an
open-source licence.

**Results Reproduced.** The artifact *is* the mechanised result: re-running
`lake build` reproduces the paper's central scientific claim — that the
regex-based type system is sound (Theorem 3.1) and that the algorithmic checker
agrees with the relational specification (`check_stmt_sound`) — by having the
Lean kernel re-check the proofs. It also re-runs the **31** per-execution
`type_soundness_dec` certificates and the type checking conformance suite. The
**Section 6** performance result is reproducible too, via the separate Rust
harness in [`benchmark/`](benchmark/): `benchmark/corroborate.sh` corroborates the
≈2.2× / ≈30 µs claim on a bundled sample in minutes (we observed ≈2.0× / ~18 µs
on an Apple M2), and `benchmark/run.sh` reproduces the full corpus figures.

### Scope note

The **Section 6** performance numbers come from the Rust implementation in the
Sui client — a *separate* codebase from the Lean development. That code is not
vendored here (see [`benchmark/IMPLEMENTATION.md`](benchmark/IMPLEMENTATION.md)
for why, and for how it maps to the Lean artifact), but it is pinned by commit
and its results are reproducible through the [`benchmark/`](benchmark/) harness
— either the bundled-sample corroboration or the full ~13–16 GB corpus. The
full corpus run needs the public dataset and comparable hardware (the paper used
an Apple M1 Max); the bundled corroboration needs neither.
