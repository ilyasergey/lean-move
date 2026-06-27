# Artifact status — requested badges

This artifact accompanies OOPSLA 2026 paper **#1171**, *Tracking Borrows with
Regular Expressions*. We apply for all four badges:

- **Artifact Available**
- **Artifact Evaluated — Functional**
- **Artifact Evaluated — Reusable**
- **Results Reproduced**

## Why we believe the artifact qualifies

**Available.** The artifact is released under the Apache-2.0 licence (see
[`LICENSE`](LICENSE)). Upon acceptance it will be deposited at a permanent
location with a DOI (e.g. Zenodo); we defer the public deposit while the paper
is under double-blind revision, to preserve anonymity.

**Functional.** The artifact is *documented, consistent, complete, and
exercisable*. It is the complete Lean 4 development described in the paper:
the language, regex library, small-step semantics, relational and algorithmic
type systems, the machine-checked soundness proof, the parser/translator, and
the full test suite. Verification and validation evidence:

- `lake build` re-checks every definition and proof with the Lean kernel and
  completes with **zero errors**.
- The development contains **zero `sorry`, zero `admit`, and zero `axiom`**
  declarations (a one-line check is given in [`ARTIFACT.md`](ARTIFACT.md)).
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
`type_soundness_dec` certificates and the type-checking conformance suite.

### Scope note (what this artifact does *not* reproduce)

The performance numbers in **Section 6** (≈2.2× slowdown, ≈30 µs/function over
2.9M functions) come from the **Rust implementation in the Sui blockchain
client**, which is a *separate* codebase and is **not** part of this Lean
artifact. Those numbers are out of scope for this submission; "Results
Reproduced" here refers to the mechanised formal results above.
