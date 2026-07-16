## Lean-Move

An experimental formalisation of Move borrow checker in Lean.

See **[metatheory.md](metatheory.md)** for a detailed overview of the
type system, soundness statement, proof architecture, and key invariants.

> ## 📄 OOPSLA 2026 artefact
>
> This repository is the Lean development behind the OOPSLA 2026 paper
> **_Tracking Borrows with Regular Expressions_**, which describes this
> regex-based borrow checker for Move and its AI-assisted mechanisation in Lean.
>
> **➡️ The evaluated artefact is on the
> [`oopsla26-artefact`](https://github.com/ilyasergey/lean-move/tree/oopsla26-artefact)
> branch** — it adds the artefact-evaluation guide (`ARTIFACT.md`), an Apache-2.0
> licence, and the paper's Section 6 performance benchmark (`benchmark/`), on top
> of the machine-checked soundness proof, executable checker, and conformance tests.

**To get the artefact and reproduce it:**

```bash
git switch oopsla26-artefact   # switch to the artefact branch
make eval                      # kernel-check the Lean proofs + corroborate the Section 6 benchmark
```

Then read **ARTIFACT.md** on that branch for the full evaluation guide —
requirements, kick-the-tires, the claims-to-code mapping, and the Rust benchmark.

## AI-assisted development

This formalisation was developed with an AI coding assistant. Two documents
record how that collaboration was steered, accompanying the paper's
*AI-Assisted Mechanisation* section:

- **[CLAUDE.md](CLAUDE.md)** — the project configuration supplied to the
  assistant: build commands, repository layout, the proof architecture
  (`WellTypedState` invariant, weakening, decidable soundness certificates),
  the working conventions that made the collaboration productive, and the Lean 4
  pitfalls encountered.
- **[PROMPTS.md](PROMPTS.md)** — a set of representative prompts from the
  development, organised by phase (encoding → algorithmic checker → soundness →
  testing → vectors → enums) and anchored to the commits they produced.

How to use them:

- *To reproduce the proofs*, you do not need either file — `lake build` checks
  everything (see below). They document *process*, not build steps.
- *To understand or extend the proofs*, read `CLAUDE.md` first for the
  architecture and conventions, then `metatheory.md` for the technical detail.
- *To see how the AI was directed*, read `PROMPTS.md`; each block links to the
  dates and commits it corresponds to, so it can be cross-checked against
  `git log`. (The prompts are representative and reconstructed from the git
  history and working notes; the raw session transcripts were not retained.)

## Dependencies

* `mathlib4-v4.27.0`
* `batteries-v4.27.0`

## Building

### Build everything (default)
```bash
lake build
```
Builds the core library, all type-checking examples, and runtime tests
(including type-soundness certificates).

### Build core library only
```bash
lake build core
```

### Build type-checking examples
```bash
lake build examples    # all examples
lake build litmus       # basic litmus tests only
lake build expressivity # expressivity tests only
```

- `LeanMove/Tests/Typechecking/litmus/` — basic accepted / rejected examples
- `LeanMove/Tests/Typechecking/expressivity/` — transpiled from the
  [Move bytecode verifier tests](https://github.com/tnowacki/sui/tree/example-tests/external-crates/move/crates/bytecode-verifier-transactional-tests/tests/reference_safety/expressivity)
- `LeanMove/Tests/MVIR/` — Move IR source files (`.mvir`) shared across
  parsing and type-checking tests

### Build runtime tests only
```bash
lake build runtime
```
