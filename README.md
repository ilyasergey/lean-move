## Lean-Move

An experimental formalisation of Move borrow checker in Lean.

See **[metatheory.md](metatheory.md)** for a detailed overview of the
type system, soundness statement, proof architecture, and key invariants.

> **Artifact evaluators:** start with **[ARTIFACT.md](ARTIFACT.md)** — the
> evaluation guide (requirements, kick-the-tires, full build, and the
> claims-to-code mapping). Requested badges are listed in
> **[STATUS.md](STATUS.md)**. The project is licensed under Apache-2.0
> (**[LICENSE](LICENSE)**). `make build` fetches the mathlib cache and
> re-checks every proof. The paper's Section 6 performance benchmark (Rust,
> separate) lives in **[benchmark/](benchmark/)** — see ARTIFACT.md §8 and
> **[benchmark/IMPLEMENTATION.md](benchmark/IMPLEMENTATION.md)** (a guide to the
> production Rust checker and how it maps to this Lean development).
>
> **One-command evaluation** (from the repo root): **`make eval`** checks
> *everything* — the Lean proofs and the Section 6 benchmark. **`make eval-lean`**
> runs the Lean half (build + axiom-clean check); **`make eval-rust`** runs the
> Rust benchmark corroboration on the bundled sample.

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
Builds the core library, all type checking examples, and runtime tests
(including type soundness certificates).

### Build core library only
```bash
lake build core
```

### Build type checking examples
```bash
lake build examples    # all examples
lake build litmus       # basic litmus tests only
lake build expressivity # expressivity tests only
```

- `LeanMove/Tests/Typechecking/litmus/` — basic accepted / rejected examples
- `LeanMove/Tests/Typechecking/expressivity/` — transpiled from the
  [Move bytecode verifier tests](https://github.com/tnowacki/sui/tree/example-tests/external-crates/move/crates/bytecode-verifier-transactional-tests/tests/reference_safety/expressivity)
- `LeanMove/Tests/MVIR/` — Move IR source files (`.mvir`) shared across
  parsing and type checking tests

### Build runtime tests only
```bash
lake build runtime
```
