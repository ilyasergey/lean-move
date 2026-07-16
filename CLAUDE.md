# CLAUDE.md — AI configuration for the LeanMove development

This file is the project-level configuration and guidance that was supplied to
the AI coding assistant (Claude Code) throughout the mechanisation of the
MoveLight borrow checker. It is included in the artefact, as referenced in the
paper's *AI-Assisted Mechanisation* section, to document how the human prover
steered the assistant. It captures the build commands, the proof architecture,
the working conventions, and the hard-won Lean 4 pitfalls that made the
collaboration productive.

> The companion file [`PROMPTS.md`](PROMPTS.md) contains a set of representative
> prompts from the development, organised by phase and anchored to the commits
> they produced.

---

## 1. What this project is

LeanMove is a fully mechanised reference implementation, in Lean 4, of a
regex-based borrow checker for **MoveLight** — an ANF calculus that captures the
essence of Move IR (MoveIR). It contains:

- the language, regular expression library, and small-step operational semantics;
- a **relational** type system (the declarative specification) and an
  **algorithmic** (executable, Boolean) type checker proven sound with respect
  to it;
- a machine-checked **type soundness** proof (progress + preservation) ruling out
  all *preventable* runtime errors (dangling references, use-after-move, write
  type mismatch, etc.);
- a **parser/translator** from MoveIR text to MoveLight ASTs and a conformance
  test suite drawn from the production Move compiler's own tests;
- **decidable per-execution soundness certificates** (`type_soundness_dec`).

The core idea: reachability between abstract references is tracked by **regular
expressions over field paths**. Borrowing a field is a **Brzozowski derivative**;
the write safety check (`check_outbound`) reduces to deciding `L(r) ⊆ {ε}`; and
borrow disjointness reduces to regex emptiness-of-intersection.

**Hard invariant of this repository: the build has zero `sorry` and zero
`axiom`.** Never introduce one as a shortcut. If a goal cannot be
closed, stop and surface it — a `sorry` that slips into a committed proof
silently invalidates the soundness claim.

---

## 2. Build and verify

Toolchain (pinned in `lean-toolchain` / `lakefile.lean`):

- `leanprover/lean4:v4.27.0`
- `mathlib4-v4.27.0`, `batteries-v4.27.0`

```bash
lake build              # everything: core library + all tests + soundness certificates
lake build core         # core library only (language, type system, proofs) — fastest inner loop
lake build examples     # all type checking examples
lake build litmus       # basic accepted/rejected litmus tests
lake build expressivity # tests transpiled from the Move bytecode verifier suite
lake build runtime      # runtime tests + per-execution type_soundness_dec certificates
```

Guidance for the assistant:

- After any change to a definition or proof, run `lake build core` before
  declaring success. Do **not** report a proof as complete without a clean
  build of at least the affected target.
- The two heavy files — `Preservation.lean` (~11K LOC) and `Weakening.lean`
  (~8K LOC) — are slow to elaborate. When iterating inside one of them, work
  lemma-by-lemma and lean on the fact that earlier lemmas are cached.
- Some concrete-environment theorems need a raised recursion limit. Use
  `set_option maxRecDepth 4096 in` (occasionally `16384`) immediately before the
  `rfl`/`decide`-style theorem, not globally.

---

## 3. Repository layout

```
LeanMove/
  Lang/
    MoveLight.lean              core syntax + types (Expr, Stmt, MoveType, Aref)
    Macros.lean                 concrete syntax macros (the ;; StmtBuilder, regex notation)
    PrettyPrint.lean
    MoveIR/                     MoveIR.lean, Syntax.lean, Parser.lean, Translate.lean, PrettyPrint.lean
  Semantics/
    Smallstep.lean              machine state, heap ops, step function, RuntimeError
  Structures/
    Regex.lean                  regex, Brzozowski derivative, emptiness, ⊆{ε}, disjointness
    PathMap.lean                path environment (refs + paths), extend, node removal, transitive closure
    AssocMap.lean               verified associative map (insert/lookup lemmas)
    ListUtils.lean
  Typing/
    Types.lean, TypesUtils.lean PathElement, MoveType, environment lemmas
    TypeChecking.lean           RELATIONAL typing rules (the specification)
    Algorithmic/
      AlgorithmicTypeChecking.lean   executable Boolean checker (check_stmt)
      AlgorithmicTypingSoundness.lean  check_stmt ⟹ relational judgement
      DecidableTypeEnv.lean     decidable environment well-formedness; test env builders
    Soundness/
      Defs.lean                 WellTypedState invariant, ValueMatchesType, SoundnessAssumptions
      Progress.lean
      Preservation.lean         the bulk: one lemma per typing rule case
      Weakening.lean            subsumption / reference substitution σ threaded everywhere
      InitState.lean            initial-state safety, type_soundness_dec
      SafeExec.lean, StackSafeUtils.lean
    TypeSoundness.lean          top-level type_soundness theorem
  Tests/
    MVIR/                       .mvir source files (shared by parsing + typechecking tests)
    Parsing/                    alpha-equivalence tests (parsed vs. hand-written ASTs)
    Typechecking/litmus/        small accepted/rejected examples
    Typechecking/expressivity/  transpiled from the Move bytecode verifier suite
    Runtime/AllTests.lean       runtime conformance + decidable soundness certificates
```

`metatheory.md` is the canonical prose overview (definitions, statements, proof
architecture, invariant clauses, limitations). Read it first for orientation; it
is kept in sync with the Lean sources.

The `benchmark/` folder (added for the OOPSLA artefact) is a **separate Rust
performance harness** for the paper's Section 6; it is unrelated to the Lean
build (`lake` never touches it). See `benchmark/README.md` and
`benchmark/IMPLEMENTATION.md`.

---

## 4. Proof architecture (read before touching soundness)

- **Two type systems, one proof of agreement.** `TypeChecking.lean` is the
  relational spec; `Algorithmic/` is the executable checker. The bridge theorem
  is `check_stmt_sound : check_stmt … = true → typecheck_stmt …`. When the spec
  changes, the algorithmic side and this bridge change with it — keep them in
  lock-step.

- **Soundness = progress + preservation** (Wright–Felleisen style), over a
  fuel-indexed small-step semantics. The connective tissue is the
  **`WellTypedState`** invariant relating the type environment to the concrete
  machine via a reference map `μ : Aref → Loc`.
  - Core invariant: **29 clauses** (variable/site validity, reference tracking +
    injectivity of `μ`, path–heap coherence, heap typing, borrow safety,
    structural freshness/root conditions).
  - With the enum extension it grows to **35 clauses** (enum-environment
    consistency, name/field uniqueness, default value well-typedness).
  - Preservation is **one named lemma per typing rule case (41 cases)**; each
    re-establishes *every* clause of the invariant.

- **Weakening is the other load-bearing lemma.** `E₁ ⊒ E₂` (subsumption) means
  there is a bijective reference substitution `σ` with
  `L(paths(σ ρ, σ ρ')) ⊆ L(paths(ρ, ρ'))` for all pairs. Used at control flow
  joins and calls. The **direction of inclusion matters and is the single most
  common source of mistakes** (see §5).

- **Two auxiliary lemmas you will keep reaching for:**
  - *Regex path transfer*: if `v₁, v₂ : τ` and field path `p` navigates through
    `v₁`, it also navigates through `v₂`. This — **not** path-connectivity — is
    what discharges the `T-WriteRef` preservation case.
  - *Derivative-strips-prefix*: `f·w ∈ L(r₁·r₂) → w ∈ L(δ(r₁,f)·r₂)`, used in the
    concatenation case of path transfer.

- **Non-vacuity.** `SoundnessAssumptions` bundles **23 preconditions**. To prove
  the assumptions are satisfiable (not vacuously false), every runtime test
  instantiates `type_soundness_dec` and discharges the precondition by
  `decide`/evaluation, yielding a kernel-checked per-execution certificate.

---

## 5. How to collaborate on these proofs (working conventions)

These practices are what kept the assistant productive; follow them.

1. **Decompose aggressively into named lemmas.** Before attempting a large
   obligation (a preservation case, a weakening case), extract it into a
   top-level `lemma` with an explicit statement. This keeps each goal inside the
   context window and makes the structure auditable. Weakening was built as ~20
   per-case lemmas; preservation likewise. Prefer "extract 5 reusable lemmas,
   then simplify the cases" over one monolithic tactic block.

2. **Never try to prove a false statement — name the missing invariant
   instead.** The recurring failure mode was attacking a plausible-but-false
   lemma. If an obligation looks false (e.g. "all coexisting references are
   connected by a path" — false for independently created borrows), *stop* and
   either produce a counterexample or identify the invariant clause that is
   actually needed. Strengthening `WellTypedState` is normal and expected.

3. **Mind the direction of subsumption.** When applying weakening, `E₁ ⊒ E₂` is
   asymmetric. Double-check which environment is the more restrictive (more
   paths) one before rewriting; do not invert the two.

4. **Get the argument order of `extend`/`update_with_extension` right.** Inbound
   edges use concatenation `paths(ρ'', ρ') = paths(ρ'', ρ)·p`; outbound edges use
   the derivative `paths(ρ', ρ'') = δ(paths(ρ, ρ''), p)`. Swapped arguments
   produce nonsensical paths that still typecheck locally but break later —
   verify against a small example.

5. **Explain proofs bottom-up.** When asked to describe an approach, start from
   the sub-goals and build toward the top statement; this exposes dead ends
   early.

6. **Propagate uniformly for extensions.** Adding a feature (a path element, a
   value/type compatibility case) means threading the *same* pattern through
   every existing lemma. Do it mechanically and consistently rather than
   re-deriving each site.

7. **Steer at the level of goals and plans**, not individual tactics.
   Representative requests: *"decompose the preservation statement into one named
   lemma per statement kind"*; *"this obligation looks false for independently
   created references — give a counterexample or name the missing invariant
   clause"*.

---

## 6. Lean 4 pitfalls observed in this project

- **`sorry`/`axiom` are forbidden** in committed code (restated because
  it matters most).
- **`List.mem_map_of_mem`**: `f` is *implicit* — write `(f := Prod.snd) h`.
- **`List.not_mem_nil _`** yields `False`, not `¬ a ∈ []`; prefer `nomatch hmem`.
- **`split at h` on `Option.bind`** splits the *outer* some/none, not the inner
  match; `rename_i` then captures the wrong variables. Split the inner match
  explicitly with `cases hlk : lookup … with …`.
- **`some x = some y`**: use `simp only [Option.some.injEq] at h; subst h`.
  `obtain rfl := h` does not fire on `some x = some y`.
  For ref/type injections: `simp only [Option.some.injEq, MoveType.ref.injEq]`.
- **`bne` vs `decide (· ≠ ·)`**: `a != b` is `!(a == b)` definitionally, but is
  *syntactically* different from `decide (a ≠ b)`. Filter predicates must match
  exactly what the definition produces (`AssocMap.insert` filters with `!=`).
- **`List.lookup` direction**: in `lookup a ((k,v)::es)` the search key `a` is on
  the LEFT of `==`, the entry key `k` on the RIGHT. `lookup_insert_ne … (hne : k' ≠ k)`
  takes `hne` as *lookup-key ≠ insert-key*.
- **`native_decide` fails on `TypeEnv`** — it has a function-valued field
  (`paths`), so `DecidableEq` cannot be synthesised. For concrete
  label environment lookups use `rfl` (the kernel compares only string keys).
- **`rw` through struct projections / `update`** fails (no syntactic match).
  Pattern: bind a hypothesis with the explicit type using definitional equality,
  then `rw` on that — `have h' : lookup (insert m x v) y = some r := h; rw [lookup_insert_same] at h'`.
- **`subst h` (where `h : a = b`) eliminates the RHS `b`.** `rcases … with rfl`
  on `r = t` eliminates `t`. If you need both names later, use `rw [h]` instead.
- **`unfold f at h` fails through a local `let`**: unfold the `let` binding first
  (`unfold pe' f at h`).
- **Existentials**: `trivial` cannot close `∃ n, .refid 0 = .refid n`; supply the
  witness (`exact ⟨0, rfl⟩`).
- **Inline `have … ; omega` inside `(by …)`** can cause parse failures; pull it
  out into a separate `have` with an explicit type.
- **Inline struct literal as a function argument** (e.g.
  `freshenBlockEnv t { … }`) is ambiguous with a do-block; define the struct as a
  separate `private def`.
- **Scoping**: outer variables are not visible inside `by` blocks nested in an
  `exact { … }` structure literal.

---

## 7. Conventions

- **UK spelling** in prose (matches the paper).
- **Commit messages** state the proof obligation discharged or the fix made,
  e.g. "Prove preservation_writeRef (sorry-free)", "Fix reversed
  update_with_extension args in assign rule". Snapshot commits during a long
  proof push are fine; squash only if asked.
- **Anonymity (double-blind paper supplement)**: the supplement submitted with
  the double-blind paper must be anonymous — do not add author names,
  affiliations, emails, or repository URLs to source or docs. The anonymised
  build (`make artefact-anon`) scrubs identifying strings from `.lean`/`.md`/`.mvir`
  files. (The OOPSLA Artifact Evaluation is single-blind, so the AE archive
  produced by `make artefact` is not anonymised.)
- **Tests are part of the spec.** When changing a typing rule, update the
  accepted/rejected expressivity and litmus tests and the alpha-equivalence
  parser tests; a rule change that breaks conformance with the production checker
  is a bug in the change, not the tests.
