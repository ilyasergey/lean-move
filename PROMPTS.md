# Representative development prompts

This file accompanies the artefact and the paper's *AI-Assisted Mechanisation*
section. It records a set of **representative prompts** that drove the
construction of the LeanMove formalisation with the AI coding assistant, from
the initial encoding of the typing rules through the soundness proofs and the
vector/enum extensions.

## A note on provenance

The development was carried out in an interactive assistant, and the raw,
turn-by-turn session transcripts were not retained. The prompts below are
therefore **representative and reconstructed**, not a verbatim log: they are
distilled from the project's git history, the development working notes, and the
recollection of the human prover, and each block is annotated with the date(s)
of the corresponding work. They reflect the *style and granularity* of the
actual interaction — natural-language steering at the level of goals,
decompositions, and design decisions, not individual tactics. Two of them
(marked *verbatim*) are quoted directly in the paper.

The work proceeded in phases that line up with the commit-intensity figure in
the paper: design/encoding → algorithmic checker → soundness proofs (with the
weakening and call-rule peaks) → testing/parser → vectors → enums.

---

## Phase 0 — Encoding the typing rules (Dec 2025 – Jan 2026)

The MoveLight calculus and the paper-level typing rules were human-designed,
following discussions with the designers of the production Move borrow checker.
The assistant encoded them in Lean and built the surrounding infrastructure.

> Encode the MoveLight statement language in ANF: every statement carries its
> continuation, and `ret`/`jump`/`branch` are terminal. Give me `Expr` and
> `Stmt` inductives matching the grammar we sketched, plus `beq`/`DecidableEq`.

> Implement the relational typing judgement `Λ; E ⊢ s : T` as an inductive
> relation, one constructor per statement form. Start with the borrowing and
> ownership-transfer rules (copy, move, borrow, borrow-field, write-ref,
> freeze), then control flow (jump, branch, call, ret), then pack/unpack and
> release/abort.

> Refactor control flow into basic blocks with a `LabelEnv` mapping each block
> label to the type environment expected at its entry, so `jump`/`branch` can be
> checked against it.

*(Dec 18, 2025 — jump/branch rules; basic blocks + `LabelEnv`; return rule checks
no locals are borrowed; `typecheck_fun`; freeze consumes the old reference.)*

> Add concrete-syntax macros so the test programs read like the MoveLight in the
> paper, and add regex notation with Brzozowski derivatives so I can write path
> expressions directly.

*(Jan 8, 2026 — AST macros and regex/derivative notation.)*

> Transpile this batch of programs from the Move bytecode verifier's
> reference-safety expressivity tests into MoveLight ASTs, and embed the original
> MoveIR source as a comment in each example file.

*(Jan 21, 2026 — expressivity examples transpiled from the Move bytecode-verifier suite.)*

---

## Phase 1 — Algorithmic checker (Jan 2026)

> Define an executable Boolean `check_stmt` that decides the relational
> judgement, and prove `check_stmt … = true → typecheck_stmt …` (algorithmic
> soundness). Keep it a single syntax-directed forward pass — no search, no
> backtracking.

> Inline `typecheck_usage` and `typecheck_expr` into `typecheck_stmt` and put
> the whole checker in continuation-passing style so each statement transforms
> the environment and recurses on the continuation.

*(Jan 22, 2026 — algorithmic `check_stmt` with soundness; CPS refactor.)*

---

## Phase 2 — Soundness infrastructure and preservation (early–mid Feb 2026)

This was the main effort. The pattern throughout: state the invariant, attempt a
case, discover a missing clause, strengthen the invariant, repeat.

> Set up the type-soundness scaffold: small-step semantics with a fuel counter,
> the classification of runtime errors into *preventable* and *acceptable*, and
> the regex-soundness lemmas (emptiness, `⊆ {ε}`, disjointness) we will need.

*(Feb 12 — small-step semantics; type-soundness scaffold.)*

> **Decompose the preservation statement into one named lemma per statement
> kind.** *(verbatim — quoted in the paper.)* Give each lemma an explicit
> statement re-establishing the full `WellTypedState` invariant, and prove the
> easy passthrough cases (literals, copy, move, release) first.

> Add inversion lemmas for every `typecheck_stmt` constructor so each
> preservation case can destructure the typing derivation cleanly.

*(Feb 13 — preservation plan; inversion lemmas; extracted cases; release case;
assign cases; borrowImm.)*

> This `rmap_paths` obligation keeps recurring across borrow cases — extract it
> as a reusable lemma (`rmap_paths_update_with_epsilon`) and apply it uniformly.

*(Feb 13 — extracted `rmap_paths_update_with_epsilon` and reused it.)*

> We need more invariant clauses: add `varEnv_refs_in_pathEnv`,
> `siteEnv_refs_in_pathEnv`, and `live_refs_unique` to `WellTypedState`, and
> show every existing case still re-establishes them.

*(Feb 13 — added invariant clauses; further clauses 18–20 on Feb 15.)*

> Make environment well-formedness decidable so the example files stop carrying
> manual well-formedness proofs.

*(Feb 14 — decidable environment well-formedness; `initState_safe` +
`SoundnessAssumptions`; `type_soundness_dec`.)*

> Extract the repeated reasoning in these preservation cases into reusable
> lemmas, then simplify the cases that use them.

*(Feb 14 — "extract 7 reusable lemmas, simplify 6 cases"; "extract 5 more, simplify 4".)*

### A false-statement trap (write-ref)

> *(after a stalled attempt)* This obligation — that every coexisting reference
> is connected by a path in the path environment — **looks false for references
> created independently**; give a counterexample or name the missing invariant
> clause. Don't try to prove it as stated.

The resolution was to use the **regex path-transfer lemma** instead: since the
old and new values at the written location share a type, all existing field
paths remain navigable regardless of how the references were created.

*(Feb 16 — "Prove preservation_writeRef (sorry-free)"; unpack case.)*

### A real bug found through a failed proof (assignment rule)

> The assign case won't close and the paths it produces are nonsensical. Check
> the argument order to the path-extension operation in the assignment rule
> against the borrow-field rule.

The arguments to `update_with_extension` were reversed in the assignment rule —
fixed, and the case then went through.

*(Feb 6 — "Fix reversed update_with_extension args in assign rule and prove assign case".)*

---

## Phase 3 — Weakening (the Feb 17 peak)

> Prove the weakening lemma `E₁ ⊒ E₂ ∧ Λ; E₁ ⊢ s : T → Λ; E₂ ⊢ s : T`. Define
> subsumption via a bijective reference substitution `σ` with
> `L(paths(σ ρ, σ ρ')) ⊆ L(paths(ρ, ρ'))`. Build it as one lemma per typing-rule
> case, exactly like preservation, and thread `σ` through every environment
> component.

> The σ-substitution is inverting on me again: be explicit about which
> environment is the more restrictive one (`E₁`, more paths) and which inclusion
> direction each goal needs before rewriting.

*(Feb 16–18 — weakening infrastructure; "extract 6 large cases into lemmas";
remaining cases extracted; "Weakening.lean is now sorry-free".)*

---

## Phase 4 — Call/return rules → zero sorrys (Feb 18–19)

> Implement `connect` for the call rule: for each mutable returned reference add
> only inbound `.∗` paths (so the result is immediately writable); for immutable
> returns also add outbound paths; and add paths from `ρ₀` to each output.

> The call case fails and the output check rejects safe programs. Audit the call
> rule: I suspect the conservative `extend_with_star` is applied with swapped
> arguments and the output check is overly restrictive.

Both suspicions were correct — swapped `extend_with_star` arguments and an
over-strict output check.

*(Feb 17 — "Fix call typing rule: bidirectional extend_with_star, output
population"; "swap extend_with_star args, remove overly restrictive check, add tests".)*

> Refactor `ret` to return a list of parameter types with the four safety
> conditions (types conform; no path from `ρ₀`; mutable returns pass
> `check_outbound`; mutable returns don't alias each other), then prove the `ret`
> preservation case.

> Now prove `preservation_call` and eliminate the last `sorry` from
> `Preservation.lean`.

*(Feb 18–19 — ret refactor; ret return conditions; `preservation_ret`; "Prove
preservation_call: eliminate all sorrys"; "Eliminate last sorry".)*

> *(committed by hand during an assistant outage)* Introduce the new
> stack-safety predicate and the return-preservation scaffolding.

*(Feb 18 — the manual commit made during an assistant outage.)*

---

## Phase 5 — Parser, conformance, and non-vacuity (Feb 22)

> Write a parser and translator from MoveIR text to MoveLight ASTs, and replace
> the inline AST strings in the tests with `include_str` of `.mvir` files so the
> same source feeds both parsing and type-checking tests.

> Add alpha-equivalence tests: parse each `.mvir` file and check the result is
> alpha-equivalent to a hand-written reference AST.

> Simplify the test environments so there are no magic refid numbers — use
> `freshenBlockEnv` plus an order-independent refid-matching search
> (`extendRefSubst`) validated by regex subsumption.

> Extend the soundness theorem so it rules out *all eight* preventable runtime
> errors, and refine the return writability check so it examines only live
> sites rather than all tracked references.

The last clause was the third design-level bug — the return writability check
was over-broad. (It caused false rejections only; no deployed program was
affected, and the fix was confirmed with the Move team.)

*(Feb 22 — parser + pretty-printer; alpha-equivalence tests; test-environment
simplification; "rule out all 8 preventable runtime errors"; "Consume call input
sites from siteEnv; refine ret writability check".)*

---

## Phase 6 — Vectors (Mar 3–4, ~one day of proof work)

> Add vector support as a uniform extension: a single `.vecElem` path element for
> all element indices, `BasicMoveType.tvec`, the eight Move vector operations,
> and their typing rules. `vec_mut_borrow` mirrors `borrow-field` (extend with
> `.vecElem`); `vec_push_back`/`pop_back`/`swap` require `check_outbound` like
> `write-ref` and then remove all element references from the path environment.

> Thread `.vecElem` through the value/type-compatibility relation and every
> existing soundness lemma, applying the same pattern at each site, then close
> the vector preservation cases with zero sorrys.

*(Mar 3–4 — vector phases 1–9; rejection tests from the Sui bytecode-verifier
suite; "Complete type soundness proof for vector extension (zero sorrys)".)*

---

## Phase 7 — Enums and the flat encoding (Mar 5–10)

> Add non-recursive enums: `pack_variant`, `unpack_variant` (checks the
> constructor at runtime), and `variant_switch` (dispatch, reusing the `T-Jump`
> subsumption per arm). Stub the type-checker cases first, then the semantics.

### A design decision the assistant could not find on its own

> Encoding enum values so that only the active variant's fields are present
> **breaks the path-transfer lemma** — after a write that changes the active
> variant, paths into the old variant's fields become unnavigable. Your
> nested-`Option` proposal doesn't fix this. Use a **flat encoding**: represent
> an enum as a tagged record carrying *all* variants' fields under qualified
> names (`Variant.field`), inactive ones filled with type-correct defaults, so
> two values of the same enum type always have identical field structure and
> path transfer holds unconditionally.

> Add the six new `WellTypedState` clauses the flat encoding needs (enum-env
> consistency, name/variant/field uniqueness, qualified-field uniqueness,
> default-value well-typedness) and thread `enumEnv` consistency through all 35
> invariant reconstructions.

*(Mar 5–10 — enum stubs; work-in-progress; complete enum support; enum invariant
+ InitState; "Multi-variant enum soundness: flat encoding, zero sorrys, decidable
certificate".)*

---

## Phase 8 — Artefact packaging (Mar 13–15)

> Add a Makefile target that archives the committed tree and, for the
> double-blind paper supplement, drops the Makefile itself and `sed`-scrubs
> identifying strings from the source; exclude the working-notes directory from
> the archive.

*(Mar 13–15 — Makefile and archive targets; working-notes directory removed.)*

---

## Cross-cutting lessons (mirrors the paper)

- **Where the assistant was strongest:** proof *repair* — propagating a
  definition/invariant change across a large proof landscape (the one-day vector
  extension touched 30+ files because the change was uniform); routine
  passthrough preservation cases; boilerplate and list/infrastructure lemmas.
- **Where it needed steering:** picking the right *problem decomposition* for
  novel statements (it would otherwise attempt a plausible-but-false lemma); the
  *direction* of subsumption in weakening; and runtime-representation design
  decisions such as the flat enum encoding.
- **The single most effective practice:** aggressive lemma extraction —
  decomposing every large obligation into independently provable named lemmas,
  which kept goals in-context and produced an auditable, modular proof.
- **The human's role was steering:** confirming invariant clauses (most of the
  35 were assistant-proposed and human-vetted), choosing representations, and
  cutting off unproductive attempts early — not writing tactic scripts.
