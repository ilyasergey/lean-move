# The production Rust implementation, matched to the Lean artefact

The paper's **Section 6** concerns the **Rust** implementation of the regex-based
borrow checker inside the Move bytecode verifier of the Sui client — a different
codebase from the Lean formalisation in this artefact. This guide says **where it
is**, **what is what**, links the important parts to the **online** source, and
**matches each part to the Lean development**.

## Where it lives

The implementation is **not vendored** into this artefact (it is large, and its
determinism is already pinned by commit). It lives in the public
**`MystenLabs/sui`** monorepo at the exact revision the benchmark builds against:

- **Repository:** [`github.com/MystenLabs/sui`](https://github.com/MystenLabs/sui) (public).
- **Exact commit:** [`ab36f2fea373075f42ffb158aaf37b66e4b68fc6`](https://github.com/MystenLabs/sui/commit/ab36f2fea373075f42ffb158aaf37b66e4b68fc6)
  — repo root at that commit:
  [`github.com/MystenLabs/sui/tree/ab36f2f…`](https://github.com/MystenLabs/sui/tree/ab36f2fea373075f42ffb158aaf37b66e4b68fc6).
  This SHA is pinned as `rev = …` on the `move-*` git dependencies in
  [`reference-safety-bench/Cargo.toml`](reference-safety-bench/Cargo.toml).
- **The checker crates (pinned):**
  [`external-crates/move/crates` @ ab36f2f](https://github.com/MystenLabs/sui/tree/ab36f2fea373075f42ffb158aaf37b66e4b68fc6/external-crates/move/crates).
- **Browse locally:** after any `cargo build` / `./corroborate.sh`, Cargo has
  checked the revision out under
  `~/.cargo/git/checkouts/sui-*/ab36f2f/external-crates/move/crates/`.

### Why it isn't bundled in the artefact

We deliberately do **not** vendor these Rust sources into the artefact:

- **It is a separate production codebase, not the object of this artefact.** The
  artefact's contribution is the Lean *specification and soundness proof*; the
  Sui verifier is an independent implementation of the same design, maintained in
  its own repository. Bundling it would blur that boundary.
- **Determinism is already guaranteed without it.** The exact revision is pinned
  by commit SHA in `Cargo.toml`, and every transitive dependency in `Cargo.lock`,
  so `cargo build` fetches byte-identical sources on any machine. Vendoring would
  add nothing to reproducibility.
- **Size.** Vendoring the pinned crates plus their full transitive graph is
  ~230 MB (`cargo vendor`); a raw checkout of the monorepo is ~1 GB. Either would
  dwarf the entire rest of the artefact (a few MB) for no scientific benefit.
- **Network is required anyway.** Reproduction already needs the network — for
  the Rust toolchain (`rustup`) and, for the full run, the public dataset — so
  fetching the pinned crates on first build costs nothing extra (~1 minute).

For a fully offline build (e.g. an air-gapped evaluation), run `cargo vendor` in
the benchmark crate to materialise the sources locally, or fetch them once on a
connected machine; the pinned revision guarantees identical results either way.

## What is what (with online links)

The Rust code is factored just like the paper and the Lean development: a
**regex + path graph library**, a **verifier pass** that drives it over Move
bytecode, and the **old** graph-based checker kept in-tree as the benchmark's
baseline.

### `move-regex-borrow-graph` — the core library

[crate root](https://github.com/MystenLabs/sui/tree/ab36f2fea373075f42ffb158aaf37b66e4b68fc6/external-crates/move/crates/move-regex-borrow-graph)

| File (online) | What it is |
|------|------------|
| [`src/regex.rs`](https://github.com/MystenLabs/sui/blob/ab36f2fea373075f42ffb158aaf37b66e4b68fc6/external-crates/move/crates/move-regex-borrow-graph/src/regex.rs) | The regular expression type `Regex<Lbl>` over path labels and its operations — the Brzozowski **derivative**, emptiness / `ε` tests, union/concatenation/star. The engine behind edge extension and the write check. |
| [`src/collections.rs`](https://github.com/MystenLabs/sui/blob/ab36f2fea373075f42ffb158aaf37b66e4b68fc6/external-crates/move/crates/move-regex-borrow-graph/src/collections.rs) | The **path environment** as a transitively closed graph (`Graph`, `Path`). Edge construction is the paper's `extend`: `extend_by_epsilon` (copy/freeze), `extend_by_label` (field borrow, via the derivative), `extend_by_dot_star_for_call` (the Kleene-star `.∗` call extension, §2.6). `release`/`release_all` = node removal; `join` = merge at control flow joins (subsumption); `canonicalize` = normalise reference names. |
| [`src/references.rs`](https://github.com/MystenLabs/sui/blob/ab36f2fea373075f42ffb158aaf37b66e4b68fc6/external-crates/move/crates/move-regex-borrow-graph/src/references.rs) | `Ref` — abstract references (the paper's `ρ`). |
| [`src/graph_map.rs`](https://github.com/MystenLabs/sui/blob/ab36f2fea373075f42ffb158aaf37b66e4b68fc6/external-crates/move/crates/move-regex-borrow-graph/src/graph_map.rs), [`src/meter.rs`](https://github.com/MystenLabs/sui/blob/ab36f2fea373075f42ffb158aaf37b66e4b68fc6/external-crates/move/crates/move-regex-borrow-graph/src/meter.rs) | Indexed graph storage; gas/metering hooks. |
| [`src/tests/`](https://github.com/MystenLabs/sui/tree/ab36f2fea373075f42ffb158aaf37b66e4b68fc6/external-crates/move/crates/move-regex-borrow-graph/src/tests) | Unit and **property** tests for the regex and the graph. |

### `move-bytecode-verifier/src/regex_reference_safety` — the new verifier pass

[module root](https://github.com/MystenLabs/sui/tree/ab36f2fea373075f42ffb158aaf37b66e4b68fc6/external-crates/move/crates/move-bytecode-verifier/src/regex_reference_safety)

| File (online) | What it is |
|------|------------|
| [`mod.rs`](https://github.com/MystenLabs/sui/blob/ab36f2fea373075f42ffb158aaf37b66e4b68fc6/external-crates/move/crates/move-bytecode-verifier/src/regex_reference_safety/mod.rs) | Transfer functions: an abstract interpreter walking each function's bytecode instruction by instruction, updating the path graph and enforcing the checks. Its `verify` is what the benchmark times as **new**. |
| [`abstract_state.rs`](https://github.com/MystenLabs/sui/blob/ab36f2fea373075f42ffb158aaf37b66e4b68fc6/external-crates/move/crates/move-bytecode-verifier/src/regex_reference_safety/abstract_state.rs) | The analysis domain `AbstractState` wrapping the regex `Graph`; `Label` (path elements = fields/variants), `ValueKind`, the write/borrow-safety check (the paper's `check_outbound`), and call handling (`extend_by_dot_star_for_call`). |
| [`serializable_state.rs`](https://github.com/MystenLabs/sui/blob/ab36f2fea373075f42ffb158aaf37b66e4b68fc6/external-crates/move/crates/move-bytecode-verifier/src/regex_reference_safety/serializable_state.rs) | A serialisable view of the abstract state (diagnostics/persistence). |

### `move-bytecode-verifier/src/reference_safety` — the old (deployed) checker

[module root](https://github.com/MystenLabs/sui/tree/ab36f2fea373075f42ffb158aaf37b66e4b68fc6/external-crates/move/crates/move-bytecode-verifier/src/reference_safety) — the
borrow graph analysis of the deployed-checker paper [7]; its `verify` is what the
benchmark times as **old**.

## Correspondence: paper ↔ Lean ↔ production Rust

Both realise the same design in the same layered structure — a regex library, a
transitively closed path graph, and a per-unit reference safety checker — but
they are independent codebases (no shared code) and diverge in several deliberate
ways (see below). Rust links below are pinned to `ab36f2f`; a file linked once is
referred to by name afterwards.

| Paper concept | Lean (this artefact) | Production Rust |
|---------------|----------------------|-----------------|
| Regex over path labels; derivative `δ`; emptiness / `ε` | `deriv`, `only_matches_empty` in [`Structures/Regex.lean`](../LeanMove/Structures/Regex.lean) | `Regex<Lbl>` in [`regex.rs`](https://github.com/MystenLabs/sui/blob/ab36f2fea373075f42ffb158aaf37b66e4b68fc6/external-crates/move/crates/move-regex-borrow-graph/src/regex.rs) |
| Path environment Π (transitively closed) | [`Structures/PathMap.lean`](../LeanMove/Structures/PathMap.lean) | `Graph`, `Path` in [`collections.rs`](https://github.com/MystenLabs/sui/blob/ab36f2fea373075f42ffb158aaf37b66e4b68fc6/external-crates/move/crates/move-regex-borrow-graph/src/collections.rs) |
| `extend`: `ε` (copy/freeze) / field / `.∗` (call) | `extend` / `update_with_extension` (`PathMap.lean`) | `extend_by_epsilon` / `extend_by_label` / `extend_by_dot_star_for_call` (`collections.rs`) |
| Node removal (release / consumed refs) | node removal (`PathMap.lean`) | `release` / `release_all` (`collections.rs`) |
| Environment merge at control flow joins | subsumption `E_L ⊒ E` (`T-Jump`; [`Weakening.lean`](../LeanMove/Typing/Soundness/Weakening.lean)) | `join` + `canonicalize` (`collections.rs`) |
| Abstract references `ρ` | `Aref` in [`Lang/MoveLight.lean`](../LeanMove/Lang/MoveLight.lean) | `Ref` in [`references.rs`](https://github.com/MystenLabs/sui/blob/ab36f2fea373075f42ffb158aaf37b66e4b68fc6/external-crates/move/crates/move-regex-borrow-graph/src/references.rs) |
| Write check `check_outbound` | `check_outbound` in [`Typing/Types.lean`](../LeanMove/Typing/Types.lean) | `is_writable` in [`abstract_state.rs`](https://github.com/MystenLabs/sui/blob/ab36f2fea373075f42ffb158aaf37b66e4b68fc6/external-crates/move/crates/move-bytecode-verifier/src/regex_reference_safety/abstract_state.rs) |
| Borrow/ownership rules (copy, move, freeze, field borrow, write) | `T-CopyRef` / `T-Move` / `T-Freeze` / `T-BorrowField` / `T-WriteRef` in [`TypeChecking.lean`](../LeanMove/Typing/TypeChecking.lean) | `copy_loc` / `move_loc` / `freeze_ref` / … (`abstract_state.rs`) |
| Per-unit checker (driver) | `check_stmt` (algorithmic) / `typecheck_stmt` (relational) over MoveLight | `verify` → `analyze_function` + `TransferFunctions::execute` in [`mod.rs`](https://github.com/MystenLabs/sui/blob/ab36f2fea373075f42ffb158aaf37b66e4b68fc6/external-crates/move/crates/move-bytecode-verifier/src/regex_reference_safety/mod.rs) |
| Deployed graph-based checker (baseline only) | — (not modelled; paper's [7]) | [`reference_safety/`](https://github.com/MystenLabs/sui/tree/ab36f2fea373075f42ffb158aaf37b66e4b68fc6/external-crates/move/crates/move-bytecode-verifier/src/reference_safety) |
| Soundness theorem | `type_soundness` in [`TypeSoundness.lean`](../LeanMove/Typing/TypeSoundness.lean) | — (deployed code; not proved) |

## Where the Lean model and the Rust implementation diverge

They enforce the same discipline but are not line-for-line equivalent. The main
differences, all deliberate:

1. **Input & state model.** Lean checks **MoveLight**, an ANF calculus with named
   *sites* — a faithful model of MoveIR that abstracts away the operand stack.
   The Rust pass runs on the real **stack-based Move bytecode**, so it maintains
   an abstract operand stack (`AbstractStack<AbstractValue>`) and lowers each
   `Bytecode` instruction to graph operations. The regex/path graph core is the
   same; the surrounding plumbing (sites vs. stack slots) differs.

2. **Inference vs. checking.** The Rust checker *infers*: `verify` calls
   `analyze_function`, a **dataflow analysis run to a fixpoint** that computes a
   `BlockInvariant` per basic block and `join`s at merge points. The Lean checker
   *only checks*: `check_stmt` takes the per-block label environment **as given**
   and makes a single forward pass — the translation validation architecture, in
   which the inferring abstract interpreter is intentionally **not** mechanised
   (paper §5.3). Lean's counterpart to `join` is subsumption `⊒` against the
   supplied environments, not iterative fixpoint computation.

3. **Metering / gas.** The Rust pass threads a `Meter` through every operation
   (`STEP_BASE_COST`, `GraphMeter`) to bound verification cost and prevent
   on-chain denial-of-service. The Lean checker has no metering (fuel appears
   only in the *operational semantics*, not in the checker).

4. **Feature coverage.** The Rust code handles the full production instruction
   set (global-storage operations, generics on monomorphised code, abilities,
   every bytecode). Lean models the core calculus plus vectors and enums, and
   deliberately omits generics, abilities, and global storage (paper §5.3).

5. **Auxiliary machinery.** The Rust module ships `serializable_state.rs`
   (serialisation for diagnostics/persistence), which has no Lean counterpart;
   the Lean side ships the *proof* artefacts (the `WellTypedState` invariant,
   weakening, preservation), which have no Rust counterpart.

6. **Status.** Lean is machine-checked **sound**; the Rust code is the
   **deployed implementation** with no machine-checked proof. This artefact does
   **not** prove the two equivalent: the Lean proof establishes soundness of the
   *design*, and the benchmark corroborates the Rust implementation's
   *performance* (Section 6). Formally bridging them — proving the Rust pass
   refines the Lean model — is future work.
