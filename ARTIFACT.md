# Artifact Evaluation Guide

Artefact for the OOPSLA 2026 paper *Tracking Borrows with Regular Expressions*.

This artefact has **two independent parts**, matching the two kinds of claim in
the paper:

1. **The Lean development** — the bulk of the artefact (guide §2–§7). It is the
   complete Lean 4 mechanisation of the regex-based Move borrow checker: the
   language, regular expression library, small-step operational semantics, the
   relational and algorithmic type systems, the machine-checked **type soundness
   proof**, the MoveIR parser/translator, and the conformance test suite. It is
   **plain source** needing only a Lean toolchain (no Docker/VM); because Lean's
   build re-checks every proof with the kernel, a successful build *is* the
   verification. This part substantiates the paper's **formal** claims —
   soundness, algorithmic checker soundness, decidable certificates (Secs. 2–5).

2. **The Rust benchmark** — `benchmark/` (guide §8). A self-contained harness
   that substantiates the paper's **Section 6 performance** claim. Those numbers
   come from a *different* codebase — the production Move verifier in the Sui
   client, written in **Rust** — not from the Lean development. The harness times
   the deployed (graph-based) against the new (regex-based) checker, built against
   a pinned public Sui revision, and has its own Rust toolchain and dataset.

The two parts are **independent** — separate toolchains, no shared code — and
share only the *design*: the Lean side proves that design sound; the Rust side is
a production implementation of it, whose performance the benchmark measures. The
artefact does **not** prove the two equivalent; see
[`benchmark/IMPLEMENTATION.md`](benchmark/IMPLEMENTATION.md) for the part-by-part
mapping and the deliberate divergences. You can evaluate either part on its own;
`make eval` runs both (see the Quick start below).

Requested badges and their justification are in [`STATUS.md`](STATUS.md); a prose
overview of the metatheory is in [`metatheory.md`](metatheory.md).

---

## Quick start — one-command evaluation

From the repository root:

| Command | What it does |
|---------|--------------|
| `make eval` | **Evaluate everything** — build and kernel-check the Lean proofs (with the axiom-clean check) *and* corroborate the Section 6 benchmark. |
| `make eval-lean` | The **Lean** half only: `lake exe cache get && lake build`, then the `#print axioms` check (§2–§3). |
| `make eval-rust` | The **Rust** half only (paper §6): build the benchmark and corroborate it on the bundled sample — no dataset download (§8). |

Requirements and a step-by-step walkthrough follow (Lean: §1–§3; benchmark: §8).

---

## 1. Requirements (Lean and Rust)

The artefact has two independent parts with separate toolchains — the **Lean**
development (§2–§7) and the **Rust** Section 6 benchmark (§8). Either can be
evaluated on its own; `make eval` runs both.

**Common.**
- **OS:** Linux (x86-64) or macOS (x86-64 or Apple Silicon); Windows via WSL2
  should also work.
- **No special hardware**, no GPU, no telemetry. Network is used only to install
  toolchains and fetch pinned dependencies/caches (per part, below) — never
  during proof-checking.

**Lean development (§2–§7).**
- **Toolchain:** `elan`, which reads `lean-toolchain` and installs the pinned
  Lean automatically. Pinned versions (declared in `lean-toolchain` /
  `lakefile.lean`; the proof depends only on these):

  | Component | Version |
  |-----------|---------|
  | Lean 4    | `leanprover/lean4:v4.27.0` |
  | mathlib4  | `v4.27.0` |
  | batteries | `v4.27.0` |

- **Disk:** ≈ 8–10 GB (the mathlib build cache dominates).
- **RAM:** 8 GB minimum, 16 GB recommended (the large `Preservation.lean` /
  `Weakening.lean` are memory-intensive to elaborate).
- **Network:** once, to install `elan` and download the prebuilt mathlib cache.

**Rust benchmark — paper Section 6 (§8).**
- **Toolchain:** a Rust toolchain pinned by `benchmark/rust-toolchain.toml`
  (edition 2024 → Rust ≥ 1.85); `rustup` installs it automatically.
- **Network:** once on first build, to fetch the pinned Sui crates.
- **Data:** the corroboration sample is **bundled** (`benchmark/sample.zip`,
  ~7 MB) — no download. Only the optional full corpus run (`run.sh`) fetches the
  ~13–16 GB public dataset.
- **Disk:** a few GB for the Rust build; ~13–16 GB more only for the full corpus.

---

## 2. Getting started with the Lean development (kick-the-tires, ≈30 min)

The goal of this phase is only to confirm the toolchain is set up and the project
compiles — not to build the whole proof yet.

**Step 1 — Install `elan`** (the Lean toolchain manager), if not already present:

```bash
curl https://elan.lean-lang.org/elan-init.sh -sSf | sh
source "$HOME/.elan/env"      # or restart your shell
```

**Step 2 — Fetch the prebuilt mathlib cache** (avoids compiling mathlib from
source, which would take hours):

```bash
cd lean-move
lake exe cache get            # downloads mathlib/batteries .olean files (~minutes)
```

**Step 3 — Compile a representative module** to confirm the setup works:

```bash
lake build LeanMove.Structures.Regex
```

This builds the regex library (Brzozowski derivative, emptiness, `⊆ {ε}`,
disjointness — the heart of the type system) and should finish quickly.

**Step 4 — Confirm there are no proof escape hatches:**

```bash
grep -rnw --include='*.lean' 'sorry'   LeanMove | wc -l   # expect: 0
grep -rn  --include='*.lean' '^axiom ' LeanMove | wc -l   # expect: 0
```

**Step 5 — Corroborate the Section 6 benchmark** (~2–3 min; full detail in §8):

```bash
make eval-rust        # builds the Rust benchmark and runs it on the bundled sample
```

This needs a Rust toolchain (auto-installed via `benchmark/rust-toolchain.toml`)
and network for the pinned Sui crates on first build; it downloads **no** dataset.
Expect a ratio ≈2× and tens of µs per function.

If Steps 1–5 succeed you are set up correctly. `make eval` runs the whole
evaluation — Lean proofs and benchmark — in one command.

---

## 3. Full evaluation of the Lean development (≈ up to 1 hour, mostly unattended)

This section is the **Lean** half of a full evaluation; the **Rust** Section 6
benchmark is §8, and `make eval` runs both in one command.

**Step 1 — Build everything.** This re-checks the entire development — every
definition, every typing rule, the algorithmic checker and its soundness bridge,
the full progress/preservation soundness proof, and every test — with the Lean
kernel:

```bash
lake exe cache get      # (no-op if already fetched)
lake build              # equivalently: make build
```

A clean exit (no `error:` output) means the kernel accepted every proof. The two
large proof files dominate wall-clock time; budget tens of minutes to ~1 hour
depending on hardware. `lake` is incremental, so re-runs are fast.

Build targets (all built by the default `lake build`):

| Target | What it checks |
|--------|----------------|
| `lake build core` | the core library: language, regex, semantics, both type systems, **all soundness proofs** |
| `lake build litmus` | small accepted/rejected litmus programs |
| `lake build expressivity` | programs transpiled from the Move bytecode verifier reference safety suite |
| `lake build examples` | litmus + expressivity together |
| `lake build parsing` | parser alpha-equivalence tests |
| `lake build runtime` | runtime conformance + the 31 per-execution `type_soundness_dec` certificates |

**Step 2 — Verify the soundness proof is complete and axiom-clean.** This is the
decisive check for a mechanised-proof artifact. The committed script
[`scripts/AxiomCheck.lean`](scripts/AxiomCheck.lean) prints the axiom
dependencies of the soundness theorems; run it (after the build above):

```bash
lake env lean scripts/AxiomCheck.lean
```

Expected output (order may vary), for **both** theorems:

```
'LeanMove.Typing.TypeSoundness.type_soundness' depends on axioms: [propext, Classical.choice, Quot.sound]
'LeanMove.Typing.TypeSoundness.type_soundness_dec' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The absence of `sorryAx` confirms the proof has no holes. (`propext`,
`Classical.choice`, `Quot.sound` are the standard classical axioms used
throughout mathlib; see §6 on the trusted computing base.)

**Step 3 — (optional) Re-confirm zero `sorry`/`axiom`** as in §2 Step 4.

---

## 4. Significant claims and where to check them (Lean and Rust)

Per the AE guidelines, here is the list of the paper's significant claims and
the artifact evidence for each. Names are fully qualified under namespace
`LeanMove.Typing.TypeSoundness` unless noted.

Line numbers index the Lean sources at the artifact's `HEAD` (the `.lean`
files are unchanged across the documentation commits, so the anchors are stable).

| # | Paper claim | Location in paper | Evidence in artifact (`file:line`) |
|---|-------------|-------------------|----------------------|
| 1 | **Type soundness** (no preventable runtime error) | Thm 3.1, §3.4 | `type_soundness` — [`TypeSoundness.lean:55`](LeanMove/Typing/TypeSoundness.lean#L55); dangling-ref form `type_soundness_no_danglingRef` — [`:68`](LeanMove/Typing/TypeSoundness.lean#L68) |
| 2 | Soundness = **progress + preservation** | §3.4 | `preservation` — [`Preservation.lean:11086`](LeanMove/Typing/Soundness/Preservation.lean#L11086); progress — [`Progress.lean:436`](LeanMove/Typing/Soundness/Progress.lean#L436) |
| 3 | **Weakening** (Lemma 3.2): `E₁ ⊒ E₂ ∧ ⊢ s` ⇒ `⊢ s` under `E₂` | Lemma 3.2, §3.4 | `typecheck_stmt_weaken` — [`Weakening.lean:7801`](LeanMove/Typing/Soundness/Weakening.lean#L7801) |
| 4 | **Regex path transfer** (Lemma 3.3) | Lemma 3.3, §3.4 | `HasType_transfer` — [`Defs.lean:1927`](LeanMove/Typing/Soundness/Defs.lean#L1927); `readPath_HasType_transfer` — [`:1676`](LeanMove/Typing/Soundness/Defs.lean#L1676) |
| 5 | Algorithmic checker is **sound w.r.t. the relational spec** | §5.2 | `check_stmt_sound` — [`AlgorithmicTypingSoundness.lean:1814`](LeanMove/Typing/Algorithmic/AlgorithmicTypingSoundness.lean#L1814) |
| 6 | `WellTypedState` invariant has **29 clauses** (35 with enums) | §3.4, §4.2 | `WellTypedState` — [`Defs.lean:619`](LeanMove/Typing/Soundness/Defs.lean#L619) |
| 7 | `SoundnessAssumptions` bundles preconditions; collapsed into a **decidable** check | §5.2 | `SoundnessAssumptions` — [`InitState.lean:324`](LeanMove/Typing/Soundness/InitState.lean#L324); `…checkDecidable` — [`:473`](LeanMove/Typing/Soundness/InitState.lean#L473); `type_soundness_dec` — [`TypeSoundness.lean:83`](LeanMove/Typing/TypeSoundness.lean#L83) |
| 8 | **Non-vacuity:** per-execution kernel-checked safety certificates | §5.2 | 31 `type_soundness_dec` instantiations — [`Tests/Runtime/AllTests.lean`](LeanMove/Tests/Runtime/AllTests.lean) |
| 9 | Regex ops (`δ`, emptiness, `⊆ {ε}`) verified against language semantics | §3.2, §3.5 | `deriv` [`Regex.lean:65`](LeanMove/Structures/Regex.lean#L65), `only_matches_empty` (`⊆{ε}`) [`:288`](LeanMove/Structures/Regex.lean#L288), `is_empty` [`:273`](LeanMove/Structures/Regex.lean#L273), `has_nonempty_match` [`:318`](LeanMove/Structures/Regex.lean#L318); `check_outbound` — [`Types.lean:180`](LeanMove/Typing/Types.lean#L180) |
| 10 | Decidable, polynomial regex checks (no language-equivalence) | §3.5 | `check_stmt` (single forward pass) — [`AlgorithmicTypeChecking.lean:375`](LeanMove/Typing/Algorithmic/AlgorithmicTypeChecking.lean#L375); regex ops as in claim 9 |
| 11 | **Conformance** with the production checker on transpiled tests | §5.2 | accepted/rejected suites under [`Tests/Typechecking/`](LeanMove/Tests/Typechecking/) (33 expressivity + 14 litmus), built by `lake build examples` |
| 12 | **Parser/translator** correctness via alpha-equivalence | §5.2 | 35 tests under [`Tests/Parsing/`](LeanMove/Tests/Parsing/), `.mvir` sources under [`Tests/MVIR/`](LeanMove/Tests/MVIR/), `lake build parsing` |
| 13 | **Vector** extension, zero new sorrys | §4.1 | rules `let_bind_vecMutBorrow` [`TypeChecking.lean:688`](LeanMove/Typing/TypeChecking.lean#L688), `vecPushBack_rule` [`:714`](LeanMove/Typing/TypeChecking.lean#L714); `.vecElem` — [`Types.lean:131`](LeanMove/Typing/Types.lean#L131) |
| 14 | **Enum** extension via flat encoding; +6 invariant clauses | §4.2 | rules `let_bind_packVariant` [`TypeChecking.lean:743`](LeanMove/Typing/TypeChecking.lean#L743), `unpackVariant_rule` [`:761`](LeanMove/Typing/TypeChecking.lean#L761); flat encoding in [`Semantics/Smallstep.lean`](LeanMove/Semantics/Smallstep.lean) |
| 15 | Whole development is `sorry`/`axiom`-free | §5.1 | §2 Step 4 and §3 Step 2 above |
| 16 | LOC / commit-timeline figures (Table 1, Fig 17) | §5.1 | reproducible from the repo — see §7 |
| 17 | **Section 6 performance:** regex checker ≈2.2× the deployed checker, ≈30 µs/function | §6 | Rust harness [`benchmark/`](benchmark/); `./corroborate.sh` (bundled sample — we observed ≈2.0×, ~18 µs on an Apple M2) or `./run.sh` (full corpus); see §8 |
| 18 | **Backwards compatibility / strictly more expressive** (every function the deployed checker accepts is accepted by the regex checker) | §6, Intro | the benchmark errors if the regex checker rejects any corpus function — [`benchmark/reference-safety-bench/src/main.rs`](benchmark/reference-safety-bench/src/main.rs); see §8 |

> **Section 6 (performance) is reproducible too**, via the separate Rust harness
> in [`benchmark/`](benchmark/) — see §8. It is a different codebase (the Sui
> Rust verifier, not the Lean development), with its own toolchain and a public
> dataset fetched on demand (never stored in this repository).

---

## 5. Paper-to-artifact correspondence — Lean development (definitions and figures)

| Paper | Artifact (`file:line`) |
|-------|----------|
| MoveLight syntax (Fig. 8) | `Expr` [`MoveLight.lean:406`](LeanMove/Lang/MoveLight.lean#L406), `Stmt` [`:428`](LeanMove/Lang/MoveLight.lean#L428), `MoveType` [`:278`](LeanMove/Lang/MoveLight.lean#L278), `Aref` [`:265`](LeanMove/Lang/MoveLight.lean#L265) |
| Typing rules (Figs. 9, 10) | `typecheck_stmt` (relational inductive) — [`TypeChecking.lean:321`](LeanMove/Typing/TypeChecking.lean#L321) |
| Algorithmic checker | `check_stmt` — [`AlgorithmicTypeChecking.lean:375`](LeanMove/Typing/Algorithmic/AlgorithmicTypeChecking.lean#L375) |
| Path environment Π: `extend`, node removal, transitive closure | [`Structures/PathMap.lean`](LeanMove/Structures/PathMap.lean) |
| `check_outbound`; derivative `δ`; emptiness; `⊆ {ε}` | `check_outbound` [`Types.lean:180`](LeanMove/Typing/Types.lean#L180); `deriv` [`Regex.lean:65`](LeanMove/Structures/Regex.lean#L65); `only_matches_empty` [`:288`](LeanMove/Structures/Regex.lean#L288) |
| Small-step semantics (Fig. 11), runtime errors (Fig. 12) | `step` [`Smallstep.lean:415`](LeanMove/Semantics/Smallstep.lean#L415); `RuntimeError` [`:264`](LeanMove/Semantics/Smallstep.lean#L264) |
| Vector rules (Fig. 14), enum rules (Fig. 16) | in `typecheck_stmt`: vectors [`TypeChecking.lean:688`](LeanMove/Typing/TypeChecking.lean#L688), enums [`:743`](LeanMove/Typing/TypeChecking.lean#L743) |

See [`metatheory.md`](metatheory.md) for the full prose walkthrough, the
project layout, and the limitations.

---

## 6. Trusted computing base, axioms, and assumptions (Lean development)

- **TCB:** the Lean 4 kernel (v4.27.0) plus the three standard classical axioms
  `propext`, `Classical.choice`, `Quot.sound` inherited from mathlib. §3 Step 2
  shows how to confirm the soundness theorem depends on exactly these and on no
  `sorryAx`.
- **No project-specific axioms and no `sorry`** anywhere in the development.
- **Assumptions stated in the theorem, not hidden:** `type_soundness` is
  parameterised by `SoundnessAssumptions` (well-formed label/enum environments,
  argument/parameter type compatibility, heap well-formedness, etc.). To guard
  against these being *vacuously unsatisfiable*, `type_soundness_dec` collapses
  them into a single decidable Boolean check, and the 31 runtime certificates
  discharge it by evaluation for concrete inputs — so the assumptions are
  demonstrably satisfiable (§4, claims 7–8).

### Deviations from the paper / what is intentionally not modelled (paper §5.3)

The formalisation omits, by design: generics (the checker runs on
monomorphised code), abilities (`copy`/`drop`, orthogonal to borrowing), global
storage, references stored *inside* records (forbidden by current Move), and the
abstract interpreter that *infers* label environments (the artifact follows a
translation validation architecture: it *checks* given environments, so an
inference bug can only reject valid programs, never accept unsafe ones).

---

## 7. Reusability and reproducing the quantitative figures (Lean development)

**Extending the development.** The vector (§4.1) and enum (§4.2) extensions are
worked examples of the standard recipe: add a path element / type compatibility
case, then thread it uniformly through the lemmas. Start from
[`CLAUDE.md`](CLAUDE.md) (architecture + conventions + Lean-4 pitfalls) and
[`metatheory.md`](metatheory.md), then read the relevant `Soundness/` file.
[`PROMPTS.md`](PROMPTS.md) records how the development was driven, phase by
phase.

**Reproducing Table 1 (LOC) and the test counts** from the repository:

```bash
# non-blank lines per major component (approximation of Table 1)
find LeanMove -name '*.lean' | xargs wc -l | sort -rn | head
# test suite sizes
ls LeanMove/Tests/Typechecking/expressivity/accepted/*.lean | wc -l   # 21
ls LeanMove/Tests/Typechecking/expressivity/rejected/*.lean | wc -l   # 12
ls LeanMove/Tests/Typechecking/litmus/{accepted,rejected}/*.lean | wc -l   # 14
ls LeanMove/Tests/Parsing/Test_*.lean | wc -l                          # 35
grep -c type_soundness_dec LeanMove/Tests/Runtime/AllTests.lean        # 31 certificates
```

**Reproducing the development timeline (Fig. 17)** — if the artifact is
distributed as a git repository:

```bash
git log --since=2025-12-01 --date=format:'%Y-%m-%d' --pretty='%ad' | sort | uniq -c
```

---

## 8. Reproducing Section 6 (performance) — the Rust benchmark (`benchmark/`)

Section 6 compares the wall-clock time of the new regex-based reference safety
checker against the deployed graph-based one. Those numbers come from the
**Rust** implementation in the Sui client, not the Lean development, so they live
in a separate, self-contained Rust harness under [`benchmark/`](benchmark/)
(with its own [`benchmark/README.md`](benchmark/README.md)).

**What it measures.** For every non-native function in a corpus of compiled Move
modules it times `reference_safety::verify` (old, graph-based) and
`regex_reference_safety::verify` (new, regex-based) back-to-back, and reports the
ratio of means plus percentiles. Both verifiers are taken from a **pinned public
Sui revision** (the `rev = …` on the `move-*` git dependencies in
[`benchmark/reference-safety-bench/Cargo.toml`](benchmark/reference-safety-bench/Cargo.toml)).

For a guide to that production Rust implementation — where each part lives online
(direct links at the pinned revision) and how it maps to the Lean development in
this artefact — see [`benchmark/IMPLEMENTATION.md`](benchmark/IMPLEMENTATION.md).

**Why the Rust sources are not packaged in the artefact.** The production checker
is a *separate* codebase (the Sui verifier), not the object of this artefact —
which is the Lean specification and soundness proof. Its exact revision is pinned
by SHA in `Cargo.toml` and `Cargo.lock`, so the fetched sources are byte-identical
and reproducible *without* vendoring; bundling them would add ~230 MB (a raw
checkout is ~1 GB) and dwarf the rest of the artefact for no benefit, while the
network is needed anyway (toolchain and, for the full run, the dataset). The
[implementation guide](benchmark/IMPLEMENTATION.md) explains this and gives a
`cargo vendor` recipe for offline builds.

**Requirements & determinism.** A Rust toolchain, pinned by
[`benchmark/rust-toolchain.toml`](benchmark/rust-toolchain.toml) (rustup installs
it automatically), plus network on first build for the pinned Sui crates. The
small corroboration sample is **bundled** as `benchmark/sample.zip` (~7 MB:
1,889 framework `.mv` modules plus their decompiled `.move` sources), so
`corroborate.sh` needs **no** dataset download and extracts it fresh on each run.
The **full** dataset (`MystenLabs/sui-packages`) is fetched from its public
source on demand by `run.sh` and is **never stored in this repository**. The Sui
verifier revision, the toolchain, and the bundled sample are all pinned/fixed, so
results are bit-for-bit reproducible up to hardware-dependent timings (see
[`benchmark/README.md`](benchmark/README.md) → “What is shipped” for the sample's
size, selection, and provenance).

**Two ways to run** (from the `benchmark/` directory):

- *Deterministic small sample corroboration* (minutes, **no dataset download**) —
  extracts the bundled `sample.zip` (1,889 framework modules / ~15k functions)
  and reports the statistics:
  ```bash
  ./corroborate.sh
  ```
- *Full corpus* (the paper's exact setting) — needs the entire ~13–16 GB dataset
  and hours of compute; prompts to fetch the dataset and choose the corpus:
  ```bash
  ./run.sh
  ```

**What to expect.** The paper reports the regex checker is on average **2.2×**
slower with a mean of **≈30 µs/function** over 2.9M functions (Apple M1 Max). We
ran `corroborate.sh` on an Apple M2 over the ~15,000 framework functions and
observed a ratio of **≈2.0×** and **~18 µs/function** — the same direction and
order of magnitude (the subsample is framework-only and the hardware is not an
M1 Max, so the absolute microseconds are lower). This corroborates the Section 6
claim; the exact full corpus figures require `run.sh`. The tool also asserts that
the regex checker accepts *every* function the deployed checker accepts,
corroborating the backwards-compatibility / strictly-more-expressive claim.

## 9. Licence

Released under the Apache-2.0 licence ([`LICENSE`](LICENSE)), matching the
licence of mathlib, on which the development depends.
