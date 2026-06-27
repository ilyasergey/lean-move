# Artifact Evaluation Guide

**Paper #1171 — *Tracking Borrows with Regular Expressions* (OOPSLA 2026)**

This is the evaluation guide for the **LeanMove** artifact: the complete Lean 4
mechanisation of the regex-based Move borrow checker described in the paper —
the language, regular-expression library, small-step operational semantics, the
relational and algorithmic type systems, the machine-checked type-soundness
proof, the MoveIR parser/translator, and the conformance test suite.

Requested badges and their justification are in [`STATUS.md`](STATUS.md).
A prose overview of the metatheory is in [`metatheory.md`](metatheory.md).

This artifact is **plain source**: it requires only a standard Lean 4 toolchain
(no Docker or VM). Lean's build tool re-checks every proof with the kernel, so a
successful build *is* the verification.

---

## 1. Requirements

- **OS:** Linux (x86-64) or macOS (x86-64 or Apple Silicon). Windows via WSL2
  should also work.
- **Disk:** ≈ 8–10 GB (the mathlib build cache dominates).
- **RAM:** 8 GB minimum; 16 GB recommended — the two large proof files
  (`Preservation.lean`, `Weakening.lean`) are memory-intensive to elaborate.
- **Network:** needed *once*, to install the toolchain and download the
  prebuilt mathlib cache. No network is used at proof-checking time.
- **No special hardware**, no GPU, no telemetry, no network calls during the build.

**Pinned versions** (declared in `lean-toolchain` and `lakefile.lean`; the proof
depends only on these):

| Component | Version |
|-----------|---------|
| Lean 4    | `leanprover/lean4:v4.27.0` |
| mathlib4  | `v4.27.0` |
| batteries | `v4.27.0` |

`elan` reads `lean-toolchain` and selects the correct Lean version automatically.

---

## 2. Getting Started (kick-the-tires, ≈30 min)

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
grep -rnw --include='*.lean' -E 'sorry|admit' LeanMove | wc -l   # expect: 0
grep -rn  --include='*.lean' '^axiom '         LeanMove | wc -l   # expect: 0
```

If Steps 1–4 succeed you are set up correctly.

---

## 3. Full Evaluation (≈ up to 1 hour of mostly-unattended build)

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
| `lake build expressivity` | programs transpiled from the Move bytecode-verifier reference-safety suite |
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

**Step 3 — (optional) Re-confirm zero `sorry`/`admit`/`axiom`** as in §2 Step 4.

---

## 4. Significant claims and where to check them

Per the AE guidelines, here is the list of the paper's significant claims and
the artifact evidence for each. Names are fully qualified under namespace
`LeanMove.Typing.TypeSoundness` unless noted.

| # | Paper claim | Location in paper | Evidence in artifact |
|---|-------------|-------------------|----------------------|
| 1 | **Type soundness** (no preventable runtime error) | Thm 3.1, §3.4 | `type_soundness` — [`Typing/TypeSoundness.lean`](LeanMove/Typing/TypeSoundness.lean) (`type_soundness_no_danglingRef` specialises to dangling refs) |
| 2 | Soundness = **progress + preservation**; preservation is one lemma per typing rule | §3.4 | `preservation` — [`Typing/Soundness/Preservation.lean`](LeanMove/Typing/Soundness/Preservation.lean); progress in [`Progress.lean`](LeanMove/Typing/Soundness/Progress.lean) |
| 3 | **Weakening** (Lemma 3.2): `E₁ ⊒ E₂ ∧ ⊢ s` ⇒ `⊢ s` under `E₂` | Lemma 3.2, §3.4 | `typecheck_stmt_weaken` — [`Typing/Soundness/Weakening.lean`](LeanMove/Typing/Soundness/Weakening.lean) |
| 4 | **Regex path transfer** (Lemma 3.3) | Lemma 3.3, §3.4 | `HasType_transfer`, `readPath_HasType_transfer` — [`Typing/Soundness/Defs.lean`](LeanMove/Typing/Soundness/Defs.lean) |
| 5 | Algorithmic checker is **sound w.r.t. the relational spec** | §5.2 | `check_stmt_sound` — [`Typing/Algorithmic/AlgorithmicTypingSoundness.lean`](LeanMove/Typing/Algorithmic/AlgorithmicTypingSoundness.lean) |
| 6 | `WellTypedState` invariant has **29 clauses** (35 with enums) | §3.4, §4.2 | `structure WellTypedState` — [`Typing/Soundness/Defs.lean`](LeanMove/Typing/Soundness/Defs.lean) |
| 7 | `SoundnessAssumptions` bundles preconditions; collapsed into a **decidable** check | §5.2 | `SoundnessAssumptions`, `type_soundness_dec` — [`Defs.lean`](LeanMove/Typing/Soundness/Defs.lean), [`TypeSoundness.lean`](LeanMove/Typing/TypeSoundness.lean) |
| 8 | **Non-vacuity:** per-execution kernel-checked safety certificates | §5.2 | 31 `type_soundness_dec` instantiations — [`Tests/Runtime/AllTests.lean`](LeanMove/Tests/Runtime/AllTests.lean) |
| 9 | Regex ops (`δ`, emptiness, `⊆ {ε}`, disjointness) verified against language semantics | §3.2, §3.5 | [`Structures/Regex.lean`](LeanMove/Structures/Regex.lean) |
| 10 | Decidable, polynomial regex checks (no language-equivalence) | §3.5 | `Structures/Regex.lean`; algorithmic checker [`Algorithmic/AlgorithmicTypeChecking.lean`](LeanMove/Typing/Algorithmic/AlgorithmicTypeChecking.lean) |
| 11 | **Conformance** with the production checker on transpiled tests | §5.2 | accepted/rejected suites under [`Tests/Typechecking/`](LeanMove/Tests/Typechecking/) (33 expressivity + 14 litmus), built by `lake build examples` |
| 12 | **Parser/translator** correctness via alpha-equivalence | §5.2 | 35 tests under [`Tests/Parsing/`](LeanMove/Tests/Parsing/), `.mvir` sources under [`Tests/MVIR/`](LeanMove/Tests/MVIR/), `lake build parsing` |
| 13 | **Vector** extension, zero new sorrys | §4.1 | rules in [`Typing/TypeChecking.lean`](LeanMove/Typing/TypeChecking.lean); `vec_*` tests; `.vecElem` path element |
| 14 | **Enum** extension via flat encoding; +6 invariant clauses | §4.2 | enum rules + flat encoding in [`Semantics/Smallstep.lean`](LeanMove/Semantics/Smallstep.lean); `enum_*` tests |
| 15 | Whole development is `sorry`/`axiom`-free | §5.1 | §2 Step 4 and §3 Step 2 above |
| 16 | LOC / commit-timeline figures (Table 1, Fig 17) | §5.1 | reproducible from the repo — see §7 |

> **Not in this artifact:** the Section 6 performance results (≈2.2×, ≈30 µs,
> 2.9M functions) are from the separate **Rust** implementation in the Sui
> client and are out of scope here (see [`STATUS.md`](STATUS.md)).

---

## 5. Paper-to-artifact correspondence (definitions and figures)

| Paper | Artifact |
|-------|----------|
| MoveLight syntax (Fig. 8) | `Expr`, `Stmt`, `MoveType`, `Aref` in [`Lang/MoveLight.lean`](LeanMove/Lang/MoveLight.lean) |
| Typing rules (Figs. 9, 10) | `typecheck_stmt` (relational) in [`Typing/TypeChecking.lean`](LeanMove/Typing/TypeChecking.lean) |
| Algorithmic checker | `check_stmt` in [`Typing/Algorithmic/AlgorithmicTypeChecking.lean`](LeanMove/Typing/Algorithmic/AlgorithmicTypeChecking.lean) |
| Path environment Π, `extend`, node removal, transitive closure | [`Structures/PathMap.lean`](LeanMove/Structures/PathMap.lean) |
| `check_outbound`, derivative `δ`, emptiness, `⊆ {ε}` | [`Structures/Regex.lean`](LeanMove/Structures/Regex.lean) |
| Small-step semantics (Fig. 11), runtime errors (Fig. 12) | [`Semantics/Smallstep.lean`](LeanMove/Semantics/Smallstep.lean) |
| Vector rules (Fig. 14), enum rules (Fig. 16) | [`Typing/TypeChecking.lean`](LeanMove/Typing/TypeChecking.lean) |

See [`metatheory.md`](metatheory.md) for the full prose walkthrough, the
project layout, and the limitations.

---

## 6. Trusted computing base, axioms, and assumptions

- **TCB:** the Lean 4 kernel (v4.27.0) plus the three standard classical axioms
  `propext`, `Classical.choice`, `Quot.sound` inherited from mathlib. §3 Step 2
  shows how to confirm the soundness theorem depends on exactly these and on no
  `sorryAx`.
- **No project-specific axioms, no `sorry`, no `admit`** anywhere in the
  development.
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
translation-validation architecture: it *checks* given environments, so an
inference bug can only reject valid programs, never accept unsafe ones).

---

## 7. Reusability and reproducing the quantitative figures

**Extending the development.** The vector (§4.1) and enum (§4.2) extensions are
worked examples of the standard recipe: add a path element / type-compatibility
case, then thread it uniformly through the lemmas. Start from
[`CLAUDE.md`](CLAUDE.md) (architecture + conventions + Lean-4 pitfalls) and
[`metatheory.md`](metatheory.md), then read the relevant `Soundness/` file.
[`PROMPTS.md`](PROMPTS.md) records how the development was driven, phase by
phase, anchored to commits.

**Reproducing Table 1 (LOC) and the test counts** from the repository:

```bash
# non-blank lines per major component (approximation of Table 1)
find LeanMove -name '*.lean' | xargs wc -l | sort -rn | head
# test-suite sizes
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

## 8. Licence

Released under the Apache-2.0 licence ([`LICENSE`](LICENSE)), matching the
licence of mathlib, on which the development depends.
