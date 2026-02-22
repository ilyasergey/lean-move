# Changes Made on 2026-02-12

## New: Small-step operational semantics and runtime tests

### LeanMove/Semantics/Smallstep.lean (new, ~430 lines)
Executable small-step interpreter for MoveLight programs.

- **Runtime values:** `Value` — `int`, `bool`, `unit`, `record` (nested), `ref` (heap location + field path)
- **Global heap:** `Heap` with `alloc`, `read`, `write`, `readRef`, `writeRef`; nested field navigation via `readPath`/`writePath`
- **Call stack:** `Frame` (varStore, siteStore, current stmt, blocks, funEnv, returnInfo) + `Machine` (frame, stack, heap)
- **Error model:** `RuntimeError` — uninitialized var/site, type mismatch, unknown function/label, dangling ref, etc.
- **`step : ExecState → ExecState`** — handles all 16 Stmt/Expr cases (CPS-style continuations)
- **`run : Nat → ExecState → ExecState`** — fuel-bounded driver
- **`initState`** — creates initial execution state from FunDef, funEnv, args, and optional heap
- **Design:** `release` is no-op at runtime; `freeze` copies ref value; borrow tracking is purely static/type-level

### LeanMove/Semantics.lean (new)
Aggregator: `import LeanMove.Semantics.Smallstep`

### LeanMove/Tests/Runtime/AllTests.lean (new)
Runtime tests for all example programs using `#guard` (accepted) and `#eval` (rejected).

**Accepted programs (21 `#guard` tests):** All 10 accepted programs execute correctly:
- `borrow_in_loop_fixed_ok`: infinite loop exhausts fuel (`isError`)
- `deref_borrow_field_ok`: inter-procedural calls (M.new returns `{f: 2}`, foo halts)
- `alias_writes`, `alias_write_after_join`, `extension_after_call`, `extension_writes_after_join`,
  `imm_borrow_after_mut`, `multible_mutable_return_values`, `mutable_borrows_are_not_unique`,
  `subtree_writes_release`: all halt successfully

**Rejected programs (8 `#eval` tests):** All rejected programs succeed at runtime — borrow-checking
violations (dangling refs, conflicting borrows) are purely static; the interpreter does not enforce them.

### Modified files
- **LeanMove.lean** — added `import LeanMove.Semantics`
- **lakefile.lean** — added `runtime` build target

## New: Runtime safety litmus tests

### LeanMove/Tests/Typechecking/litmus/rejected/ (5 new files)
Programs that are rejected by the type checker AND fail at runtime with specific errors.
Each test asserts the exact `RuntimeError` variant via `#guard match`.

| File | Runtime error | What it demonstrates |
|------|--------------|---------------------|
| `use_after_move.lean` | `uninitializedVar` | Move consumes variable; subsequent copy fails |
| `uninitialized_var.lean` | `uninitializedVar` | Reading local before assignment |
| `deref_non_ref.lean` | `typeMismatch "readRef on non-ref"` | Dereferencing an integer |
| `unpack_non_record.lean` | `typeMismatch "unpack on non-record"` | Unpacking an integer |
| `borrow_field_non_ref.lean` | `typeMismatch "borrowField on non-ref"` | Borrowing field from record value (not ref) |

## New: Genuine dangling pointer example

### LeanMove/Tests/Typechecking/litmus/rejected/dangling_ref.lean (new)
A program that creates a genuine dangling pointer at runtime — unlike the `simple_dangling`
examples where overwrites preserve field structure, this one replaces `S{f:42}` with `T{g:0}`
(different fields), so the field reference `f_ref` with path `[field "f"]` becomes invalid.

- **Type checker rejects** via `check_outbound_bool`: `f_ref` borrows from `r`, blocking `writeRef`
- **Runtime produces `danglingRef` error**: `readPath` on `{g:0}` can't find field `"f"`
- Runtime test in AllTests.lean asserts specifically `danglingRef` (not just any error)

## Rename: `initial` → `litmus` in Tests/Typechecking

Renamed `LeanMove/Tests/Typechecking/initial/` to `LeanMove/Tests/Typechecking/litmus/`.
Updated lakefile build targets (`initial` → `litmus`), AllTests.lean imports, and changelog references.

## Change: Use `#guard` for failing type-checking tests

Converted standalone `_check_fails` theorems in rejected examples from `theorem ... := by rfl`
(or `by native_decide`) to idiomatic `#guard !check_fun ...` tests. These theorems are not
referenced by downstream proofs, so the conversion is safe.

**Files changed (6):**
- `litmus/rejected/borrow_in_loop.lean`
- `expressivity/rejected/imm_borrow_after_mut_call_invalid.lean`
- `expressivity/rejected/imm_borrow_after_mut_fields_invalid.lean`
- `expressivity/rejected/simple_dangling.lean` (4 tests)
- `expressivity/rejected/mutable_borrows_are_not_unique_calls_invalid.lean`

## Refactor: Move regex definitions and lemmas to Regex.lean

Moved all regex-related definitions and soundness lemmas from the algorithmic
checker files into `Regex.lean`, consolidating them with the existing regex
infrastructure. All call sites resolve via `open Regex`.

### Regex.lean — New definitions and theorems
- `regexBeq` — boolean structural equality for `Regex α` (moved from `TypeCheckingAlgorithmic.lean`)
- `regexSubsumedBy` — conservative language inclusion check (moved from `TypeCheckingAlgorithmic.lean`)
- `regexBeq_refl` — reflexivity of `regexBeq` (moved from `AlgorithmicTypingSoundness.lean`)
- `regexBeq_eq` — soundness: `regexBeq r1 r2 = true → r1 = r2` (moved from `AlgorithmicTypingSoundness.lean`)
- `eq_regexBeq` — completeness: `r1 = r2 → regexBeq r1 r2 = true` (moved from `AlgorithmicTypingSoundness.lean`)
- `is_empty_sound` — `is_empty r = true → ∀ s, ¬ interpret_regex r s` (moved from `AlgorithmicTypingSoundness.lean`)
- `regexSubsumedBy_sound` — `regexSubsumedBy r1 r2 = true → L(r1) ⊆ L(r2)` (moved from `AlgorithmicTypingSoundness.lean`)

### TypeCheckingAlgorithmic.lean
- Removed `regexBeq` and `regexSubsumedBy` definitions (now in `Regex.lean`)

### AlgorithmicTypingSoundness.lean
- Removed `regexBeq_refl`, `regexBeq_eq`, `eq_regexBeq` lemmas (now in `Regex.lean`)
- Removed `is_empty_sound`, `regexSubsumedBy_sound` theorems (now in `Regex.lean`)

### Checker.lean
- Removed dead import of deleted `AlgorithmicTypingCompleteness`

## Refactor: Extract generic type/environment lemmas into TypesUtils.lean

Extracted ~590 lines of generic type and environment invariant definitions and
preservation lemmas from `AlgorithmicTypingSoundness.lean` into a new
`LeanMove/Checker/TypesUtils.lean`. These lemmas depend only on `Types.lean` and
`TypeChecking.lean` (not on the algorithmic checker), making them available for
future semantic type soundness proofs.

### TypesUtils.lean (new)
Import: `import LeanMove.Checker.TypeChecking`

**freshRef / nextFreshRef properties:**
- `freshRef_iff_freshRefBool`, `nextFreshRef_fresh`, `freshRefBool_implies_freshRef`, `nextFreshRef_fresh_prop`
- `nextFreshRef_not_root`, `nextFreshRef_is_refid`, `nextFreshRef_not_varRef`

**PathEnv definitions and preservation:**
- `delete_ref_node_refs`, `delete_ref_node_paths_involving_r`, `delete_ref_node_paths_not_involving_r`
- `isBorrowPath` (def), `PathEnv.WellFormed` (structure), `PathEnv.init_wellformed`
- `delete_ref_node_wellformed`

**SiteEnv.RefsNotRoot + preservation:**
- `SiteEnv.RefsNotRoot` (def), `empty_refs_not_root`, `insert_refs_not_root`
- `delete_refs_not_root`, `deleteAll_refs_not_root`, `addFieldSites_refs_not_root`

**VarEnv.RefsNotRoot / RefsAreFresh + preservation:**
- `VarEnv.RefsNotRoot`, `VarEnv.RefsAreFresh` definitions
- Insert/update/lookup preservation lemmas for both invariants
- `moveTypeRefsNotRoot`, `moveTypeIsFreshRef`, `Aref.isFreshRef` definitions
- `Aref.Compatible_preserves_freshRef`, `MoveType.compatible_preserves_freshRef`

**TypeEnv.WellFormed + operation preservation:**
- `TypeEnv.WellFormed` (structure), `init_wellformed`
- Preservation for: `insert_siteEnv`, `delete_siteEnv`, `deleteAll_siteEnv`, `update_varEnv`, `insert_update`, `insert_pathEnv`, `delete_insert_pathEnv`, `delete_delete_insert`, `deleteAll_insert`
- `update_with_extension_wellformed`, `update_with_epsilon_wellformed`
- `garbage_collect_wellformed`, `consume_ref_transfer_wellformed`
- `TypeEnv.equiv_refl`

**Standalone generic lemmas:**
- `varRef_fresh_when_not_borrowed` — uses relational `not_borrowed`, pure env property
- `call_connect_inputs_outputs_wf` — uses relational `call_connect_inputs_outputs`

### AlgorithmicTypingSoundness.lean
- Added `import LeanMove.Checker.TypesUtils`
- Removed ~800 lines of generic definitions and lemmas (now in TypesUtils.lean)
- Reduced from ~1900 to ~1097 lines
- Remaining: all `*_bool_sound/complete` bridge lemmas, private helpers, core soundness theorems (`check_letBind_sound`, `check_stmt_sound`, `check_fun_sound`)

## New: Type soundness proof scaffold and regex infrastructure

### LeanMove/Typing/TypeSoundness.lean (new, ~265 lines)
Scaffold for proving that well-typed MoveLight functions never produce
`danglingRef` errors at runtime. Contains core definitions and theorem
statements with `sorry` proof bodies.

**Core definitions:**
- `HasType` — shape-compatibility between runtime `Value` and static `BasicMoveType`
- `RefMap` — bridge between abstract `Aref` and concrete `(Loc × List Field)` pairs
- `ValueMatchesType` — relates runtime values to `MoveType` via `RefMap`
- `PathReflectedInHeap` — connects PathEnv paths to concrete heap field structure
- `WellTypedState` — central invariant relating `Machine` to `TypeEnv`:
  env well-formed, stmt typed, variable/site consistency, rmap liveness, path coherence

**Proven lemmas:**
- `readPath_append` — readPath distributes over path concatenation
- `readPath_prefix_succeeds` — longer path success implies prefix success
- `check_outbound_only_empty` — `check_outbound` with `only_matches_empty ∘ simplify`
  implies all outbound paths match only `[]` (uses new regex lemmas)

**Theorem statements (with `sorry`):**
- `heap_write_preserves_read` — writes at different locations don't interfere
- `heap_writeRef_preserves_readRef_diff_loc` — writeRef at different locs preserves readRef
- `no_danglingRef_progress` — well-typed state never produces danglingRef
- `preservation` — each step preserves WellTypedState
- `type_soundness` — main theorem: `typecheck_fun f lenv → ∀ n loc, run n ... ≠ .error (.danglingRef loc)`

### LeanMove/Structures/Regex.lean — New soundness lemmas (~250 lines added)
- `DerivFree` — predicate: regex has no `.deriv` constructors
- `nullable_sound` — `nullable r = true → interpret_regex r []`
- `nullable_complete` — `DerivFree r → interpret_regex r [] → nullable r = true`
- `simplify_deriv_free` — `simplify` always produces deriv-free regexes
- `brzozowski_step_sound` — `DerivFree r → (⟦brzozowski_step a r⟧ s ↔ ⟦r⟧ (a :: s))`
- `simplify_preserves_semantics` — `⟦simplify r⟧ s ↔ ⟦r⟧ s`
- `only_matches_empty_sound` — `only_matches_empty r = true → ⟦r⟧ s → s = []`

### Modified files
- **LeanMove/Typing.lean** — added `import LeanMove.Typing.TypeSoundness`

## Rename: `LeanMove/Checker` → `LeanMove/Typing`

Renamed the `Checker` directory and namespace to `Typing` throughout the project.

### Files moved
- `LeanMove/Checker.lean` → `LeanMove/Typing.lean`
- `LeanMove/Checker/` → `LeanMove/Typing/` (5 files including `Algorithmic/` subfolder)

### Namespace/import updates (22 files)
- All `import LeanMove.Checker.*` → `import LeanMove.Typing.*`
- All `namespace LeanMove.Checker` → `namespace LeanMove.Typing`
- All `end LeanMove.Checker` → `end LeanMove.Typing`
- All `open LeanMove.Checker` → `open LeanMove.Typing`
- Affected: root `LeanMove.lean`, aggregator `Typing.lean`, 5 source files in `Typing/`, 15 example files
