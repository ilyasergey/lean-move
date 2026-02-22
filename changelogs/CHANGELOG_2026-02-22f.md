# Changelog — 2026-02-22f

## Extend type soundness to rule out all preventable runtime errors

### Summary

Strengthened the type soundness theorem from ruling out 1 error type
(`danglingRef`) to ruling out **8 of 11** runtime error constructors.
Only 3 "acceptable" errors remain: `divisionByZero` (runtime arithmetic),
`outOfFuel` (bounded interpreter), and `aborted` (well-typed `abort`).

### Motivation

The original `type_soundness` theorem only proved absence of `danglingRef`
errors, yet the type system actually prevents many more runtime failures.
This change closes the gap between what the type system guarantees and what
the theorem states.

### Approach

**Three prerequisite fixes** to the operational semantics:

1. **`aborted` error constructor** (`Smallstep.lean`): Added a new
   `RuntimeError.aborted` to separate intentional termination (`abort`
   statement, `skip` in callee) from type errors. Previously both produced
   `typeMismatch`, making it impossible to rule out all `typeMismatch`
   errors.

2. **Boolean binop evaluation** (`Smallstep.lean`): Added `evalBinopBool`
   for `eq` and `nand` on booleans. The type system allows these
   combinations (`binop_type`), but the step function previously only
   handled integer operands, causing a spurious `typeMismatch`.

3. **`RuntimeError.isAcceptable`** (`Smallstep.lean`): Predicate marking
   `divisionByZero`, `outOfFuel`, `aborted` as acceptable. Enumerating
   acceptable (not unacceptable) errors ensures new constructors are
   ruled out by default.

**New WellTypedState invariants** (`Defs.lean`, 23→25 fields):

4. **`lenv_labels_in_blocks`**: Every label in the label environment has a
   corresponding block in the current frame. Rules out `unknownLabel`.

5. **`has_return_info`**: Non-top-level frames always have return info.
   Rules out one `typeMismatch` site in `ret` handling.

**Progress theorem** (`Progress.lean`, ~650 new lines):

6. **`step_error_is_acceptable`**: If a well-typed state steps to an
   error, that error is acceptable. Proves impossibility of all 8
   preventable errors via helper lemmas:
   - `danglingRef`: `rmap_live` (references → valid heap locations)
   - `uninitializedVar`: `var_consistent` (valid vars have values)
   - `uninitializedSite`: `site_consistent` (typed sites have values)
   - `unknownLabel`: `lenv_labels_in_blocks` (labels → blocks)
   - `unknownFunction`: `funEnv_typed` + `FunTypeSafe`
   - `arityMismatch`: `types_conform` length chains
   - `typeMismatch`: type-directed value matching (bool→`.bool`,
     ref→`.ref`, record→`.record`)
   - `invalidFieldAccess`: not produced by step (0 sites)

**SafeExecState restructuring** (`SafeExec.lean`):

7. Changed from `| .error (.danglingRef _) => False | .error _ => True`
   to `| .error e => e.isAcceptable`. Updated `safe_step` to use
   `step_error_is_acceptable`. Added `safe_run_no_unacceptable_error`
   (general) alongside existing `safe_run_no_danglingRef` (corollary).

**Strengthened theorems** (`TypeSoundness.lean`):

8. `type_soundness` / `type_soundness_dec`: now take
   `(e : RuntimeError) (hna : ¬e.isAcceptable)` and conclude
   `∀ n, run n ... ≠ .error e`.
9. `type_soundness_no_danglingRef` / `type_soundness_dec_no_danglingRef`:
   backward-compatible corollaries preserving the old API.

### Key changes

#### Semantics/Smallstep.lean (~30 lines)
- Added `RuntimeError.aborted` constructor
- Added `RuntimeError.isAcceptable` predicate
- Added `evalBinopBool` for boolean `eq`/`nand`
- Changed `abort` and `skip`-in-callee to produce `.aborted`
- Extended binop case to handle `(.bool, .bool)` operands

#### Typing/Soundness/Defs.lean (~15 lines)
- Added `lenv_labels_in_blocks` (field 24) and `has_return_info` (field 25) to `WellTypedState`
- Added corresponding conjuncts to `FunTypeSafe` and `StackSafe`

#### Typing/Soundness/Progress.lean (~650 lines)
- 18 helper lemmas: `findBlock_some_of_mem`, `readVar_some_of_validVar`,
  `getVarLoc_some_of_validVar`, `readSite_some_of_typed`,
  `HasType_tbool_is_bool`, `HasType_u64_is_int`, `HasType_trecord_is_record`,
  `ValueMatchesType_ref_is_ref`, `ValueMatchesType_basic_is_hasType`,
  `typecheck_fun_blocks_ne_nil`, `evalBinopBool_some_of_binop_type_tbool`,
  `collectSiteValues_some`, `collectSiteValues_length`, `collectPackFields_some`,
  `types_conform_sites_typed`, `types_conform_length`, `bindReturnValues_some`,
  `allocArgs_some`, `collectSiteValues_some_of_typed`
- Main theorem: `step_error_is_acceptable`

#### Typing/Soundness/SafeExec.lean (~70 lines changed)
- Restructured `SafeExecState` to use `isAcceptable`
- Added `SafeExecState.not_error`, `safe_run_no_unacceptable_error`
- Kept backward-compatible `not_danglingRef`, `safe_run_no_danglingRef`

#### Typing/Soundness/InitState.lean (~110 lines)
- Added `lenv_labels_in_blocks` and `args_length` to `SoundnessAssumptions`
- Added corresponding boolean checks to `checkDecidable`
- Added `allocArgs_some_of_length_eq` helper lemma
- Updated `initState_safe` for new error impossibility proofs

#### Typing/Soundness/Preservation.lean (~105 lines)
- Threaded `lenv_labels_in_blocks` and `has_return_info` through all
  preservation cases (direct transfer for most; special handling for
  call/ret)

#### Typing/Soundness/StackSafeUtils.lean (~12 lines)
- Threaded new `StackSafe` conjuncts through utility lemmas

#### Typing/Algorithmic/DecidableTypeEnv.lean (~2 lines)
- Added `lenv_labels_in_blocks` check to `checkFunEnv` (12th check)
- Added corresponding peel step in `checkFunEnv_sound`

#### Typing/TypeSoundness.lean (rewritten)
- General `type_soundness` / `type_soundness_dec` ruling out all
  non-acceptable errors
- Backward-compatible `_no_danglingRef` corollaries

#### Tests/Runtime/AllTests.lean (~54 lines changed)
- Updated all 27 `type_soundness_dec` calls to `type_soundness_dec_no_danglingRef`

#### metatheory.md (~117 lines changed)
- Updated TL;DR, error classification table, theorem statements,
  proof architecture, WellTypedState fields, test descriptions

### Result

`lake build` succeeds (349 jobs). All existing tests pass. The type
soundness theorem now rules out 8 of 11 runtime error constructors,
matching the full power of the MoveLight type system.
