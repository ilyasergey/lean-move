# Changes Made on 2026-02-10

## Summary
1. Proved the `writeRef` and `call` cases of `check_stmt_sound`, closing all remaining sorrys in `AlgorithmicTypingSoundness.lean`.
2. Moved algorithmic checker files to `LeanMove/Checker/Algorithmic/` subfolder.
3. Removed obsolete `TypeCheckingMisc.lean`.

## Changes

### LeanMove/Checker/Types.lean
- Restricted `check_outbound` to quantify only over tracked refs (`s' ∈ penv.refs`) instead of all possible refs. This is needed for the `writeRef` soundness proof since `only_matches_empty` on unreduced `.deriv` constructors from non-tracked refs would be unsound.

### LeanMove/Checker/TypeChecking.lean
- Changed `write_ref` relational rule to use `simplify` before `only_matches_empty`, matching the algorithmic checker's behavior: `check_outbound env.pathEnv r (λ re ↦ only_matches_empty (simplify re))`

### LeanMove/Checker/Algorithmic/AlgorithmicTypingSoundness.lean (was LeanMove/Checker/AlgorithmicTypingSoundness.lean)

**Proved `writeRef` case** (~40 lines):
- Uses `check_outbound_bool_implies_check_outbound` to bridge Bool→Prop
- Constructs WellFormed for the transformed env via `garbage_collect_wellformed`, `SiteEnv.delete_refs_not_root`

**Proved `call` case** (~25 lines):
- Splits on `all_fresh_sites_bool`, cases on `lookup env.funEnv fnName`, splits on the 4-way `&&` condition
- Uses bridge lemmas to convert each Bool check to its Prop counterpart
- Uses `call_connect_inputs_outputs_wf` for WellFormed preservation

**New bridge lemmas:**
- `check_mutable_inputs_isolated_bool_sound` — Bool isolation check → relational `check_mutable_inputs_isolated`
- `check_mutable_inputs_have_outbound_bool_sound` — Bool outbound check → relational `check_mutable_inputs_have_outbound`
- `filterMap_all_none` — when `∀ a ∈ as, f a = none`, then `as.filterMap f = []`
- `call_connect_inputs_outputs_wf` — `call_connect_inputs_outputs` preserves `TypeEnv.WellFormed` when all output sites are fresh (key insight: `io=[]` and `mo=[]` make the three foldl operations identity)

### LeanMove/Structures/AssocMap.lean
- Added `notIn_implies_lookup_none` theorem: bridges `notIn m k = true → lookup m k = none` (needed by `call_connect_inputs_outputs_wf`)

### Refactoring: moved algorithmic files to Algorithmic/ subfolder

Moved:
- `TypeCheckingAlgorithmic.lean` → `Algorithmic/TypeCheckingAlgorithmic.lean`
- `AlgorithmicTypingSoundness.lean` → `Algorithmic/AlgorithmicTypingSoundness.lean`
- `AlgorithmicTypingCompleteness.lean` → `Algorithmic/AlgorithmicTypingCompleteness.lean`

Updated imports in:
- `LeanMove/Checker.lean`
- 6 example files (`alias_writes`, `extension_after_call`, `alias_write_after_join`, `imm_borrow_after_mut`, `deref_borrow_field_ok`, `borrow_in_loop_fixed_ok`)

### Removed
- `LeanMove/Checker/Old/TypeCheckingMisc.lean` — obsolete file

## Technical Notes

### `rw [filterMap_all_none as _ ...]` pattern for lambda matching
When `simp only [hio, hmo]` can't match filterMap lambda expressions (due to alpha-equivalence issues with bound variable names after `unfold`), use `rw [filterMap_all_none as _ (fun a ha => by simp [hlookup_none a ha])]` with `_` for `f`. This lets Lean's unifier match the exact lambda from the goal, avoiding the need to write alpha-equivalent lambdas manually.
