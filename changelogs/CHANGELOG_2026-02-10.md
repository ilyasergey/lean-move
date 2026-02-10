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

## Order-independent VarEnv/SiteEnv comparison

### Problem
The algorithmic checker compared VarEnv and SiteEnv using structural list equality (`==`/`=`). Since `AssocMap` stores entries as `List (K × V)` and `update`/`insert` prepend entries, the order depends on operation order. When two branches perform moves in different orders (e.g., `extension_writes_after_join.lean`: l1 does `move a; move b` vs l2 does `move b; move a`), the resulting VarEnvs are semantically identical but structurally different, causing the subsumption check at join points to fail.

### Fix
Replaced structural equality with lookup-based equivalence for VarEnv and SiteEnv.

### LeanMove/Structures/AssocMap.lean
- Added `LookupEquiv` (Prop): `∀ k, lookup m1 k = lookup m2 k`
- Added `lookup_equiv_bool` (Bool): checks all keys from both maps via `decide`
- Added `lookup_none_of_not_mem_keys` helper lemma
- Added bridge lemmas: `lookup_equiv_bool_sound` and `lookup_equiv_bool_complete`
- Added `LookupEquiv.refl` convenience lemma

### LeanMove/Checker/Types.lean
- `TypeEnv.equiv`: changed `env1.siteEnv = env2.siteEnv` and `env1.varEnv = env2.varEnv` to use `LookupEquiv`
- `TypeEnv.subsumes`: same changes

### LeanMove/Checker/Algorithmic/TypeCheckingAlgorithmic.lean
- `TypeEnv.equiv_bool`: replaced `==` with `lookup_equiv_bool` for siteEnv and varEnv
- `TypeEnv.subsumes_bool`: same changes

### LeanMove/Checker/Algorithmic/AlgorithmicTypingSoundness.lean
- Updated `equiv_refl`, `equiv_bool_implies_equiv`, `equiv_implies_equiv_bool`, `subsumes_bool_implies_subsumes` to use `LookupEquiv` bridge lemmas

### LeanMove/Examples/expressivity/accepted/extension_writes_after_join.lean
- Added algorithmic type checking environments and label environment for all 4 blocks
- Proved `t_check : check_fun t t_lenv = true := by rfl` (all blocks pass including l2)
- Proved `t_welltyped` via `check_fun_sound` (no sorry)
- Proved `t_lenv_wf` and supporting freshness lemmas

### LeanMove/Examples/initial/accepted/deref_borrow_field_ok.lean
- Updated 3 `TypeEnv.equiv` proofs: replaced `rfl` with `LookupEquiv.refl _` for siteEnv/varEnv

### LeanMove/Examples/initial/accepted/borrow_in_loop_fixed_ok.lean
- Updated `TypeEnv.equiv` and `TypeEnv.subsumes` proofs: replaced `rfl` with `LookupEquiv.refl _`

## Technical Notes

### `rw [filterMap_all_none as _ ...]` pattern for lambda matching
When `simp only [hio, hmo]` can't match filterMap lambda expressions (due to alpha-equivalence issues with bound variable names after `unfold`), use `rw [filterMap_all_none as _ (fun a ha => by simp [hlookup_none a ha])]` with `_` for `f`. This lets Lean's unifier match the exact lambda from the goal, avoiding the need to write alpha-equivalent lambdas manually.
