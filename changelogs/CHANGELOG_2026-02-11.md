# Changes Made on 2026-02-11

## Extract generic list utility lemmas into ListUtils.lean

Created `LeanMove/Structures/ListUtils.lean` consolidating 13 generic list manipulation lemmas from across the project into one file.

### Structures/ListUtils.lean (new)
- `List.splits`, `List.splits_sound`, `List.splits_complete` — moved from Regex.lean
- `List.lookup_filter_of_lookup`, `List.lookup_filter_self_none`, `List.lookup_filter_mem_none`, `List.lookup_filter_ne`, `List.lookup_filter_notin` — moved from AlgorithmicTypingSoundness.lean
- `List.filterMap_all_none`, `List.eraseDups_length_le`, `List.filter_length_eq_implies`, `List.nodup_of_length_eraseDups`, `List.nodup_snd_pair_absurd` — moved from AlgorithmicTypingSoundness.lean (made non-private, added `List.` prefix)
- Uses `Classical.not_not` (core Lean 4) instead of `not_not` (Mathlib) to keep imports minimal

### Structures/Regex.lean
- Added `import LeanMove.Structures.ListUtils`
- Removed `List.splits`, `List.splits_sound`, `List.splits_complete` (now in ListUtils)

### AlgorithmicTypingSoundness.lean
- Removed 13 list lemmas (5 `List.lookup_filter_*`, `filterMap_all_none`, `eraseDups_length_le`, `filter_length_eq_implies`, `nodup_of_length_eraseDups`, `nodup_snd_pair_absurd`, `list_lookup_filter_ne`) — net reduction of ~300 lines
- Updated call sites to use `List.`-prefixed names from ListUtils

## Summary
1. Completed all accepted example proofs: added algorithmic check theorems and relational well-typedness proofs for the 4 remaining accepted examples.
2. Added algorithmic check-fails theorems for all 5 rejected examples (8 functions total).
3. Updated EXAMPLES-TODO.md to reflect current state.
4. Fixed lakefile for renamed file `mutable_borrows_are_not_unique_calls_invalid.lean`.

## Accepted Examples — Completed

### expressivity/accepted/imm_borrow_after_mut.lean
- Fixed local variable refids (`.refid 3` → `.refid 2` for `var_rimm` due to freeze ref collision)
- Added `direct_check`, `copy_and_freeze_check` theorems (`check_fun f lenv = true := by rfl`)
- Added `direct_welltyped`, `copy_and_freeze_welltyped` proofs via `check_fun_sound`
- Added supporting `VarEnv.RefsAreFresh` and `lenv_wf` lemmas

### expressivity/accepted/multible_mutable_return_values.lean
- Added imports for algorithmic checker
- Added `borrow_check`, `write_check` theorems
- Added `borrow_welltyped`, `write_welltyped` proofs via `check_fun_sound`
- Added supporting freshness and well-formedness lemmas

### expressivity/accepted/mutable_borrows_are_not_unique.lean
- Fixed all local variable refids to match algorithmic checker's `nextFreshRef` behavior
- Added `fields_check`, `fields_write_check` theorems
- Added `fields_welltyped`, `fields_write_welltyped` proofs via `check_fun_sound`
- Added supporting freshness and well-formedness lemmas

### expressivity/accepted/subtree_writes_release.lean
- Fixed local variable refids (`.varRef var_root` → `.refid N`)
- Constructed multi-block label environments for all 4 blocks (l0, l1, l2, l3)
- Built custom `t_l3_pathEnv` with forward and reverse derivative paths to handle `regexSubsumedBy` limitation
- Proved custom `PathEnv.WellFormed` for l3 environment (can't use `init_wellformed` with custom PathEnv)
- Added `t_check : check_fun t t_lenv = true := by rfl`
- Added `t_welltyped` proof via `check_fun_sound`

## Rejected Examples — Algorithmic Rejection Proven

Added algorithmic checker infrastructure to all 5 rejected example files:
- Imports for `TypeCheckingAlgorithmic` and `AlgorithmicTypingSoundness`
- Canonical label environments (`initEnv` + `lenv`)
- `#eval check_fun f lenv` debug output (all return `false`)
- Check-fails theorems (`check_fun f lenv = false := by native_decide`)

The `_illtyped` theorems (`¬ ∃ lenv, typecheck_fun f lenv`) remain as `sorry` pending the completeness theorem.

### expressivity/rejected/imm_borrow_after_mut_call_invalid.lean
- `invalid_check_fails : check_fun invalid invalid_lenv = false`

### expressivity/rejected/imm_borrow_after_mut_fields_invalid.lean
- `invalid_write_check_fails : check_fun invalid_write invalid_write_lenv = false`

### expressivity/rejected/mutable_borrows_are_not_unique_calls_invalid.lean
- `call_and_write_invalid_check_fails : check_fun call_and_write_invalid call_and_write_invalid_lenv = false`
- File renamed from `mutable_borrows_not_unique_calls_invalid.lean`

### expressivity/rejected/simple_dangling.lean
- 4 check-fails theorems for `field_dangling`, `nested_field_dangling`, `simple_call_dangling`, `field_call_dangling`

### initial/rejected/borrow_in_loop.lean
- `foo_check_fails : check_fun foo foo_lenv = false`
- Changed `varEnv` init to use `init_fun_varEnv foo` (consistent with other examples)

## Other Changes

### lakefile.lean
- Updated module name `mutable_borrows_not_unique_calls_invalid` → `mutable_borrows_are_not_unique_calls_invalid` in both `expressivity` and `examples` build targets

### EXAMPLES-TODO.md
- Updated to reflect all accepted examples complete (no sorrys)
- Updated rejected examples status (algorithmic rejection proven, relational proofs pending completeness)

## Make Type Checker Aref-Agnostic

Made the algorithmic and relational type checkers agnostic to the exact `.refid` values
in local variable type declarations. Previously, swapping e.g. `.refid 2` and `.refid 3`
in `locals` would cause `check_fun` to return `false`. Now, Aref comparisons in
`var_assign_invalid` and at block boundaries (`TypeEnv.equiv`/`subsumes`) use
kind-compatible matching (any `.refid n` is compatible with any `.refid m`).

### DecidableEquality.lean — New Aref/MoveType compatibility definitions
- Added `Aref.compatible` (Bool) / `Aref.Compatible` (Prop): kind-aware Aref comparison
- Added `MoveType.compatible` / `compatible_bool`: compare MoveTypes ignoring exact Aref values
- Bridge lemmas: `compatible_bool_sound`, `compatible_of_beq`

### Types.lean — VarEnv compatible comparison
- Added `VarEntryCompatible`: compatible comparison for `(IsValid × MoveType × Mut)` tuples
- Added `VarEnvLookupCompatible`: like `LookupEquiv` but uses `MoveType.compatible` for types
- Added `VarEnvLookupCompatible.refl` theorem
- Changed `TypeEnv.equiv` and `TypeEnv.subsumes` to use `VarEnvLookupCompatible` for varEnv

### TypeChecking.lean — Relational rule update
- `var_assign_invalid` now takes both τ (declared) and τ' (computed from siteEnv)
- Requires `MoveType.compatible τ τ'` instead of `τ = τ'`
- Stores τ' (computed type) in varEnv instead of τ (declared type)

### TypeCheckingAlgorithmic.lean — Algorithmic rule update
- Added `varentry_compatible_bool`, `varenv_entry_compatible_opt`, `varenv_lookup_compatible_bool`
- `var_assign_invalid` uses `MoveType.compatible_bool` instead of `==`
- Stores τ' (computed type) in varEnv
- `equiv_bool` and `subsumes_bool` use `varenv_lookup_compatible_bool` for varEnv

### AlgorithmicTypingSoundness.lean — Soundness proof update
- Added `Aref.Compatible_preserves_freshRef` and `MoveType.compatible_preserves_freshRef` bridge lemmas
- Added `varentry_compatible_bool_sound`, `varenv_entry_compatible_opt_sound`, `varenv_lookup_compatible_bool_sound`
- Updated `TypeEnv.equiv_refl`, `equiv_bool_implies_equiv`, `subsumes_bool_implies_subsumes`
- Updated `var_assign_invalid` soundness case to use compatible instead of equal types
- `equiv_implies_equiv_bool` (completeness direction) left as `sorry`

### Example files updated
- `borrow_in_loop_fixed_ok.lean`: `LookupEquiv.refl _` → `VarEnvLookupCompatible.refl _` (2 occurrences)
- `deref_borrow_field_ok.lean`: same (3 occurrences), added `· rfl` / `· exact MoveType.compatible_of_beq _ _ rfl` for new `compatible` premises in `var_assign_invalid`
- `alias_write_after_join.lean`: changed var_y refid to `.refid 42` to demonstrate agnosticism; freshness proofs use wildcards `⟨_, rfl⟩`
- `alias_writes.lean`: changed var_y refid to `.refid 52` in `borrow_local_and_copy_ref_reverse`; freshness proof uses wildcard
- `imm_borrow_after_mut_call_invalid.lean`: `native_decide` → `rfl`, commented out `sorry` theorem
- `mutable_borrows_are_not_unique_calls_invalid.lean`: `native_decide` → `rfl`
