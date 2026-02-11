# Changes Made on 2026-02-11

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
