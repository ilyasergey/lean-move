# Changes Made on 2026-01-21

## Summary
Added expressivity examples transpiled from Move bytecode verifier tests.

## Overview

This change adds 12 examples from the Move bytecode verifier transactional tests
(reference_safety/expressivity) transpiled to MoveLight. These examples demonstrate
various borrow checking scenarios that should either pass or fail type checking.

Source: https://github.com/tnowacki/sui/tree/example-tests/external-crates/move/crates/bytecode-verifier-transactional-tests/tests/reference_safety/expressivity

## New Files

### Accepted Examples (pass type checking)
Located in `LeanMove/Examples/expressivity/accepted/`:

1. **alias_write_after_join.lean** - Writing through aliased mutable references after control flow joins
2. **alias_writes.lean** - Four modules showing aliased writes in different orders
3. **extension_after_call.lean** - Borrowing and writing to nested struct fields
4. **extension_writes_after_join.lean** - Writing to extensions after control flow joins
5. **imm_borrow_after_mut.lean** - Immutable references coexisting with mutable references
6. **multible_mutable_return_values.lean** - Functions returning multiple mutable references
7. **mutable_borrows_are_not_unique.lean** - Multiple mutable borrows to nested fields
8. **subtree_writes_release.lean** - Writes safe due to lossy reference graph

### Rejected Examples (fail type checking)
Located in `LeanMove/Examples/expressivity/rejected/`:

1. **simple_dangling.lean** - Various ways to create dangling references (WRITEREF_EXISTS_BORROW_ERROR)
2. **imm_borrow_after_mut_call_invalid.lean** - Cannot write when immutable alias exists
3. **imm_borrow_after_mut_fields_invalid.lean** - Cannot write through mutable when immutable field ref exists
4. **mutable_borrows_not_unique_calls_invalid.lean** - Unknown relationship between overlapping refs

## Changes to Existing Files

### LeanMove/Examples/Macros.lean
Added new macros for more readable MoveLight code:
- `branch cond "l1" "l2"` - Conditional branch
- `* a ::= b` - Write through reference
- `ret [sites]` - Return statement
- `release s` - Release reference
- `letsite a ← *b` - Dereference (read reference)
- `letsite a ← freeze b` - Freeze reference

### lakefile.lean
Added `expressivity` build target to compile all expressivity examples:
```bash
lake build expressivity
```

### README.md
Updated with:
- Correct dependency versions
- Build instructions for expressivity examples
- Link to source examples

## Theorems

Each accepted example includes a well-typedness theorem with `sorry`:
```lean
theorem t_welltyped : ∃ lenv, typecheck_fun t lenv := by
  sorry
```

Each rejected example includes an ill-typedness theorem with `sorry`:
```lean
theorem t_illtyped : ¬ (∃ lenv, typecheck_fun t lenv) := by
  sorry
```

## Notes

- All examples include links to the original .mvir source files
- The transpilation preserves the essential borrow checking semantics
- Some simplifications were made where MoveLight doesn't support certain features
  (e.g., vectors, tuple return types)
- Proofs are left as `sorry` for future work
