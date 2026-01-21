# Changes Made on 2026-01-21

## Summary
Refactored control flow into Terminator type; added build targets for all examples.

## Overview

This change introduces a major refactoring to separate control flow (jump, branch, ret, abort)
from regular statements into a dedicated `Terminator` type. This ensures that control flow
only appears at the end of blocks, matching the structure of real intermediate representations.

Additionally, the Macros module was moved from Examples to Lang, and build targets were added
for all example categories.

## Major Changes

### Control Flow Refactoring

**LeanMove/Lang/MoveLight.lean**:
- Added new `Terminator` inductive type with constructors: `jump`, `branch`, `ret`, `abort`
- Updated `Block` structure to have three fields: `label`, `body` (Stmt), `terminator` (Terminator)

**LeanMove/Checker/TypeChecking.lean**:
- Removed `abort`, `jump`, `branch` rules from `typecheck_stmt`
- Added new `typecheck_terminator` inductive relation for control flow checking
- Updated `typecheck_block` to check body via `typecheck_stmt`, then terminator via `typecheck_terminator`
- Simplified `typecheck_fun`: removed fall-through logic between blocks

### Module Reorganization

**LeanMove/Lang/Macros.lean** (moved from LeanMove/Examples/Macros.lean):
- Updated macros for new Terminator type (`jump`, `branch`, `ret`, `abort`)
- All example files updated to import from new location

### Build Targets

**lakefile.lean**:
- Added `lake build initial` for initial examples
- Added `lake build examples` for all examples (initial + expressivity)

**README.md**:
- Updated with all build target instructions

### Proof Completions

**LeanMove/Examples/initial/accepted/**:
- `borrow_in_loop_fixed_ok.lean`: Complete proof with no `sorry`
- `deref_borrow_field_ok.lean`: Complete proof with no `sorry`

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

### LeanMove/Lang/Macros.lean (moved from LeanMove/Examples/Macros.lean)
Macros for more readable MoveLight code:
- `jump "label"` - Unconditional jump (Terminator)
- `branch cond "l1" "l2"` - Conditional branch (Terminator)
- `ret [sites]` - Return statement (Terminator)
- `abort s` - Abort execution (Terminator)
- `* a ::= b` - Write through reference
- `release s` - Release reference
- `letsite a ← *b` - Dereference (read reference)
- `letsite a ← freeze b` - Freeze reference

### lakefile.lean
Build targets for examples:
```bash
lake build initial      # Initial examples only
lake build expressivity # Expressivity examples only
lake build examples     # All examples
```

### README.md
Updated with:
- All build target instructions
- Description of initial examples

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
- Initial examples in `accepted/` have complete proofs (no `sorry`)
- Expressivity examples have `sorry` placeholders for future proof work
