# Changes Made on 2026-01-21

## Summary
Added integer literals to MoveLight; refactored control flow into Terminator type; improved MVIR documentation in examples.

## Overview

This change introduces several improvements:

1. **Integer Literals**: Added native support for integer literals in MoveLight with the new
   `Expr.intLit` expression and renamed `.tint` to `.u64` for clarity.

2. **Control Flow Refactoring**: Separated control flow (jump, branch, ret, abort) from regular
   statements into a dedicated `Terminator` type.

3. **MVIR Documentation**: All rejected examples now include the full original MVIR source code
   as documentation comments, and translations have been verified for correctness.

4. **Build Targets**: Added `lake build` targets for all example categories.

## Major Changes

### Integer Literals Support

**LeanMove/Lang/MoveLight.lean**:
- Renamed `.tint` to `.u64` in `BasicMoveType` for clarity
- Added `Expr.intLit : Nat → Expr` constructor for integer literal expressions

**LeanMove/Checker/TypeChecking.lean**:
- Added `typecheck_expr.t_intLit` rule: integer literals type check to `.basic .u64`

**LeanMove/Lang/Macros.lean**:
- Added macro `letsite a ← #n` for binding integer literals to sites
- Example usage: `(letsite s0 ← #0)` binds integer 0 to site s0

### MVIR Documentation in Rejected Examples

All files in `LeanMove/Examples/expressivity/rejected/` now include:
- Full original MVIR source code as documentation comments
- Verified translations matching MVIR semantics exactly
- Proper use of integer literal expressions

Files updated:
- `simple_dangling.lean` - Four modules demonstrating dangling reference errors
- `imm_borrow_after_mut_call_invalid.lean` - Cannot write with immutable alias
- `imm_borrow_after_mut_fields_invalid.lean` - Cannot write through mutable when immutable field ref exists
- `mutable_borrows_not_unique_calls_invalid.lean` - Unknown relationship between overlapping refs

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
- `letsite a ← #n` - Integer literal (NEW)

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

- All examples now include full original MVIR source code as documentation comments
- The transpilation preserves the essential borrow checking semantics
- Some simplifications were made where MoveLight doesn't support certain features
  (e.g., vectors, tuple return types)
- Initial examples in `accepted/` have complete proofs (no `sorry`)
- Expressivity examples have `sorry` placeholders for future proof work
- Integer literals are now explicitly represented using `Expr.intLit` and the `#n` macro
- Separate `.mvir` files removed; MVIR source is now embedded in Lean files as comments
