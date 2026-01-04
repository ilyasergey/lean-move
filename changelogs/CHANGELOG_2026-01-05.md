# Changes Made on 2026-01-05

## Summary
Fixed `TypeEnv.equiv` to enable type checking of loops with borrow-release patterns.

## Problem Identified

The `borrow_in_loop.lean` example could not be proven to type-check. Analysis revealed two issues:

1. **Missing site initialization**: The program used `assign var_x s0` but `s0` was never bound in the `siteEnv`.

2. **Borrow-checking violation**: The program kept a borrow alive across a loop back-edge while trying to reassign the borrowed variable. The typing rules correctly reject this pattern.

## Solution: Weaken TypeEnv.equiv

The original `TypeEnv.equiv` required **full extensional equality** of `PathEnv.paths` functions:
```lean
(∀ p, env1.pathEnv.paths p = env2.pathEnv.paths p)
```

This was too strong. After `delete_ref_node` removes a reference `r`:
- `(delete_ref_node pe r).paths (r, r) = Regex.empty` (paths involving r are emptied)
- `PathEnv.init.paths (r, r) = Regex.ε` (the function returns ε when u = v)

These differ syntactically even though `r ∉ PathEnv.init.refs`.

**Fix:** Weaken `TypeEnv.equiv` to only compare paths between references in the refs list:
```lean
(∀ u v, u ∈ env1.pathEnv.refs → v ∈ env1.pathEnv.refs →
  env1.pathEnv.paths (u, v) = env2.pathEnv.paths (u, v))
```

This is semantically correct because paths involving non-live references are irrelevant for borrow checking.

## Changes Made

### 1. Modified `TypeEnv.equiv`
**File:** `LeanMove/Checker/TypeChecking.lean`

- Changed from full extensional equality to comparing only paths between live refs
- Added detailed documentation explaining the rationale

### 2. Added `delete_ref_node` lemmas
**File:** `LeanMove/Checker/TypeChecking.lean`

Added several lemmas to support reasoning about `delete_ref_node`:
- `delete_ref_node_refs`: How refs list changes after deletion
- `delete_ref_node_paths_involving_r`: Paths involving deleted ref become empty
- `delete_ref_node_paths_not_involving_r`: Paths not involving deleted ref are unchanged
- `delete_ref_node_restores_init_refs`: Specific lemma for restoring to init
- `delete_ref_node_init_paths_between_roots`: Paths between roots preserved
- `delete_ref_node_init_refs`: Refs list restoration
- `delete_ref_node_paths_between_remaining`: Key lemma for remaining refs

### 3. Documented `borrow_in_loop.lean`
**File:** `LeanMove/Examples/borrow_in_loop.lean`

Added extensive documentation explaining:
- Why the program cannot type-check (borrow-checking violation)
- The two stuck points in the proof
- What would make the program type-check (alternatives)

### 4. Created `borrow_in_loop_fixed.lean`
**File:** `LeanMove/Examples/borrow_in_loop_fixed.lean` (new file)

Created a fixed version of the program that:
- Takes `x` as a parameter (starts valid)
- Borrows `x`, immediately releases the borrow, then jumps back
- **Complete proof** that the program type-checks using the weakened `TypeEnv.equiv`

The proof demonstrates that releasing a borrow before a loop back-edge correctly restores the type environment to a state equivalent to the loop entry environment.

## Key Insight

The fix is semantically correct: paths involving non-live references are irrelevant for borrow checking since those refs have been released. The `refs` list accurately tracks which abstract references are "live" in the current scope, so we only need to compare paths between those references.

## Code Organization: Decoupling Types from Rules

### 5. Created `Types.lean`
**File:** `LeanMove/Checker/Types.lean` (new file)

Extracted type environment definitions and auxiliary lemmas from `TypeChecking.lean`:
- Basic types: `Mut`, `VarBorrowStatus`, `IsValid`
- Environment types: `SiteEnv`, `VarEnv`, `PathEnv`, `FunEnv`, `TypeEnv`, `LabelEnv`
- PathEnv operations: `init`, `check_outbound`, `garbage_collect`, `update_with_extension`, `extend_with_star`, `update_with_epsilon`, `delete_ref_node`, `consume_ref_transfer`, `freshRef`
- Function signatures: `ParamType`, `FunSig`
- `TypeEnv.equiv` definition with documentation
- `WellFormedEnv` structure
- All `delete_ref_node` lemmas

### 6. Simplified `TypeChecking.lean`
**File:** `LeanMove/Checker/TypeChecking.lean`

Now imports `Types.lean` and contains only:
- Typing relations for usages (`typecheck_usage`)
- Typing relations for expressions (`typecheck_expr`)
- Typing relations for statements (`typecheck_stmt`)
- Typing relation for functions (`typecheck_fun`)
- Helper functions specific to typing rules
- Notation macros

This separation makes the codebase more maintainable by keeping type definitions separate from typing rules.
