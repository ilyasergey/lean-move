# Changes Made on 2025-12-04

## Summary
Implemented TODO items from discussion transcript (GMT20250808) between Ilya Sergey and Todd Nowacki for the Move borrow checker formalization.

## Changes Implemented

### 1. ✅ Local Root Node in PathEnv
**File:** `LeanMove/Checker/TypeChecking.lean:98-101`

Added `PathEnv.init` to initialize PathEnv with `.root` present. The root represents a meta-reference to all local variables, enabling efficient borrow checking via graph traversal.

### 2. ✅ Updated `not_borrowed` Check
**File:** `LeanMove/Checker/TypeChecking.lean:210-216`

Refined to check that no outbound edge from `.root` accepts a path starting with `root_to_var x`. This matches Todd's implementation approach from the discussion.

### 3. ✅ Clarified BorrowingKind
**File:** `LeanMove/Lang/MoveLight.lean:65-79`

Added comments clarifying that `BorrowingKind` only tracks mutability (Imm/Mut), NOT provenance. Provenance is tracked via PathEnv edges with `root_to_var`. The existing implementation was already correct.

### 4. ✅ WellFormedEnv Invariant
**File:** `LeanMove/Checker/TypeChecking.lean:178`

Added `rootPresent` invariant ensuring `.root ∈ typeEnv.pathEnv.refs`.

### 5. ✅ Completed `call_connect_inputs_outputs`
**File:** `LeanMove/Checker/TypeChecking.lean:406-463`

Implemented three rules for function call path updates:
- Immutable outputs (IO) →`.*` from all inputs (MI ∪ II)
- Mutable outputs (MO) →`.*` from mutable inputs (MI) only
- Immutable outputs →`.*` from each other

### 6. ✅ Implemented `pack` Expression Rule
**File:** `LeanMove/Checker/TypeChecking.lean:384-399`

Implemented type checking for record construction: `b ← T { f1: a1, ..., fn: an }`
- Verifies field sites have correct types matching the record definition
- Ensures no aliasing (all field sites distinct)
- Consumes field sites (removes from siteEnv)
- Produces fresh site with record type
- Marked with `[Q]` for review with Todd (only handles basic types currently)

### 7. ✅ Added Mutable Input Validation to `call` Rule
**Files:** `LeanMove/Checker/TypeChecking.lean:460-482` (helper functions), `618-632` (call rule)

Added two validation checks for function calls:
- `check_mutable_inputs_isolated`: Ensures no mutable input can reach any other input via PathEnv
- `check_mutable_inputs_have_outbound`: Ensures all mutable inputs have non-trivial outbound edges (beyond ε)

These checks enforce proper isolation of mutable borrows passed to functions.

### 8. ✅ Implemented `return` Statement Rule
**File:** `LeanMove/Checker/TypeChecking.lean:634-657`

Implemented the `return (a1, ..., an)` statement rule as the dual of `call`:
- Type conformance checking: return sites must match function's declared return types
- Mutable return isolation: reuses `check_mutable_inputs_isolated` to prevent aliased mutable returns
- Liveness validation: reuses `check_mutable_inputs_have_outbound` for mutable returns
- Environment cleanup: removes all sites except those being returned (garbage collection)

The rule enforces ownership discipline at function exit, ensuring proper resource cleanup and safe return values.

### 9. ✅ Added Comprehensive Documentation Comments
**File:** `LeanMove/Checker/TypeChecking.lean:203-533`

Added detailed documentation for all three type checking relations:
- `typecheck_usage`: Explains variable usage operations (move, copy, borrow) with judgment form and invariants
- `typecheck_expr`: Documents expression forms, site lifecycle, and type safety properties
- `typecheck_stmt`: Comprehensive overview of statement rules, environment transformations, and validation checks

### 10. ✅ Implemented Sequential Composition (`seq`)
**Files:** `LeanMove/Lang/MoveLight.lean:124` (syntax), `LeanMove/Checker/TypeChecking.lean:659-667` (rule)

Changed block statement from list-based to binary sequential composition:
- Updated `Stmt` to use `seq : Stmt → Stmt → Stmt` instead of `block : List Stmt → Stmt`
- Updated `FunDef.body` from `List Stmt` to `Stmt` (use `seq` for multiple statements)
- Implemented typing rule: threads environment through first statement to second statement
- Simple, clean formalization: `⟨env⟩ ⊢ s1 ⤳ ⟨env'⟩` and `⟨env'⟩ ⊢ s2 ⤳ ⟨env''⟩` implies `⟨env⟩ ⊢ s1; s2 ⤳ ⟨env''⟩`

## Key Insights

1. **Local Root Node:** `Aref.root` tracks variable borrows via edges `root →[root_to_var x] r`
2. **Provenance Separation:** Tracked in path graph, not types—solves function output typing
3. **Dot-Star Extensions:** Function calls use `.*` for conservative aliasing approximation

## Build Status
✅ Successful: `lake build`
- Only warnings are for expected unused variables in TODO stubs

## Files Modified
- `LeanMove/Checker/TypeChecking.lean`: PathEnv init, not_borrowed, WellFormedEnv, call_connect_inputs_outputs, pack rule, mutable input validation, return rule, seq rule, comprehensive documentation
- `LeanMove/Lang/MoveLight.lean`: Documentation comments, changed block to seq (binary composition)

## Next Steps
1. Implement dot-star derivative rules in `extend_with_star`
2. Complete remaining expression/statement rules: `unpack`, `abort`, `release`, `if/while`
3. Work through complete examples and prove invariants
