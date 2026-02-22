# Changes Made on 2026-01-22

## Summary
Added algorithmic type checking function `check_usage` with soundness proofs; refactored type definitions into DecidableEquality module; improved decidability infrastructure for MoveLight types.

## Overview

This change introduces algorithmic type checking to complement the relational typing rules:

1. **Algorithmic `check_usage`**: A function that computes the output environment given an input environment, usage, site, and type. Returns `Option TypeEnv`.

2. **Soundness Proofs**: New `TypeCheckingProofs.lean` file with formal proofs connecting the algorithmic `check_usage` to the relational `typecheck_usage`.

3. **DecidableEquality Module**: Extracted type definitions requiring custom boolean equality (`Field`, `BasicMoveType`, `MoveType`, etc.) into a dedicated module with soundness/completeness proofs.

4. **Boolean Borrow Checking**: Added `not_borrowed_bool` function for efficient algorithmic checking of the borrow constraint.

## Major Changes

### New Algorithmic Type Checking

**LeanMove/Checker/TypeChecking.lean**:
- Added `not_borrowed_bool : Var → TypeEnv → Bool` - boolean version of `not_borrowed` for algorithmic checking
- Added `check_usage : TypeEnv → Usage → Site → MoveType → Option TypeEnv` - algorithmic version of `typecheck_usage`
- Changed `typecheck_usage` rules to use `freshRefBool` instead of `freshRef` for decidable checking
- Updated `typecheck_expr.usage` to use `check_usage` function

### New Soundness Proofs

**LeanMove/Checker/TypeCheckingProofs.lean** (NEW FILE):
- `PathEnv.WellFormed` - Well-formedness predicate for PathEnv
- `PathEnv.init_wellformed` - Proof that initial PathEnv is well-formed
- `not_borrowed_bool_implies_not_borrowed_for_simple_regex` - Helper lemma for simple regex cases
- `not_borrowed_bool_implies_not_borrowed` - Soundness of boolean borrow check
- `check_usage_sound` - Main soundness theorem: `check_usage env u a τ = some env' → typecheck_usage env u env' a τ`

### DecidableEquality Module

**LeanMove/Structures/DecidableEquality.lean** (NEW FILE):
Extracted from MoveLight.lean, contains:
- `Field`, `BasicMoveType`, `Var`, `Aref`, `BorrowingKind`, `MoveType` type definitions
- Custom `beq` functions for nested inductive types (records)
- Reflexivity proofs (`beq_refl`)
- Soundness proofs (`eq_of_beq`)
- Completeness proofs (`beq_of_eq`)
- `DecidableEq` instances derived from these proofs

### Boolean freshRef

**LeanMove/Checker/Types.lean**:
- Added `freshRefBool : Aref → PathEnv → Bool` - boolean version of `freshRef`
- Added `freshRef_iff_freshRefBool` - equivalence proof between `freshRef` and `freshRefBool`

## New Files

1. **LeanMove/Checker/TypeCheckingProofs.lean**
   - Soundness proofs for algorithmic type checking
   - Connects `check_usage` function to `typecheck_usage` relation

2. **LeanMove/Structures/DecidableEquality.lean**
   - Core MoveLight types with decidable equality
   - Boolean equality functions with formal proofs

## Changes to Existing Files

### LeanMove/Checker/TypeChecking.lean
- Added `not_borrowed_bool` definition
- Added `check_usage` function (60+ lines)
- Changed `freshRef` to `freshRefBool` in `typecheck_usage` rules
- Updated `typecheck_expr.usage` constructor to use `check_usage`

### LeanMove/Checker/Types.lean
- Added `freshRefBool` definition
- Added `freshRef_iff_freshRefBool` theorem

### LeanMove/Lang/MoveLight.lean
- Removed type definitions (moved to DecidableEquality.lean)
- Now imports DecidableEquality.lean

### LeanMove/Tests/initial/accepted/*.lean
- Updated proofs to use new `typecheck_expr.usage` signature with `check_usage`
- Proofs now use `rfl` to discharge `check_usage` obligations

## Technical Details

### check_usage Function Structure
```lean
def check_usage (env : TypeEnv) (u : Usage) (a : Site) (τ : MoveType) : Option TypeEnv :=
  if ¬notIn env.siteEnv a then none
  else match u with
  | .move x => ...      -- checks not_borrowed_bool, lookup, type equality
  | .copy x => ...      -- handles basic types and reference types
  | .borrowImm x => ... -- creates immutable borrow
  | .borrowMut x => ... -- creates mutable borrow (requires .mutable)
```

### PathEnv.WellFormed Predicate
```lean
def PathEnv.WellFormed (pe : PathEnv) : Prop :=
  ∀ r, r ∉ pe.refs → ∀ p : PathElement, ¬interpret_regex (pe.paths (.root, r)) [p]
```

This ensures refs not in the refs list have paths that don't accept any single-element path, which is necessary for the soundness of `not_borrowed_bool`.

## Notes

- The algorithmic `check_usage` is sound but not complete (conservative for complex regexes)
- `not_borrowed_bool` returns `false` for complex regex patterns (conservative approximation)
- All proofs are complete (no `sorry` outside expressivity examples)
- Initial example proofs updated to work with new `check_usage`-based typing
