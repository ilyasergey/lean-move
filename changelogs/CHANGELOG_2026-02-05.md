# Changes Made on 2026-02-05

## Summary
Created algorithmic type checker and foundational proofs for equivalence with relational type checking.

## Overview

1. **Algorithmic Type Checker**: Created `TypeCheckingAlgorithmic.lean` with executable versions of the relational type checking rules.

2. **Foundational Proofs**: Created `TypeCheckingProofs.lean` with key lemmas needed for soundness/completeness proofs.

3. **Regex Equality**: Fixed `regexBeq` to use structural recursion (removed `termination_by`) enabling definitional equality.

4. **Soundness/Completeness Structure**: Added statement-level and function-level theorems with full structure; terminal cases proved, recursive cases marked with `sorry`.

## New Files

### LeanMove/Checker/TypeCheckingAlgorithmic.lean
New file containing algorithmic (executable) type checker:
- `check_stmt` - Returns `Option TypeEnv` for statement type checking
- `check_fun` - Returns `Bool` for function type checking
- `regexBeq` - Boolean equality for Regex (structural recursion)
- `TypeEnv.equiv_bool` - Boolean check for type environment equivalence
- Helper functions: `not_borrowed_bool`, `no_locals_borrowed_bool`, `all_fresh_sites_bool`, `types_conform_bool`, `check_outbound_bool`, etc.

### LeanMove/Checker/TypeCheckingProofs.lean
New file containing proofs and lemmas:

**Regex Lemmas:**
- `regexBeq_refl` - Reflexivity of regex boolean equality
- `regexBeq_eq` - Soundness: `regexBeq r1 r2 = true → r1 = r2`
- `eq_regexBeq` - Completeness: `r1 = r2 → regexBeq r1 r2 = true`

**Fresh Reference Lemmas:**
- `freshRef_iff_freshRefBool` - Equivalence between propositional and boolean fresh ref
- `nextFreshRef_fresh` - Fresh reference generation produces fresh refs
- `nextFreshRef_fresh_prop` - Propositional version

**PathEnv Lemmas:**
- `delete_ref_node_paths_involving_r` - PathEnv deletion lemmas
- `SimpleRootPath` - Inductive predicate for simple paths (empty, ε, or char)
- `PathEnv.Simple` - Paths from root are simple
- `PathEnv.WellFormed` - Well-formedness combining Simple + refs completeness
- `PathEnv.init_simple` - Initial path env has simple paths
- `PathEnv.init_wellformed` - Initial path env is well-formed

**TypeEnv Lemmas:**
- `TypeEnv.equiv_refl` - Reflexivity of env equivalence
- `TypeEnv.equiv_bool_implies_equiv` - Boolean implies propositional
- `TypeEnv.equiv_implies_equiv_bool` - Propositional implies boolean

**Borrowing Lemmas:**
- `not_borrowed_bool_sound` - Soundness with WellFormed assumption
- `no_locals_borrowed_bool_sound` - Soundness for all locals not borrowed

**Types Conform Lemmas:**
- `types_conform_bool_sound` - Boolean to propositional
- `types_conform_bool_complete` - Propositional to boolean

**Fresh Sites Lemmas:**
- `all_fresh_sites_bool_sound` - Boolean to propositional
- `all_fresh_sites_bool_complete` - Propositional to boolean

**Main Theorems (with sorries for recursive cases):**
- `check_stmt_sound` - Statement soundness (terminal cases complete)
- `check_stmt_complete` - Statement completeness (terminal cases complete)
- `check_fun_sound` - Function soundness
- `check_fun_complete` - Function completeness
- `check_fun_equiv` - Main equivalence: `check_fun f lenv = true ↔ typecheck_fun f lenv`

## Technical Notes

### Regex Equality
The `regexBeq` function was initially defined with `termination_by r _ => sizeOf r` which prevented definitional equality. By removing this annotation, Lean infers structural recursion automatically, enabling `rfl` proofs for base cases.

### PathEnv.WellFormed
A key invariant for the proofs combining two properties:
1. **Simple**: Paths from root are always empty, ε, or a single char
2. **Refs Complete**: References not in the refs list have empty paths from root

### Proof Strategy
The foundational lemmas establish bidirectional correspondence between boolean functions and propositional predicates. The main theorems have:
- **Terminal cases fully proved**: skip, jump, branch, ret, abort
- **Recursive cases with sorry**: letBind, writeRef, assign, call, release, unpack

Completing the recursive cases requires:
1. Proving WellFormed preservation for path environment operations
2. Showing that `nextFreshRef` produces refs equivalent to existentially quantified refs in the relational rules

### File Status
- `TypeCheckingAlgorithmic.lean`: Compiles without errors or warnings
- `TypeCheckingProofs.lean`: Compiles with `sorry` warnings only
