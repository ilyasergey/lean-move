# Changes Made on 2026-01-23

## Summary
Added macros for pack, borrowField, and call statements; proved M_t_welltyped theorem; refactored deref_borrow_field_ok example to use macros and reorganized its structure.

## Overview

1. **New Macros**: Added `pack(...)`, `borrowField(...)`, and `call(...)` macros to `Macros.lean` for struct packing, field borrowing, and function calls.

2. **M_t Soundness Proof**: Proved `M_t_welltyped` theorem in `deref_borrow_field_ok.lean` with no axioms or sorrys.

3. **Refactored Example**: Converted all function bodies in `deref_borrow_field_ok.lean` to use the flat `;;` macro style and reorganized the file to group each function definition with its soundness proof.

## Changes to Existing Files

### LeanMove/Lang/Macros.lean
- Added `letsite s ← pack("T", [(f, a)])` macro for struct packing
- Added `letsite s ← borrowField(src, bt, f)` macro for field borrowing
- Added `call(results, "fname", args)` macro for function calls
- Updated documentation notes section (moved pack/borrowField/call from "Direct notation" to macro list)

### LeanMove/Tests/initial/accepted/deref_borrow_field_ok.lean
- Added `M_t_welltyped` theorem with full proof (let_bind_move → let_bind_borrowField → let_bind_readRef → var_assign_invalid → ret)
- Added `M_t_initEnv` and `M_t_lenv` definitions for the M.t function
- Added `module_funEnv` shared function environment definition
- Refactored `M_new`, `M_t`, and `foo` function bodies to use macros with flat `;;` composition
- Reorganized file structure: shared definitions at top, then each function grouped with its MoveIR comment, init environment, label environment, and soundness proof
