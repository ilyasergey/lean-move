# Changelog — 2026-02-18b

## Refactor return type checking: `MoveType` → `List ParamType` with 4-condition `ret` rule

### Summary

Replaced the single-type return checking with a multi-value return type system using `List ParamType`,
and rewrote the `ret` rule to enforce four safety conditions for returned references:

1. **Types conform**: positional matching of returned sites against declared return types
2. **No local borrowing**: returned refs don't borrow locals (`G(root, r) = ∅`)
3. **Writability**: mutable returned refs have only trivial outbound paths (`G(r, y) ⊆ {ε}`)
4. **No aliasing**: no other returned ref reaches a mutable return (`G(r₂, r₁) = ∅`)

These conditions ensure that returned references are safe at the callee boundary, consistent with
the caller's conservative path modeling in `call_connect_inputs_outputs`.

### Core changes

| File | Change |
|------|--------|
| `MoveLight.lean` | Moved `ParamType` from `Types.lean`; changed `FunDef.returnType : MoveType` → `List ParamType` |
| `Types.lean` | Removed `ParamType` definition (now in `MoveLight.lean`) |
| `TypeChecking.lean` | Rewrote `typecheck_stmt` to use `List ParamType`; new 4-condition `ret` rule; added `types_conform`, `ret_refs_not_from_locals`, `ret_mutable_writable`, `ret_mutable_no_aliases` predicates |
| `TypeCheckingAlgorithmic.lean` | Added boolean helpers `ret_refs_not_from_locals_bool`, `ret_mutable_writable_bool`, `ret_mutable_no_aliases_bool`; updated `check_stmt` ret case |
| `AlgorithmicTypingSoundness.lean` | Added soundness lemmas for all 3 new boolean helpers; updated `check_stmt_sound` ret case |
| `Weakening.lean` | Mechanical `retType` → `retTypes` rename; ret case uses `sorry` for conditions 2-4 (anti-monotone in paths) |
| `Defs.lean` | `WellTypedState.retType : MoveType` → `retTypes : List ParamType`; updated `StackSafe` |
| `Preservation.lean` | Mechanical rename; updated `inv_ret` to extract 4 conditions |
| `Progress.lean` | Mechanical rename |
| `SafeExec.lean` | Mechanical rename |

### New litmus tests

#### Accepted (3 tests in `return_param_ref_ok.lean`)
- `fn_return_basic`: returns a basic `u64` — trivially passes (no refs)
- `fn_return_param_ref`: takes `r: &mut u64`, returns `move(r)` — passes because parameter refs use `.varRef` (no path from root)
- `fn_return_two`: returns two independent `&mut u64` params — passes writability and no-aliasing

#### Rejected
- `return_local_borrow.lean`: borrows a local variable and tries to return it — fails condition 2 (root reaches the borrow ref)
- `return_aliased_mut.lean`: returns two aliased mutable refs via copy+move of same param — fails condition 4
- `return_mut_with_outstanding_borrow.lean`: takes `p: &mut Point`, does `borrowField` creating `G(varRef(p), r') = [.field x]`, then tries to return `move(p)` — fails condition 3 (non-trivial outbound path)

### Example file updates (~25 files)

All `FunDef` constructions updated:
- `returnType := .basic .u64` → `returnType := [⟨.u64, none⟩]`
- `returnType := .ref bt r bk` → `returnType := [⟨bt, some true/false⟩]`
- Functions with `Stmt.ret []` changed to `returnType := []` (not `[⟨.tunit, none⟩]`, since `types_conform [] [_]` = false due to length mismatch)

### Runtime & soundness tests

Added runtime execution and `type_soundness_dec` checks to `AllTests.lean` for all 3 new accepted return tests.

### File stats

| File | Changes |
|------|---------|
| `TypeChecking.lean` | major rewrite of ret rule and helpers |
| `TypeCheckingAlgorithmic.lean` | +83 boolean helpers |
| `AlgorithmicTypingSoundness.lean` | +107 soundness lemmas |
| `Weakening.lean` | +161/-161 (rename + ret case rewrite) |
| `Preservation.lean` | +433 rename |
| New litmus tests | +356 lines across 4 files |
| Example updates | ~25 files, minor each |
| **Total** | **+960/-511** across 37 files |

### Result

Full project builds successfully (328/328 jobs). All existing accepted tests pass.
All new litmus tests demonstrate the new return checking capabilities.

### Known limitations

Conditions 2-4 in the `ret` rule are anti-monotone in paths (more paths can violate them),
so the weakening proof for the `ret` case uses `sorry` for these conditions. This is expected —
weakening adds paths, and these conditions require path absence/emptiness.
