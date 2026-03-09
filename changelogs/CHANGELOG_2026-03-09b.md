# Changelog — 2026-03-09b

## Phase A: Add containsEnum-conditional borrow restrictions for multi-variant enum soundness

### Summary

Modified typing rules for `let_bind_borrowMut` and `var_assign_valid` to
add conditional restrictions when the borrowed/assigned type transitively
contains an enum. This is Phase A of a 4-phase plan to lift the
`checkEnumSingleVariant` restriction and support multi-variant enums in the
soundness proof.

### Motivation

The `writeRef` suffix case in preservation requires that two values of the
same type have identical `typeAtPathV` structure at every sub-path. For
record types this holds automatically (same field domain). For enum types,
`typeAtPathV` depends on the runtime variant name — so if a mutable borrow
exists alongside another reference at the same heap location, writing a
different variant through the mutable borrow would invalidate the other
reference's path structure. The fix: when a type contains an enum, require
`not_borrowed x env` before mutable borrowing and invalidate the source
variable, preventing aliased writes that could change the variant tag.

### Design: containsEnum-conditional restrictions

**`BasicMoveType.containsEnum`** (new, `MoveLight.lean`): Mutual recursive
function that checks whether a basic type transitively contains `.tenum`:
- `containsEnum (.tenum _) = true`
- `containsEnum (.trecord fields) = containsEnumEntries fields`
- `containsEnum (.tvec bt) = containsEnum bt`
- All other basic types return `false`

**`let_bind_borrowMut`** (modified, `TypeChecking.lean`):
```
Before: ... → typecheck_stmt lenv {env with siteEnv := ..., pathEnv := ...} cont
After:  ... → (containsEnum τ → not_borrowed x env) →
              typecheck_stmt lenv {env with
                varEnv := if containsEnum τ then
                            update env.varEnv x (.invalidVar, .basic τ, ms)
                          else env.varEnv,
                siteEnv := ..., pathEnv := ...} cont
```

When borrowing a variable whose type contains an enum:
1. Requires `not_borrowed x env` (no existing paths from root to x)
2. Invalidates the variable in the continuation (prevents writes through the original variable)

For non-enum types, both conditions are trivially satisfied (the
`containsEnum τ → ...` implication is vacuously true, and the `if` branch
takes the `else` path leaving `env.varEnv` unchanged).

**`var_assign_valid`** (modified, `TypeChecking.lean`): Same
`containsEnum τ → not_borrowed x env` guard added before assignment.

### Downstream proof fixes

All 5 downstream proof files were updated to handle the new typing rule
structure:

**AlgorithmicTypingSoundness.lean**: Both `borrowMut` and `assign` cases
updated to split the 3-way conjunction `⟨⟨hms, hnotIn⟩, hnotbor⟩` and
construct `not_borrowed_bool_sound` proofs. WellFormed for conditional
varEnv proved via `split`.

**Weakening.lean**: `weaken_let_bind_borrowMut` and
`weaken_var_assign_valid` extended with `hnotBorrowed` parameters.
- `VarEnvSubstEquiv_update_invalid` used for conditional varEnv weakening
- `not_borrowed_weaken` transfers `not_borrowed` through subsumption
- `RefsUnique` for conditional varEnv proved via `refine ⟨..., ...⟩`
  (triple conjunction, not binary)
- Dispatcher pattern matches updated for both cases

**Preservation.lean**:
- `inv_borrowMut` and `inv_assign` return types extended with `hnotBorrowed`
- `preservation_borrow` (shared by borrowImm/borrowMut) parameterised by
  `ve'` (continuation varEnv), `hve_valid`, `hve_invalid_consistent`,
  `hve_wf` — allowing the new env to use either `env.varEnv` (borrowImm)
  or the conditional varEnv (borrowMut)
- `varEnv_refs_in_pathEnv`, `live_refs_unique`, `rmap_has_type` proofs all
  updated to convert `ve'` lookups back to `env.varEnv` via `hve_valid`
- `var_consistent` proof handles ref types via `freshRefInEnv_ne_varEnv_ref`

**Progress.lean**: Pattern match updated for extra `borrowMut` premise.

### Files changed

| File | Changes |
|------|---------|
| `MoveLight.lean` | +`containsEnum`/`containsEnumEntries` mutual def, simp lemmas |
| `TypeChecking.lean` | +`containsEnum → not_borrowed` guard, conditional varEnv invalidation |
| `AlgorithmicTypeChecking.lean` | +`not_borrowed_bool` check in borrowMut/assign |
| `AlgorithmicTypingSoundness.lean` | +3-way conjunction handling, `not_borrowed_bool_sound` |
| `Weakening.lean` | +`hnotBorrowed` params, conditional varEnv weakening, dispatcher updates |
| `Preservation.lean` | +`ve'` parameterisation in `preservation_borrow`, inversion updates |
| `Progress.lean` | +extra premise in borrowMut pattern |

### Build

393 jobs, zero sorrys. All existing tests pass — no behaviour change for
non-enum types.
