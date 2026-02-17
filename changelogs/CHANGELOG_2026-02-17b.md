# Changelog — 2026-02-17b

## Summary: Eliminate freeze/CRT path_inclusion sorry in Weakening.lean

### self_loop_only_empty infrastructure

Added `self_loop_only_empty` property (`∀ u p, interpret_regex (pe.paths (u,u)) p → p = []`)
as a new parameter to `typecheck_stmt_weaken` and proved preservation through all PathEnv operations.

**TypesUtils.lean** (+50 lines):
- Added `self_loop_accepts_nil` field to `PathEnv.WellFormed` (4th field)
- Updated all `PathEnv.WellFormed` constructions in TypesUtils.lean

**DecidableTypeEnv.lean** (+2 lines):
- Updated `PathEnvDec.wellFormed_bool_sound` to prove the new `self_loop_accepts_nil` field

**Types.lean** (+4/-4 lines):
- Fixed `consume_ref_transfer` simp lemma adjustments for self-loop reasoning

### Weakening.lean (+262 lines)

**Four helper lemmas** proving `self_loop_only_empty` preservation:
- `self_loop_only_empty_uwe` — update_with_extension preserves (self-loop always ε)
- `self_loop_only_empty_drn` — delete_ref_node preserves (self-loop always ε)
- `self_loop_only_empty_gc` — garbage_collect preserves (self-loop always ε)
- `self_loop_only_empty_crt` — consume_ref_transfer preserves (requires `paths_from_non_member_empty`)

**`path_inclusion_consume_ref_transfer`** (~160 lines):
- Proves path inclusion through `consume_ref_transfer` with `extendSubst`
- Four cases: D (both fresh, self-loop), B (u fresh), C (v fresh), A (neither fresh)
- Key techniques: `List.mem_filter` + `decide_eq_true_eq` conversion, careful `subst` ordering

**`typecheck_stmt_weaken` — new `hself_loop_only_empty` parameter**:
- Added as 10th parameter (after `hpaths_from_nm`)
- Threaded through all 17 IH calls with appropriate helper lemma:
  - Direct passthrough: intLit, copy, move, binop, var_assign_invalid, pack, unpack, skip, jump, branch, ret
  - `self_loop_only_empty_uwe`: copy_ref, borrowField, borrowMutField
  - Compound UWE: borrowImm, borrowMut (nested `update_with_epsilon` unfolding)
  - `self_loop_only_empty_drn`: readRef, release
  - `self_loop_only_empty_gc`: writeRef
  - Compound GC+UWE: assign_valid
  - `self_loop_only_empty_crt`: freeze — **eliminates the last non-call sorry**

### Preservation.lean (+7/-6 lines)

- Updated 3 call sites of `typecheck_stmt_weaken` to pass `hwt.self_loop_only_empty`
- Minor simp fixes in `preservation_freeze` (interpret_regex, consume_ref_transfer reasoning)

### Remaining sorrys

- **Weakening.lean**: `| call => sorry` (line 2743) — only remaining sorry
- **Preservation.lean**: propagated from the call case in dispatcher

### Files changed

| File | Lines changed |
|------|--------------|
| `Weakening.lean` | +262 |
| `TypesUtils.lean` | +50 |
| `Preservation.lean` | +7/-6 |
| `DecidableTypeEnv.lean` | +2 |
| `Types.lean` | +4/-4 |
