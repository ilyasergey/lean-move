# Changelog — 2026-03-04

## Complete type soundness proof for vector extension (zero sorrys)

### Summary

Filled all 32 remaining `sorry` placeholders across 3 proof files,
making the MoveLight type soundness proof fully machine-checked with
no axioms beyond Lean's kernel. The type system now rules out 8 of 12
runtime error kinds; only `divisionByZero`, `outOfFuel`, `aborted`,
and `vectorError` remain as acceptable (non-preventable) errors.

### Files changed

**Progress.lean** (+405 lines) — 16 sorrys filled:
- 8 cases in `step_danglingRef_source`: extended the conclusion with
  4 new disjuncts for vector operations that can produce dangling-ref
  errors (vecLen, vecPopBack, vecPushBack, vecSwap); proved 4 exfalso
  cases for operations that cannot (vecPack, vecUnpack, vecImmBorrow,
  vecMutBorrow).
- 8 cases in `step_error_is_acceptable`: for each vector operation,
  proved that any error from a well-typed state is acceptable by
  eliminating uninitializedSite, typeMismatch, and danglingRef using
  `site_consistent`, `rmap_live`, and `rmap_has_type`.
- Added 4 helper lemmas: `no_danglingRef_vecLen`,
  `no_danglingRef_vecPopBack`, `no_danglingRef_vecPushBack`,
  `no_danglingRef_vecSwap`.

**Weakening.lean** (+792 lines) — 8 sorrys filled:
- 8 cases in `typecheck_stmt_weaken` for vector typing rules.
- New helper lemmas for vecUnpack: `SiteEnvSubstEquiv_addVecSites`,
  `site_tracked_addVecSites`, `RefsUnique_addVecSites` (mirroring
  existing `addFieldSites` lemmas for record unpacking).

**Preservation.lean** (+2418 lines) — 8 sorrys filled:
- 8 `preservation_vec*` helper theorems, one per vector operation.
- `vecPack`, `vecUnpack`: site store updates only (similar to
  `preservation_pack` / `preservation_unpack`).
- `vecLen`: heap read + site store update + `delete_ref_node`
  (similar to `preservation_readRef`).
- `vecImmBorrow`, `vecMutBorrow`: heap alloc + `update_with_extension`
  with `[.vecElem]` path (similar to `preservation_borrowField` /
  `preservation_borrowMutField`).
- `vecPopBack`, `vecPushBack`, `vecSwap`: heap read + write +
  `delete_ref_node` (similar to `preservation_writeRef`).
- Filled preservation dispatch (8 sorry → exact calls to helpers).

**Supporting files:**
- `Defs.lean` (+19 lines): `heap_alloc_preserves_readRef`,
  `heap_loc_bound_after_alloc`, `HasType.vec_elems` inversion lemma.
- `StackSafeUtils.lean` (+103 lines): `heap_alloc_read_same`,
  `heap_alloc_read_ne`, `lt_heap_alloc_nextLoc`,
  `stackSafe_heap_alloc`.
- `TypesUtils.lean` (+12 lines): `TypeEnv.delete_delete_insert_pathEnv_wf`
  for double-delete + insert well-formedness.
- `InitState.lean` (+8 lines): vector cases for `initState_safe`.

**metatheory.md** (+323 lines): Added Part III (Vector Extension)
documenting all 8 typing rules, operational semantics, value typing,
`.vecElem` path element, soundness proof structure, and design
decisions. Updated Parts I–II for consistency (error counts, field
counts, macro table, path operations table).

### Build

366 jobs, all passing. Zero sorrys (`grep -rn "sorry" LeanMove/`
returns no results).
