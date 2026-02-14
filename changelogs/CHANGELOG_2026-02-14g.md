# Changes Made on 2026-02-14 (Part 7)

## Prove preservation_freeze (except rmap_paths)

Added `preservation_freeze` theorem proving type preservation for the `freeze` instruction, which converts a (possibly mutable) reference to an immutable one. At runtime this is a no-op (value copy); the typing environment deletes the old site, inserts a new site with a fresh ref `r'` and `.siteBorrowImm`, and applies `consume_ref_transfer` to transfer path edges from `r` to `r'`.

### Completed WellTypedState fields (16 of 17)

- **env_wf**: delegates to `TypeEnv.delete_insert_pathEnv_wf` + `consume_ref_transfer_wellformed`
- **stmt_typed**: from typing inversion
- **var_consistent**: reuses `var_consistent_extend_rmap_fresh`
- **site_consistent**: case split on new site `s` vs old sites (with delete/insert reasoning)
- **rmap_live**: reuses `rmap_live_extend_fresh`
- **varEnv_refs_in_pathEnv**: old refs survive in `pe'.refs` (filter preserves non-`r` members)
- **siteEnv_refs_in_pathEnv**: new site has `r' ∈ pe'.refs`; old sites use `live_refs_unique` to show `r_s ≠ r`
- **live_refs_unique**: 3-part proof with insert/delete reasoning; fresh `r'` contradicts `varEnv_refs_in_pathEnv`/`siteEnv_refs_in_pathEnv`
- **blocks_typed**, **lenv_empty_siteEnv**, **funEnv_typed**, **heap_loc_bound**: passthrough
- **rmap_root_none**: reuses `rmap_root_none_extend_fresh`
- **no_paths_to_root**: case analysis on `consume_ref_transfer` path structure
- **root_path_coherence**: `v = r'` case uses `refs_complete` + rmap indirection; `v ≠ r'` delegates to old

### Remaining sorry

- **rmap_paths**: needs dedicated `rmap_paths_consume_ref_transfer` lemma to handle the path union `G(r1, r') ∪ G(r1, r)` and the rmap/rmap' mismatch

### Wired up in dispatcher

- `| freeze src => exact preservation_freeze ...` replaces `sorry`

### File modified

1. **`LeanMove/Typing/Soundness/Preservation.lean`** — +215 lines (preservation_freeze theorem + dispatcher wiring)
