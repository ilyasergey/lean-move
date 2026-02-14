# Changes Made on 2026-02-14 (Part 5)

## Extract reusable lemmas in Preservation.lean

Extracted 7 reusable lemmas from repeated proof patterns across 6 proven
preservation cases, and simplified those cases to use the new lemmas.
Net change: 244 insertions, 254 deletions (−10 lines).

### Group A: Basic insert (siteEnv gets `.basic` type, no new ref)

- **`siteEnv_refs_in_pathEnv_insert_basic`**: inserting a `.basic` type preserves `siteEnv_refs_in_pathEnv`
- **`live_refs_unique_insert_basic`**: inserting a `.basic` type preserves `live_refs_unique`
- **Used by**: `preservation_intLit`, `preservation_copy_val` (replaced ~16 lines each)

### Group B: `delete_ref_node` (pathEnv removes a ref node)

- **`no_paths_to_root_delete_ref_node'`**: `delete_ref_node` preserves `no_paths_to_root`
- **`root_path_coherence_delete_ref_node'`**: `delete_ref_node` preserves `root_path_coherence`
- **Used by**: `preservation_readRef`, `preservation_release` (replaced ~8+7 lines each)

### Group C: Fresh rmap extension (rmap extended with fresh ref `t`)

- **`var_consistent_extend_rmap_fresh`**: extending rmap with a fresh ref preserves `var_consistent`
- **`site_consistent_old_entry_extend_rmap`**: old siteEnv entries remain consistent under rmap extension
- **`rmap_live_extend_fresh`**: extending rmap with a live mapping preserves `rmap_live`
- **`rmap_root_none_extend_fresh`**: extending rmap with `t ≠ .root` preserves `rmap_root_none`
- **`live_refs_unique_insert_fresh_ref`**: inserting a site with fresh ref `t` preserves `live_refs_unique`
- **Used by**: `preservation_copy_ref`, `preservation_borrowImm` (replaced ~35+ lines each)

### Reuse potential for remaining sorry'd cases

Group C lemmas will directly apply to: `borrowMut`, `borrowField`, `borrowMutField`
(all follow the same fresh-ref-extension pattern).

### File modified

1. **`LeanMove/Typing/Soundness/Preservation.lean`** — 7 new lemmas, 6 cases simplified
