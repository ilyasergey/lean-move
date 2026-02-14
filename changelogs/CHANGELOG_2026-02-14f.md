# Changes Made on 2026-02-14 (Part 6)

## Extract more reusable lemmas in Preservation.lean

Added 5 more reusable lemmas, bringing the total to 12, and simplified 4 preservation cases.

### New lemmas

- **`freshRef_not_root`**: a ref fresh in pathEnv cannot be `.root` (used by copy_ref, borrowImm)
- **`site_consistent_delete_site`**: deleting a site preserves site_consistent (used by release)
- **`varEnv_refs_in_pathEnv_delete_ref_node`**: after delete_ref_node, varEnv refs stay in pathEnv.refs (used by readRef, release)
- **`siteEnv_refs_in_pathEnv_delete_ref_node`**: after delete_ref_node, siteEnv refs stay in pathEnv.refs (used by readRef, release)
- **`live_refs_unique_delete_site`**: deleting a site preserves live_refs_unique (used by readRef, release)

### Simplified cases

- **`preservation_copy_ref`**: 5-line `ht_not_root` block → 1-line call
- **`preservation_borrowImm`**: 5-line `hr_not_root` block → 1-line call
- **`preservation_readRef`**: 52-line block (varEnv_refs, siteEnv_refs, live_refs_unique) → 14 lines
- **`preservation_release`**: 49-line block (site_consistent, varEnv_refs, siteEnv_refs, live_refs_unique) → 4 one-line calls

### File modified

1. **`LeanMove/Typing/Soundness/Preservation.lean`** — 5 new lemmas, 4 cases simplified
