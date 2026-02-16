# Changelog — 2026-02-16b

## Prove preservation_unpack (sorry-free)

### Summary
Completed the full proof of `preservation_unpack` — the preservation theorem
for the `unpack` statement `T { f1: a1, ..., fn: an } = b; cont`, which
destructures a record value at site `b` into individual field sites `a1..an`.

This was significantly simpler than `writeRef` because there are no heap,
pathEnv, rmap, or varEnv changes — only the frame's siteStore and the
typing environment's siteEnv are modified.

### Changes to Preservation.lean

**Strengthened `inv_unpack`**: Now extracts all 5 typing preconditions:
- `hlookup_src`: source site has record type
- `hfresh`: all field sites are fresh in siteEnv
- `hdistinct`: different fields map to different sites
- `hfield_exists`: every field in the pattern exists in the record type
- `hcont`: continuation is typed in the extended environment

**New helper lemmas** (6 lemmas, ~80 lines):
- `addFieldSites_nil` / `addFieldSites_cons` — unfolding lemmas for `addFieldSites`
- `addFieldSites_lookup_not_in_fields` — sites not in the field list are unchanged
- `addFieldSites_lookup_mem` — field sites get their expected `.basic bt` type
- `unpack_foldl_lookup_not_in_fields` — runtime foldl: non-field sites unchanged
- `unpack_foldl_lookup_mem` — runtime foldl: field sites get their field values

**`preservation_unpack`** (~160 lines):
- 14 of 21 WellTypedState fields delegate directly (no heap/rmap/pathEnv/varEnv changes)
- `env_wf`: uses existing `addFieldSites_refs_not_root` + `SiteEnv.delete_refs_not_root`
- `site_consistent`: the key case — old sites delegate via foldl not-in-fields lemma;
  new field sites use `HasType.readPath_field` + foldl membership lemma
- `siteEnv_refs_in_pathEnv`, `live_refs_unique`, `rmap_has_type`: all new entries
  are `.basic` type, so ref-typed lookups lead to contradiction

**Dispatcher**: Replaced `| unpack fields src cont => sorry` with call to
`preservation_unpack`.

### Remaining sorry's in dispatcher
- `jump`, `branch`, `ret`, `call`

### Files changed
- `LeanMove/Typing/Soundness/Preservation.lean` — +292/-2 lines
