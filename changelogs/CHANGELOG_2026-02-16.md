# Changelog — 2026-02-16

## Prove preservation_writeRef (sorry-free)

### Summary
Completed the full proof of `preservation_writeRef` — the preservation theorem
for the `writeRef` (mutable dereference write `*dst = val`) statement. This was
the most complex preservation case due to heap mutation affecting multiple
WellTypedState invariants simultaneously.

### Key challenge
When `*dst = val` writes value `val` at heap location `(loc, path)`, OTHER refs
may point into the same heap location (ancestor refs that `dst`'s ref was borrowed
from). The proof must show that `HasType` is preserved for all such ancestors after
the heap mutation.

### New theorems in Defs.lean
- **HasType strengthened**: Added reverse domain check (`fields.lookup f ≠ none → lookup fentries f ≠ none`)
  to `HasType.record`, enabling bidirectional domain reasoning.
- **`HasType_transfer`**: If `HasType v1 bt1`, `HasType v1 bt2`, and `HasType v2 bt2`,
  then `HasType v2 bt1`. Key for transferring typing across writePath.
- **`typeAtPath`**: Computes the BasicMoveType at a path within a type.
- **`readPath_ne_none_implies_typeAtPath`**: If `readPath` succeeds and `HasType` holds,
  the path's type exists.
- **`HasType_typeAtPath`**: The sub-value at a path has the type given by `typeAtPath`.
- **`HasType_transfer_readPath_ne_none`**: If `HasType v1 τ`, `HasType v2 τ`, and
  `readPath v1 path ≠ none`, then `readPath v2 path ≠ none`.
- **writePath/readPath interaction lemmas**:
  - `readPath_after_writePath_same`, `writePath_preserves_readPath_ne_first`
  - `writePath_preserves_HasType` (basic version)
  - `writePath_preserves_HasType_general` (with typeAtPath compat condition)
  - `writePath_preserves_readPath_HasType` (readPath at any path still typed after writePath)
  - `readPath_append` (path decomposition)
  - `writePath_preserves_readPath_ne_none` (readPath success preserved)
- **`heap_loc_bound_after_writeRef`**: writeRef preserves the heap location bound.

### New theorems in Preservation.lean
- **`wellTypedState_heap_writeRef`**: Adapts all 21 WellTypedState fields from old heap
  to new heap after writeRef. Handles 5 heap-dependent fields:
  - `var_consistent`: same-loc basic-typed uses `writePath_preserves_HasType_general`;
    same-loc ref-typed proved impossible via `HasType_not_ref`.
  - `rmap_live`/`rmap_paths`: uses `heap_writeRef_preserves_readRef_same_loc` with
    suffix transfer via `HasType_transfer_readPath_ne_none`.
  - `rmap_has_type`: uses `writePath_preserves_readPath_HasType`.
  - `heap_loc_bound`: delegates to `heap_loc_bound_after_writeRef`.
- **`stackSafe_heap_writeRef`**: Structural recursion over stack frames, using
  `wellTypedState_heap_writeRef` for each caller frame.
- **`preservation_writeRef`**: Full preservation theorem (~300 lines) covering all
  WellTypedState fields for the new typing environment after writeRef.

### Changes to InitState.lean
- Updated `HasType.record` constructor calls to include the new reverse domain argument.

### Files changed
- `LeanMove/Typing/Soundness/Defs.lean` — HasType strengthened, ~670 lines of new lemmas
- `LeanMove/Typing/Soundness/Preservation.lean` — ~506 lines: writeRef preservation + heap helpers
- `LeanMove/Typing/Soundness/InitState.lean` — updated HasType.record calls (+34/-9 lines)
