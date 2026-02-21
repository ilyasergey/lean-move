# Changelog — 2026-02-22

## Consume call input sites + refine return writability check

### Summary

Two coordinated changes to the type checker that make `extension_after_call` use a real `call`
to `borrow` (instead of inlining), while still rejecting `return_mut_with_outstanding_borrow`:

1. **Consume call input sites**: after `call_connect_inputs_outputs`, delete the input sites
   (`bs`) from `siteEnv` via `AssocMap.deleteAll`. This models that arguments are consumed by
   the callee.

2. **Refine `ret` writability check**: check mutable return refs against live non-returned
   ref-typed sites in `siteEnv`, not all `pathEnv.refs`. This avoids false rejections when
   dead (consumed) input sites still have refs in `pathEnv.refs`.

Additionally: new macros for `borrowMutField`, `unpack`, and `*a ::= b`; `extend_with_star`
outbound path formula changed from `.* · G` to `G · .`; metatheory documentation updated.

### Problem

`extension_after_call.lean` inlined the `borrow` function body instead of using a `call`.
After a call, the callee's input sites should be consumed — the caller should not see them.
Without consuming input sites, the writability check at `ret` would falsely reject programs
where a returned mutable ref has paths to consumed (dead) input refs.

The old `ret_mutable_writable_bool` checked against all `pathEnv.refs`, including refs from
consumed sites. The refined check only looks at live non-returned ref-typed sites in `siteEnv`.

### Key changes

#### TypeChecking.lean (relational typing rules)
- `typecheck_stmt.call`: continuation env wraps with `deleteAll env''.siteEnv bs`
- `typecheck_stmt.ret` writability (condition 3): changed from checking all `y ∈ pathEnv.refs`
  to checking non-returned sites `b ∉ as` with `lookup siteEnv b = some (.ref bt' r' bk')`

#### TypeCheckingAlgorithmic.lean (executable checker)
- `ret_mutable_writable_bool`: iterates `siteEnv.entries` (skipping returned sites) instead
  of `pathEnv.refs`
- `check_stmt` call case: wraps continuation env with `deleteAll env''.siteEnv bs`

#### AlgorithmicTypingSoundness.lean
- `ret_mutable_writable_bool_sound`: updated proof for new signature (lookup-based witnesses)
- Added `list_lookup_mem`, `lookup_mem_entries` helpers
- `check_stmt_sound` call case: added `hwf_del` for deleteAll-wrapped env WF

#### Types.lean
- `extend_with_star`: outbound path formula changed from `Regex.star(.) · G(source, v)` to
  `G(source, v) · Regex.dot`. This ensures same-level aliases produce `concat(ε, .)` which is
  NOT `only_matches_empty`, blocking direct writes through call outputs that alias other refs.
  After field borrow (Brzozowski derivative), the dot collapses, allowing writes through
  field borrows.

#### TypesUtils.lean
- `extend_with_star_paths_to_non_member`: proof adjusted for new formula direction

#### Weakening.lean
- Made `SiteEnvSubstEquiv_deleteAll`, `RefsUnique_deleteAll`, `call_connect_refs_mono` public
  (removed `private`) for use in Preservation.lean
- `weaken_call`: updated for `deleteAll`-wrapped continuation env; added WF proofs for
  deleteAll envs, precomputed `call_connect` helpers to avoid `let`-binding rewrite issues
- `extend_with_star_path_inclusion`: fixed path direction for new outbound formula

#### Preservation.lean
- Added helper lemmas: `lookup_deleteAll_not_mem`, `types_conform_ext`
- `preservation_call`: introduced `popEnvDel = {popEnv with siteEnv := deleteAll popEnv.siteEnv argSites}`;
  rewrote `hstmt_typed_pop` to weaken from `ccDelEnv` to `popEnvDel`; changed entire StackSafe
  construction from `popEnv` to `popEnvDel` with adjusted siteEnv-related fields
- `inv_call`, `inv_ret`: updated for new typing rule signatures

#### Lang/Macros.lean
- Added macros: `borrowMutField`, `unpack`, fixed `*a ::= b` and `branch` precedence
- Updated documentation

#### metatheory.md
- Added Appendix on syntactic macros

#### Examples (25 files)
- `extension_after_call.lean`: uses `call` to `borrow` instead of inlining; added `borrow_sig`
- All examples updated to use new macros (`borrowMutField`, `unpack`, `*a ::= b`, `ret`)
- `return_mut_with_outstanding_borrow.lean`: still correctly rejected

### File stats

| File | Changes |
|------|---------|
| `TypeChecking.lean` | ~15 lines |
| `TypeCheckingAlgorithmic.lean` | ~15 lines |
| `AlgorithmicTypingSoundness.lean` | ~40 lines |
| `Types.lean` | ~10 lines |
| `TypesUtils.lean` | ~4 lines |
| `Weakening.lean` | ~140 lines |
| `Preservation.lean` | ~170 lines |
| `Macros.lean` | ~25 lines |
| `metatheory.md` | ~120 lines |
| Examples (25 files) | ~210 lines (mostly macro updates) |

### Result

`lake build` succeeds (328 jobs). Zero `sorry`s in the codebase. All accepted examples
type-check, all rejected examples are still rejected. `extension_after_call` now faithfully
uses a `call` to `borrow`.
