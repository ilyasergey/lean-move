# Changes Made on 2026-02-14 (Part 2)

## Prove `rmap_paths` for `preservation_borrowImm` — sorry eliminated

Completed the `preservation_borrowImm` proof by adding three new WellTypedState
invariants and using them to prove the `rmap_paths` field. The borrowImm case is
now fully sorry-free.

### Three new WellTypedState invariants (fields 15–17)

- **`rmap_root_none`**: `rmap.map .root = none` — `.root` is never mapped in rmap
- **`no_paths_to_root`**: the only path to `.root` is the self-loop from `.root` itself
- **`root_path_coherence`**: if PathEnv records a path from `.root` to ref `v` via
  `.root_to_var y` followed by field elements, and `v` maps to the same heap location
  as variable `y`, then `v`'s concrete field path equals `fieldPathOf` of those elements

### New reusable lemma: `rmap_paths_update_with_borrow`

Standalone lemma for proving `rmap_paths` after `update_with_extension r .root
[.root_to_var x] (update_with_epsilon r r pe)` with `rmap'(r) = (loc, [])`.

Four-case analysis:
- **(r, r)**: self-loop ε — trivial
- **(r, old)**: Brzozowski derivative semantics + `root_path_coherence`
- **(old, r)**: `no_paths_to_root` makes hypothesis vacuous (or `rmap_root_none`)
- **(old, old)**: paths unchanged → delegates to old `rmap_paths`

### Preservation of new invariants across all 11 existing cases

| Case | Pattern |
|------|---------|
| intLit, copy_val, binop, pack, heap_alloc | Pass-through (pathEnv/rmap/varStore unchanged) |
| move | pathEnv/rmap unchanged; `varStore(x) → some none` makes root_path_coherence vacuous for `y = x` |
| readRef, release | `delete_ref_node`: paths to/from deleted ref become `.empty` (False) |
| copy_ref | `update_with_epsilon`: `s_orig ≠ .root` from varEnv; paths(.root, t) = paths(.root, s_orig) |
| assign_valid | `garbage_collect` = `delete_ref_node`; fresh heap alloc makes `loc_v ≠ loc_y` → vacuous |
| assign_invalid | pathEnv unchanged; fresh heap alloc → vacuous |
| borrowImm | Full proof via `rmap_paths_update_with_borrow` + extend/concat/derivative analysis |

### Key technique: Brzozowski derivative as definitional equality

`interpret_regex (.deriv re a) s` is *definitionally* equal to `interpret_regex re (a :: s)`
in the Regex definition (line 90). This avoids needing a separate lemma — just
`have hp' : interpret_regex re (a :: s) := hp` leverages the definitional equality.

### Key technique: `unfold pe' update_with_extension`

For hypotheses involving `pe'` (a local `let` binding), `unfold update_with_extension`
alone fails because `unfold` can't see through let bindings. The fix is
`unfold pe' update_with_extension`, which first unfolds the let binding, then the definition.
