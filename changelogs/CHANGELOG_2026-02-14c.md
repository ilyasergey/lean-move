# Changes Made on 2026-02-14 (Part 3)

## Prove `initState_safe` and package `SoundnessAssumptions`

Completed the `initState_safe` theorem (all 17 WellTypedState fields + StackSafe)
and refactored the `type_soundness` theorem to use a `SoundnessAssumptions` structure.

### `PathEnv.WellFormed`: new `from_untracked_to_root_empty` field

Added to `TypesUtils.lean`:
```
from_untracked_to_root_empty : ∀ u, u ∉ pe.refs → u ≠ v → pe.paths (u, v) = .empty
```
Paths from untracked refs are always `.empty`. Proved for `PathEnv.init` and
preserved by `update_with_extension`, `delete_ref_node`, `garbage_collect`,
`consume_ref_transfer`.

Updated `DecidableTypeEnv.lean` with boolean check and soundness proof.

### Helper lemmas for `initState_safe`

- `init_fun_varEnv` lemmas: `valid_in_params`, `valid_not_local`, `invalid_is_local`
- `addLocals` lemmas: `preserves_lookup`, `local_some_none`
- `Heap.alloc` lemmas: `nextLoc`, `read_same`, `read_ne`, `preserves_bound`
- `allocArgs` lemmas: `preserves_old_read`, `heap_loc_bound'`, `param_allocated`

### `initState_safe` proof structure

Three cases from `initState`:
1. `allocArgs` fails → `.error arityMismatch` → trivially not `.danglingRef`
2. No blocks → `.error unknownFunction` → trivially not `.danglingRef`
3. `.running` → construct `WellTypedState` with empty `rmap` (`fun _ => none`)

Key proof techniques for the `.running` case:
- `rmap.map _ = none` makes `rmap_live`, `rmap_paths`, `root_path_coherence` vacuous
- `hno_ref_in_varEnv` (derived from `params_basic` + `VarEnvLookupCompatible`) makes
  `varEnv_refs_in_pathEnv` and `live_refs_unique` vacuous
- Empty `siteEnv` (from `lenv_empty_sites`) makes `site_consistent` and
  `siteEnv_refs_in_pathEnv` vacuous
- `no_paths_to_root`: for `u = .root`, paths(.root,.root) = ε; for `u ≠ .root`,
  `from_untracked_to_root_empty` gives `.empty` → contradiction
- `var_consistent`: valid params get heap locations via `allocArgs_param_allocated`
  and `addLocals_preserves_lookup`; invalid locals get `none` via `addLocals_local_some_none`
- `heap_loc_bound`: via `allocArgs_heap_loc_bound'`

### `SoundnessAssumptions` structure

Packages 5 non-typedness prerequisites for `type_soundness`:

| Field | Decidable | Why external |
|-------|-----------|-------------|
| `lenv_wf` | No (needs `LabelEnvDec`) | `typecheck_fun` doesn't constrain `PathEnv.WellFormed` |
| `params_basic` | Yes | Type checker is parametric in function signature |
| `heap_wf` | Yes | Runtime property, unknown to static checker |
| `lenv_empty_sites` | Yes | `TypeEnv.equiv` allows non-empty sites on both sides |
| `lenv_complete` | Yes | `hblocks_typed` is vacuously true for missing blocks |

- `SoundnessAssumptions.checkDecidable`: boolean check for the 4 decidable fields
- `SoundnessAssumptions.of_check`: soundness theorem (`lenv_wf` + `checkDecidable = true` → full structure)

### Updated theorem signatures

```lean
theorem type_soundness (f : FunDef) (lenv : LabelEnv) (funEnv : AssocMap Id FunDef)
    (args : List Value) (heap : Heap)
    (htyped : typecheck_fun f lenv)
    (hfunEnv : ∀ fname fdef, lookup funEnv fname = some fdef → ∃ lenv', typecheck_fun fdef lenv')
    (ha : SoundnessAssumptions f lenv heap) :
    ∀ n loc, Semantics.run n (initState f funEnv args heap) ≠ .error (.danglingRef loc)
```

### Files modified

1. **`LeanMove/Typing/TypesUtils.lean`**: `from_untracked_to_root_empty` field + preservation proofs
2. **`LeanMove/Typing/Algorithmic/DecidableTypeEnv.lean`**: boolean check + soundness for new field
3. **`LeanMove/Typing/TypeSoundness.lean`**: `SoundnessAssumptions`, helper lemmas, `initState_safe`, updated `type_soundness`
