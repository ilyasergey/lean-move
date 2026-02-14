# Changes Made on 2026-02-14

## Add decidable TypeEnv well-formedness (`DecidableTypeEnv.lean`)

Introduced `TypeEnvDec` — a decidable version of `TypeEnv` where `PathEnv.paths`
uses `AssocMap` instead of a function. This allows well-formedness to be checked
algorithmically (`by rfl`) instead of requiring manual proofs, eliminating
~1100 lines of boilerplate across 8 example files.

### New file: `LeanMove/Typing/Algorithmic/DecidableTypeEnv.lean`

Core types:
- `PathEnvDec` — path environment with `AssocMap (Aref × Aref) (Regex PathElement)`
- `TypeEnvDec` — type environment using `PathEnvDec`
- `LabelEnvDec` — label environment mapping labels to `TypeEnvDec`

Conversions:
- `PathEnvDec.toPathEnv` — converts to `PathEnv` (self-loops → `ε`, missing → `empty`)
- `TypeEnvDec.toTypeEnv` — converts using `toPathEnv`
- `LabelEnvDec.toLabelEnv` — converts using `mapValues`

Boolean well-formedness checks with soundness proofs:
- `PathEnvDec.wellFormed_bool` / `wellFormed_bool_sound`
- `TypeEnvDec.wellFormed_bool` / `wellFormed_bool_sound`
- `LabelEnvDec.allWellFormed_bool`

Wrapper:
- `check_fun_dec f lenvDec` — checks WF, converts, calls existing `check_fun`
- `check_fun_dec_sound` — if `check_fun_dec` returns true, relational judgment holds

### New in `LeanMove/Structures/AssocMap.lean`
- `mapValues` — maps a function over AssocMap values
- `lookup_mapValues` — `lookup (mapValues m f) k = (lookup m k).map f`

### Updated 8 example files

All accepted expressivity examples now use the simplified pattern:
```lean
def t_lenvDec : LabelEnvDec := ...
theorem t_check : check_fun_dec t t_lenvDec = true := by rfl
theorem t_welltyped : ∃ lenv, typecheck_fun t lenv := ⟨_, check_fun_dec_sound _ _ t_check⟩
```

Eliminated all `*_varEnv_fresh`, `*_pathEnv_wf`, `*_env_wf`, `*_lenv_wf` manual
proofs and `#eval` debug statements from:
- `extension_after_call.lean` (2 functions)
- `multible_mutable_return_values.lean` (2 functions)
- `mutable_borrows_are_not_unique.lean` (2 functions)
- `imm_borrow_after_mut.lean` (2 functions)
- `alias_writes.lean` (4 functions)
- `extension_writes_after_join.lean` (4 labels, PathEnv.init)
- `alias_write_after_join.lean` (4 labels, custom PathEnv with 6 entries)
- `subtree_writes_release.lean` (4 labels, complex PathEnv with 20 entries)

### Performance note

For large PathEnvDec maps (>10 entries), use direct list construction `⟨[...]⟩`
instead of chained `insert` calls to avoid O(n²) filtering overhead during
elaboration (the `insert` function filters duplicates on each call).
