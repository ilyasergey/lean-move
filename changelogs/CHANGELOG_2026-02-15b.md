# Changelog — 2026-02-15b

## Support ref-typed parameters in type soundness

Removed the `params_basic` restriction from `SoundnessAssumptions`, enabling
`type_soundness_dec` for functions with reference-typed parameters (e.g.,
`fn_borrow(arg: &mut Box)`, `M_t(this: &T)`).

### New definitions

- **`init_fun_pathEnv`** (Types.lean): Initial `PathEnv` that includes `.root`
  and all abstract refs from ref-typed params. For basic-param functions,
  definitionally equals `PathEnv.init` — all existing proofs unchanged.
- **`init_fun_pathEnvDec`** (DecidableTypeEnv.lean): Decidable counterpart.
- **`init_fun_pathEnv_basic`** (TypesUtils.lean): Lemma proving equivalence
  with `PathEnv.init` when all params are basic-typed.
- **`init_fun_varEnv_valid_in_params`** (TypesUtils.lean): Lemma connecting
  valid varEnv entries to param membership.

### SoundnessAssumptions changes (InitState.lean)

- Replaced `params_basic` + `args_typed` with:
  - **`args_compatible`**: Each argument matches its declared type — `HasType v bt`
    for basic params; `∃ loc path, v = .ref loc path ∧ heap.readRef loc path` has
    a well-typed value for ref params.
  - **`param_refs_distinct`**: Abstract refs in ref-typed params are pairwise distinct.
  - **`param_refs_not_root`**: No param ref is `.root`.
  - **`entry_varEnv_exact`**: Entry block varEnv matches `init_fun_varEnv` exactly.
- Updated `checkDecidable` with `checkArgsCompatible`, `checkParamRefsDistinct`,
  `checkParamRefsNotRoot`, `checkEntryVarEnvExact` (11 conjuncts total).
- Updated `of_check` soundness proof for all new fields.

### initState_safe proof (InitState.lean)

- Constructs `rmap` from ref-typed params mapping abstract refs to heap locations.
- **`nodup_filterMap_params_same_ref`**: Proves two params with the same abstract ref
  must have the same name (used for `live_refs_unique`).
- **`hreadRef_preserved`**: Reusable helper proving `heap'.readRef = heap.readRef`
  for rmap-mapped locations after `allocArgs`.
- All 21 `WellTypedState` fields proved for ref-param initial states, no sorrys.

### Typing infrastructure updates

- `typecheck_fun` (TypeChecking.lean): Uses `init_fun_pathEnv f` instead of `PathEnv.init`.
- `check_fun` (TypeCheckingAlgorithmic.lean): Same change.
- `check_fun_sound` (AlgorithmicTypingSoundness.lean): Same change.
- **No changes to Preservation.lean** — all ~67 sites using `varEnv_refs_in_pathEnv`
  and `siteEnv_refs_in_pathEnv` remain untouched.

### Example updates

- **`extension_writes_after_join.lean`**: Gave `var_a` and `var_b` distinct refids
  (`.refid 0` and `.refid 1`) to satisfy `param_refs_distinct`. Recomputed all
  lenvDec refids and pathEnv entries.
- All 6 ref-param example files updated to use `init_fun_pathEnvDec` in entry
  block lenvDec definitions.

### Type soundness theorems (AllTests.lean)

Added `type_soundness_dec` theorems for all 10 ref-param functions:
- `deref_borrow_field_ok.M_t` (immutable ref param)
- `extension_after_call.fn_borrow`, `fn_write` (mutable ref param)
- `extension_writes_after_join.t` (two mutable ref params, both branches)
- `multible_mutable_return_values.borrow`, `write` (mutable ref param)
- `mutable_borrows_are_not_unique.fields`, `fields_write` (mutable ref param)
- `subtree_writes_release.t` (mutable ref param, both branches)

All proofs are `by rfl` — fully computed by the kernel.

### Build target (lakefile.lean)

- Added `lake build all` target that builds core libraries, all examples, and
  runtime tests together.

### Files changed

- `LeanMove/Typing/Types.lean` — `init_fun_pathEnv`
- `LeanMove/Typing/TypesUtils.lean` — `init_fun_pathEnv_basic`, `init_fun_varEnv_valid_in_params`
- `LeanMove/Typing/TypeChecking.lean` — `PathEnv.init` → `init_fun_pathEnv f`
- `LeanMove/Typing/Algorithmic/TypeCheckingAlgorithmic.lean` — same
- `LeanMove/Typing/Algorithmic/AlgorithmicTypingSoundness.lean` — same
- `LeanMove/Typing/Algorithmic/DecidableTypeEnv.lean` — `init_fun_pathEnvDec`
- `LeanMove/Typing/Soundness/InitState.lean` — SoundnessAssumptions, checkDecidable, initState_safe
- `LeanMove/Typing/TypeSoundness.lean` — updated destructuring for 11 conjuncts
- 6 example files — lenvDec pathEnv updates, `extension_writes_after_join` refid changes
- `LeanMove/Examples/Runtime/AllTests.lean` — 10 new type soundness theorems
- `lakefile.lean` — `all` build target
