# Changelog — 2026-02-15

## HasType strengthening and type soundness tests

### HasType made inductive and recursive (Defs.lean)
- `HasType` changed from a `def` (non-recursive, `True` for basic types) to an `inductive` type with recursive record typing.
- `ValueMatchesType` for `.basic bt` now requires `HasType v bt` instead of `True`.
- Added `HasType.record_fields`, `HasType.readPath_field`, `HasType.readRef_field_ne_none` lemmas.

### Decidable HasType check (InitState.lean)
- Added `hasType_bool` / `hasType_bool.checkFields` with mutual soundness proof `hasType_bool_sound` / `hasType_checkFields_sound`.
- Termination proofs via `sizeOf_assocMap_eq` and `sizeOf_lookup_le` helper lemmas.
- Added `checkArgsTyped` for argument type-checking.

### SoundnessAssumptions extended (InitState.lean)
- `SoundnessAssumptions` now takes `args : List Value` parameter.
- New fields: `args_typed` (basic-typed arguments have matching types), `params_nodup` (unique parameter names).
- `checkDecidable` now includes `check_fun_dec` and `checkFunEnv` (absorbed from `type_soundness_dec`), plus `checkArgsTyped` and `params_nodup`.
- `of_check` derives `lenv_wf` internally from `check_fun_dec` (no longer a separate hypothesis).
- Added `allocArgs_param_has_type` lemma connecting allocated argument values to their types.

### type_soundness_dec simplified (TypeSoundness.lean)
- Takes a single `SoundnessAssumptions.checkDecidable` hypothesis instead of separate `check_fun_dec` and `checkFunEnv` hypotheses.

### Preservation: pack and assign_valid HasType (Preservation.lean)
- `preservation_pack`: constructs `HasType.record` from field sites' types, proving packed values are well-typed. Uses strengthened `inv_pack` that extracts field-type correspondence and completeness.
- `preservation_assign_valid`: propagates `HasType` from site to variable assignment.
- `preservation_borrow` takes explicit `hht : HasType val τ` parameter (extracted from strengthened `var_consistent`).
- Replaced 8 `trivial` proofs with proper `HasType` constructions (intLit, copy, readRef, binop, etc.).
- Added `rmap_has_type` proofs to all preservation cases.

### TypeChecking rules strengthened (TypeChecking.lean)
- `let_bind_pack`: added completeness hypothesis `(∀ f, lookup fentries f ≠ none → ∃ a, (f, a) ∈ fields)`.
- `var_assign_valid`: added `lookup env.siteEnv a = some (.basic τ)` hypothesis.

### Algorithmic typing soundness (AlgorithmicTypingSoundness.lean)
- Added `foldlM_pack_complete` lemma proving pack completeness.
- Updated `check_letBind_sound` and `check_stmt_sound` for new typing rule hypotheses.

### Example files simplified
- `deref_borrow_field_ok.lean`: replaced ~330-line manual proof with 3-line `check_fun_dec_sound` proofs. Fixed M_t parameter ref from `.varRef var_this` to `.refid 0` (required by algorithmic checker's `isFreshRef_bool`).
- `borrow_in_loop_fixed_ok.lean`: replaced ~200-line manual proof with 3-line `check_fun_dec_sound` proof.

### Type soundness runtime tests (AllTests.lean)
- Added `type_soundness_dec` theorems for all accepted examples with basic-typed params:
  - `borrow_in_loop_fixed_ok.foo`
  - `alias_writes` (4 functions)
  - `alias_write_after_join.t` (true/false)
  - `imm_borrow_after_mut.direct`, `copy_and_freeze`
- All proofs are `by rfl` — fully computed by the kernel.
- Documented limitation: functions with ref-typed params cannot use `type_soundness_dec` (requires `params_basic`).

### Files changed
- `LeanMove/Typing/Soundness/Defs.lean` — HasType inductive, ValueMatchesType strengthened
- `LeanMove/Typing/Soundness/InitState.lean` — hasType_bool, SoundnessAssumptions, checkDecidable, allocArgs_param_has_type
- `LeanMove/Typing/Soundness/Preservation.lean` — pack/assign_valid HasType, rmap_has_type, trivial→HasType
- `LeanMove/Typing/TypeSoundness.lean` — simplified type_soundness_dec
- `LeanMove/Typing/TypeChecking.lean` — strengthened pack and assign rules
- `LeanMove/Typing/Algorithmic/AlgorithmicTypingSoundness.lean` — foldlM_pack_complete
- `LeanMove/Typing/Algorithmic/TypeCheckingAlgorithmic.lean` — updated for new rule hypotheses
- `LeanMove/Examples/Typechecking/litmus/accepted/deref_borrow_field_ok.lean` — simplified, refid fix
- `LeanMove/Examples/Typechecking/litmus/accepted/borrow_in_loop_fixed_ok.lean` — simplified
- `LeanMove/Examples/Runtime/AllTests.lean` — type soundness tests
