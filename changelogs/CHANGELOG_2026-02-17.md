# Changelog — 2026-02-17

## Summary of changes across three commits (8706f9d, 83bf05f, 9048c2c)

### 1. σ-injectivity, SiteEnvSubstEquiv, and weakening infrastructure (8706f9d)

**TypeEnv.subsumes extended** (`Types.lean`):
- Added `SiteEnvSubstEquiv σ envL.siteEnv env.siteEnv` as a field — σ-based matching
  of site environments (both sides have same keys; types related by `applySubstMoveType σ`)
- Added σ-injectivity on refs (`Function.InjOn σ` restricted to refids appearing in
  the environments) as a field
- Added `moveTypeRefNotRoot` field — σ maps non-root refs to non-root refs
- Total subsumes fields: 7 (identity_on_non_refid, VarEnvSubstEquiv, SiteEnvSubstEquiv,
  refs_map, injectivity, nonroot, path_inclusion)

**Algorithmic typing** (`TypeCheckingAlgorithmic.lean`, `AlgorithmicTypingSoundness.lean`):
- Added `siteenv_subst_equiv_bool` — boolean check for SiteEnvSubstEquiv
- Added `siteenv_subst_equiv_bool_sound` — soundness proof
- Extended `subsumes_bool` to check σ-injectivity via `eraseDups`-based nodup check
- Updated `subsumes_bool_implies_subsumes` for the full 7-field subsumes

**Weakening infrastructure** (new file `Weakening.lean`, 214 lines):
- Created `LeanMove/Typing/Soundness/Weakening.lean`
- Proved `TypeEnv.subsumes_trans` — transitivity of subsumes (σ composition)
- Proved terminal cases of `typecheck_stmt_weaken`: skip, jump, branch
- Remaining non-terminal cases left as sorry

**Other changes**:
- `ListUtils.lean`: Added `List.inj_on_of_nodup_map` helper
- `TypeChecking.lean`: Restricted `not_borrowed` to tracked refs (`r ∈ pathEnv.refs`)
- Removed `check_mutable_inputs_have_outbound` from call rule
- Updated test expectations for rejected examples

### 2. Sorry-free AlgorithmicTypingSoundness + Weakening expansion (83bf05f)

**AlgorithmicTypingSoundness.lean — eliminated 2 sorrys** (+147 lines):
- `computeRefSubst_keys_refid` — all substitution keys are `.refid n`
- `applySubstArefList_non_refid` — substitution is identity on non-refid arefs
- `applySubstMoveTypeList_eq` — bridges list-based and function-based substitution
- `MoveType_base_compatible_bool_sound` — boolean base compatibility implies relational
- `varenv_subst_equiv_bool_sound` — boolean VarEnvSubstEquiv implies relational
- File is now completely sorry-free

**Weakening.lean — major expansion** (77 → 700 lines):
- Added `moveTypeRefNotRoot_applySubst` helper for IH calls
- Proved all non-pathEnv-modifying cases: letBind (intLit, boolLit, unitLit, binop,
  copy, move), var_assign_invalid, skip, jump, branch, ret
- Remaining 13 sorrys are pathEnv-modifying cases (borrowImm, borrowMut, borrowField,
  borrowMutField, readRef, freeze, copy_ref, writeRef, assign_valid, release, call,
  pack, unpack)

**Defs.lean**: Added `lenv_wf : LabelEnv.WellFormed lenv` field to WellTypedState
(field 9b, needed for preservation_jump/branch)

**Types.lean**: Added `LabelEnv.WellFormed` definition

### 3. preservation_jump and preservation_branch (9048c2c)

**Preservation.lean** (+237 lines):

**`siteEnv_empty_from_subsumes`** — if `envL.subsumes env` and envL has empty siteEnv,
then env also has empty siteEnv (via SiteEnvSubstEquiv).

**`findBlock_spec`** — custom helper proving `findBlock blocks label = some block`
implies `block ∈ blocks ∧ block.label = label`. Written by induction since
`List.find?_some` has a different API in Lean 4.27.

**`preservation_jump`** (~45 lines):
- Inverts typing via `inv_jump` to get `envL`, `hlookup_lenv`, `hsubsumes`
- Case-splits on `findBlock` (none → contradiction via step semantics)
- Uses `findBlock_spec` for block membership → `blocks_typed` gives typing for block body
- Applies `typecheck_stmt_weaken` to weaken from envL to env
- Constructs WellTypedState with env unchanged — all siteEnv fields vacuously true
  (env.siteEnv empty from `siteEnv_empty_from_subsumes`)

**`preservation_branch`** (~110 lines):
- Inverts typing via `inv_branch`, extracts bool from `site_consistent` + `HasType.bool`
- Case-splits on bool value (true→l1, false→l2), then on findBlock
- Constructs `env' = {env with siteEnv := delete env.siteEnv c}`
- Applies weakening from envL to env' for the selected branch
- Both branches construct WellTypedState with env', identical structure

**Dispatcher updated**: Replaced sorry for `jump` and `branch` cases with calls to
`preservation_jump` and `preservation_branch`.

**Remaining dispatcher sorrys**: `ret` and `call` only.

### Files changed (cumulative)

| File | Lines changed |
|------|--------------|
| `AlgorithmicTypingSoundness.lean` | +254 |
| `Weakening.lean` | +700 (new file) |
| `Preservation.lean` | +256 |
| `Types.lean` | +20 |
| `Defs.lean` | +3 |
| `TypeCheckingAlgorithmic.lean` | +14/-5 |
| `TypeChecking.lean` | +6/-3 |
| `ListUtils.lean` | +23 |
| `InitState.lean` | +1 |
