# Changelog — 2026-02-18c

## Prove `preservation_ret`: eliminate `ret` sorry from the preservation theorem

### Summary

Completed the preservation proof for the `ret` (return) statement case. This is the first of the two
remaining stack-manipulating cases (ret and call). The proof restores the caller's `WellTypedState`
from the `StackSafe` invariant, bridging callee return values to the caller's result sites via
`ReturnValsWellTyped` and `RefMap.extendWithReturns`.

### Changes spanning last two commits (since b6a2509)

#### New definitions in Defs.lean

| Definition | Purpose |
|-----------|---------|
| `MoveType.toParamType` | Converts `MoveType` to `ParamType` for function signature bridging |
| `ReturnValsWellTyped` | Predicate: returned values match caller's result site types (heap-dependent for refs) |
| `RefMap.extendWithReturns` | Extends RefMap with output ref mappings from returned ref values |
| `RefMap.extendWithReturns_preserves` | Preservation: old ref mappings unchanged if ref not used by any result site |
| `RefMap.extendWithReturns_preserves_none` | None preservation: unmapped refs stay unmapped if not used by result sites |
| `RefMap.extendWithReturns_values` | Dichotomy: mapped value came from original rmap OR from a returned value |
| `WellTypedState.funEnv_sig_consistent` | New field 22: bridges `env.funEnv` (FunSig) with `frame.funEnv` (FunDef) |

#### Revised StackSafe (Defs.lean)

Redesigned `StackSafe` to inline ~28 fields from `WellTypedState` into each stack frame, with two key restrictions:
- `site_consistent` restricted to `s ∉ ri.resultSites` (result sites not yet populated)
- `rmap_has_type` restricted to refs NOT from result sites (output refs unmapped in callerRmap)
- Universal quantifier: given `ReturnValsWellTyped` return values, produces full `WellTypedState`

#### New file: StackSafeUtils.lean (913 lines)

| Lemma | Purpose |
|-------|---------|
| `stackSafe_heap_alloc` | StackSafe preserved through heap allocation |
| `stackSafe_heap_writeRef` | StackSafe preserved through heap write |
| `derive_returnValsWellTyped` | Bridges callee site consistency to caller `ReturnValsWellTyped` |
| `returnVals_site_consistent` | Site consistency for result sites after `bindReturnValues` + `extendWithReturns` |
| `extendWithReturns_new_mapping_type` | If new mapping not in original rmap, some site provided it with well-typed heap value |
| `ewr_step_ref` | One-step reduction for `extendWithReturns` when site type is ref |

#### preservation_ret proof structure (Preservation.lean)

1. Extract from step: `collectSiteValues`, stack pop, `bindReturnValues`
2. Extract from typing: `inv_ret` gives 4 return safety conditions
3. Extract from StackSafe: caller env, lenv, retTypes, rmap + all inlined fields
4. Derive `ReturnValsWellTyped` via `derive_returnValsWellTyped`
5. Construct `rmap'` via `RefMap.extendWithReturns` for output ref mappings
6. Prove all WellTypedState fields for restored caller frame:
   - `site_consistent`: non-result sites from StackSafe, result sites via `returnVals_site_consistent`
   - `rmap_has_type`: old refs from StackSafe, new output refs via `extendWithReturns_new_mapping_type`
   - Other fields: transferred directly from StackSafe inlined fields

#### Key simplification: removed Nodup requirement

Restructured `extendWithReturns_new_mapping_type` with a stronger induction hypothesis
(`rmap.map r = some (loc, path) ∨ ∃ ...`) that eliminates the need for both `List.Nodup sites`
and the site-uniqueness precondition. Uses `Or.elim` term-mode pattern to avoid Lean 4 parser
conflicts with `rcases` inside `cases ... with` blocks.

### Other changes

| File | Change |
|------|--------|
| `MoveLight.lean` | Added `MoveType.toParamType` |
| `InitState.lean` | Added `funEnv_sig_consistent` to `initState_safe`; `funEnv_sig` field in `SoundnessAssumptions` |
| `SafeExec.lean` | Updated `StackSafe` usage for new signature (added `retTypes` parameter) |
| `TypeSoundness.lean` | Updated `type_soundness` / `type_soundness_dec` for new `StackSafe` + `SoundnessAssumptions` fields |
| `Preservation.lean` | Added `funEnv_sig_consistent` to all existing WellTypedState constructions; wired `preservation_ret` into dispatcher |

### File stats

| File | Changes |
|------|---------|
| `Defs.lean` | +261 (new definitions, revised StackSafe, new WTS field) |
| `StackSafeUtils.lean` | +913 (new file) |
| `Preservation.lean` | +362/-280 (preservation_ret + funEnv_sig_consistent in all cases) |
| `InitState.lean` | +20/-6 |
| `TypeSoundness.lean` | +14/-3 |
| `MoveLight.lean` | +6 |
| `SafeExec.lean` | +1/-1 |
| **Total** | **+1577/-290** across 7 files |

### Result

The `ret` case in the preservation theorem is now fully proved and wired into the dispatcher.
Only one `sorry` remains in `Preservation.lean`: the `call` case. Build succeeds (300/300 jobs).
