# Changelog — 2026-02-19

## FunTypeSafe + fold hfunSig into checkDecidable

### Summary

Introduced `FunTypeSafe` — a bundled predicate that captures all per-function properties needed
for callee `WellTypedState` construction during `preservation_call`. Strengthened `checkFunEnv`
from 1 per-function check to 7, extended `checkDecidable` with a 15th conjunct (`checkFunEnvSigs`),
and proved a new `checkFunEnv_sound` that returns `FunTypeSafe`. This eliminated the separate
`hfunSig` parameter from `type_soundness_dec` and `of_check`.

### New definitions

| Definition | File | Purpose |
|-----------|------|---------|
| `FunTypeSafe` | Defs.lean | 11-conjunct predicate: typecheck_fun + lenv WellFormed + empty siteEnv + var refs tracked/unique + funEnv sig matching + lenv complete + funEnv consistent + paths from/to non-member + self-loop |
| `checkFunEnvSigs` | DecidableTypeEnv.lean | Boolean: all lenv entries' funEnv signatures match runtime FunDef params/returnType |
| `checkFunEnvSigs_sound` | DecidableTypeEnv.lean | Soundness: derives sig matching from `checkFunEnvSigs = true` |
| `toLabelEnv_lookup_some` | DecidableTypeEnv.lean | Helper: LabelEnvDec lookup → LabelEnv lookup (made non-private) |
| `any_beq_implies_list_lookup` | DecidableTypeEnv.lean | Helper: `List.any (beq l)` → `List.lookup l` succeeds |

### Key changes

#### DecidableTypeEnv.lean
- Extended `checkFunEnv` from 1 check (`check_fun_dec`) to 7 per-function checks:
  `check_fun_dec`, empty siteEnv, lenv completeness, var refs tracked, var refs unique,
  funEnv consistency, funEnv signatures
- Moved `checkFunEnvConsistent` + soundness BEFORE `checkFunEnv` (dependency order)
- Removed old `checkFunEnv_sound` (moved to InitState.lean with stronger return type)

#### Defs.lean
- Added `FunTypeSafe` predicate (11 conjuncts)
- Changed `funEnv_typed` in `WellTypedState` and `StackSafe` to return `FunTypeSafe fdef funEnv`

#### InitState.lean
- Added `checkFunEnv_sound` returning `FunTypeSafe` (uses `split at hentry` + `rw [Bool.and_eq_true]`)
- Added `checkFunEnvSigs lenvDec funEnv` as 15th conjunct in `checkDecidable`
- Removed `hfunSig` parameter from `of_check`; derived `funEnv_sig` from `checkFunEnvSigs_sound`

#### TypeSoundness.lean
- Removed `hfunSig` parameter from `type_soundness_dec`
- Updated `.1` chain depth for 15 conjuncts

#### Preservation.lean / StackSafeUtils.lean / Weakening.lean
- Updated all `WellTypedState` and `StackSafe` constructions for new `FunTypeSafe`-returning `funEnv_typed`
- Weakening.lean: added 210+ lines for ret case return conditions proofs

### Technical notes

- `Bool.and_eq_true` in Lean 4 returns `Eq` not `Iff`: must use `rw` not `.mp`
- `split at hentry` avoids dependent elimination failures from `check_fun_dec` match expansion
- `next lenvDec _ =>` properly captures split value + equation (not `rename_i`)
- `checkFunEnvConsistent_sound` has grouped params `l1 l2 env1 env2` but FunTypeSafe needs
  interleaved `L envL L' envL'` — fixed with lambda wrapper

### File stats

| File | Changes |
|------|---------|
| `DecidableTypeEnv.lean` | +119/-29 |
| `Defs.lean` | +61/-10 |
| `InitState.lean` | +132/-66 |
| `Preservation.lean` | +65/-20 |
| `StackSafeUtils.lean` | +8/-4 |
| `Weakening.lean` | +237/-18 |
| `TypeSoundness.lean` | +20/-8 |
| **Total** | **+642/-155** across 7 files |

### Result

`type_soundness_dec` now takes 7 parameters (was 8). All 25 test theorems in AllTests.lean
pass without modification. Build succeeds (324 jobs). One `sorry` remains: `preservation_call`.

---

## preservation_call skeleton + infrastructure

### Summary

Extended `FunTypeSafe` with 4 new callee properties needed for `preservation_call`, extended
`checkFunEnv` with 4 corresponding boolean checks and proved their soundness, made `allocArgs`
helpers non-private, added `stackSafe_allocArgs`, wrote `inv_call` with all 8 premises, and
created the `preservation_call` proof skeleton with 2 sorrys (callee WellTypedState + StackSafe).

### New definitions / lemmas

| Definition | File | Purpose |
|-----------|------|---------|
| `stackSafe_allocArgs` | StackSafeUtils.lean | StackSafe preserved through allocArgs sequence |
| `inv_call` (extended) | Preservation.lean | Extracts all 8 premises from `typecheck_stmt.call` |
| `preservation_call` | Preservation.lean | Skeleton with 2 sorrys |

### Key changes

#### Defs.lean
- Extended `FunTypeSafe` with 4 new properties (15 conjuncts total):
  `params_nodup`, `param_refs_distinct`, `param_refs_not_root`, `entry_varEnv_exact`

#### DecidableTypeEnv.lean
- Extended `checkFunEnv` from 7 to 11 per-function checks (param nodup, ref distinct, not root, entry varEnv exact)

#### InitState.lean
- Made 12 `allocArgs`/`addLocals` helpers non-private
- Extended `checkFunEnv_sound` from 6→10 `Bool.and_eq_true` peeling; proves all 15 FunTypeSafe conjuncts

#### StackSafeUtils.lean
- Added `stackSafe_allocArgs`: induction on params using `stackSafe_heap_alloc` at each step

#### Preservation.lean
- Extended `inv_call` to extract all 8 premises (params, rets, outRefs, popEnv, sig, types_conform, fresh sites/refs, nodup, populate, isolated, continuation typed)
- Added `preservation_call` skeleton: simplifies step through 4 nested matches, extracts callee entry block, constructs calleeRmap, provides 2 sorry witnesses

### File stats

| File | Changes |
|------|---------|
| `Defs.lean` | +13 |
| `DecidableTypeEnv.lean` | +14 |
| `InitState.lean` | +56/-18 |
| `Preservation.lean` | +98 |
| `StackSafeUtils.lean` | +40 |
| **Total** | **+221/-18** across 5 files |

### Result

Build succeeds (289 jobs). 2 sorrys remain in `preservation_call`: callee WellTypedState + StackSafe construction.
