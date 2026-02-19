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
