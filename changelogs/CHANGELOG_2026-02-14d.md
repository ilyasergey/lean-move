# Changes Made on 2026-02-14 (Part 4)

## Refactor TypeSoundness.lean into Soundness/ subfolder

Split the monolithic `TypeSoundness.lean` (~3524 lines) into a `Soundness/` subfolder
with 5 focused files, and added a fully decidable `type_soundness_dec` theorem.

### New file structure

```
LeanMove/Typing/
├── TypeSoundness.lean          ← 67 lines: type_soundness + type_soundness_dec
└── Soundness/
    ├── Defs.lean               ← WellTypedState, RefMap, helpers, StackSafe (~350 lines)
    ├── Progress.lean           ← no_danglingRef_progress (~210 lines)
    ├── Preservation.lean       ← inversion + preservation cases + dispatcher (~2250 lines)
    ├── SafeExec.lean           ← SafeExecState, safe_step, safe_run (~110 lines)
    └── InitState.lean          ← SoundnessAssumptions, initState_safe (~640 lines)
```

### Import dependency graph

```
Defs.lean  (imports: TypeChecking, TypesUtils, Smallstep)
  ├── Progress.lean
  ├── Preservation.lean
  └── SafeExec.lean (imports Progress + Preservation)
      └── InitState.lean (imports SafeExec)
SafeExec + InitState + DecidableTypeEnv → TypeSoundness.lean
```

### New in `DecidableTypeEnv.lean`

- **`check_fun_dec_lenv_wf`**: extracts well-formedness from `check_fun_dec`
- **`FunTypingEnv`**: `AssocMap Id LabelEnvDec` — decidable typing environments for functions
- **`checkFunEnv`**: boolean check that every function in `funEnv` is well-typed
- **`checkFunEnv_sound`**: soundness — `checkFunEnv = true → ∀ fname fdef, lookup funEnv fname = some fdef → ∃ lenv', typecheck_fun fdef lenv'`

### `type_soundness_dec` — fully decidable soundness theorem

```lean
theorem type_soundness_dec (f : FunDef) (lenvDec : LabelEnvDec)
    (funEnv : AssocMap Id FunDef) (fte : FunTypingEnv)
    (args : List Value) (heap : Heap)
    (hcheck : check_fun_dec f lenvDec = true)
    (hfunEnv : checkFunEnv funEnv fte = true)
    (hdec : SoundnessAssumptions.checkDecidable f lenvDec.toLabelEnv heap = true) :
    ∀ n loc, Semantics.run n (initState f funEnv args heap) ≠
      .error (.danglingRef loc)
```

All three hypotheses are decidable boolean checks. The proof reduces to the
relational `type_soundness` via `check_fun_dec_sound`, `checkFunEnv_sound`,
`check_fun_dec_lenv_wf`, and `SoundnessAssumptions.of_check`.

### Files modified

1. **`LeanMove/Typing/Soundness/Defs.lean`** (new)
2. **`LeanMove/Typing/Soundness/Progress.lean`** (new)
3. **`LeanMove/Typing/Soundness/Preservation.lean`** (new)
4. **`LeanMove/Typing/Soundness/SafeExec.lean`** (new)
5. **`LeanMove/Typing/Soundness/InitState.lean`** (new)
6. **`LeanMove/Typing/Algorithmic/DecidableTypeEnv.lean`** (added 4 new declarations)
7. **`LeanMove/Typing/TypeSoundness.lean`** (rewritten: thin file with 2 theorems)
