# Changelog — 2026-02-17c

## Fix call typing rule: bidirectional `extend_with_star`, output population, new rule shape

### Summary

Redesigned the `call` typing rule to fix three fundamental bugs that made it
unusable for functions returning reference-typed values.

### Bug fixes

**Bug 1: Contradictory preconditions removed.**
The old rule required both `all_fresh_sites env as` (output sites NOT in siteEnv)
and `types_conform env.siteEnv as rets` (output sites IN siteEnv). These were
mutually contradictory for any non-empty output list.

**Bug 2: Output population added.**
New `populate_call_outputs` function inserts output sites into siteEnv with types
derived from the function's return type list. For reference-typed returns, fresh
abstract refs are allocated and added to pathEnv. This ensures
`call_connect_inputs_outputs` has output refs to work with (previously `mo=[]`,
`io=[]` because outputs were fresh).

**Bug 3: `extend_with_star` made bidirectional.**
Previously only created incoming paths TO `target`: `paths(u, target) = G(u, source) · .*`.
Now also creates outgoing paths FROM `target`: `paths(target, v) = .* · G(source, v)`.
The self-loop guard (`u = target ∧ v = target → ε`) is checked first.

### New definitions (TypeChecking.lean)

- **`all_refs_fresh_in_env`** — all refs in a list are fresh in the full env
- **`populate_call_outputs`** — recursive function walking `as`, `rets`, `outRefs`
  in lockstep; basic returns insert `.basic bt`, reference returns insert
  `.ref bt r bk` and add `r` to pathEnv via `update_with_epsilon`

### New call rule shape

```
| call : ∀ ... (outRefs : List Aref) (env' : TypeEnv) ...,
    lookup env.funEnv fnName = some ⟨params, rets⟩ →
    types_conform env.siteEnv bs params →
    all_fresh_sites env as →
    all_refs_fresh_in_env env outRefs →
    List.Nodup outRefs →
    populate_call_outputs env as rets outRefs = some env' →
    check_mutable_inputs_isolated env bs →
    typecheck_stmt lenv (call_connect_inputs_outputs env' as bs) cont retType →
    typecheck_stmt lenv env (.call as fnName bs cont) retType
```

Key change: `call_connect_inputs_outputs` operates on `env'` (populated env),
not `env` (original). This means `mo`/`io` filterMaps now find the output refs.

### Algorithmic checker updates (TypeCheckingAlgorithmic.lean)

- **`countRefReturns`** — count reference-typed returns
- **`generateFreshRefs`** — generate sequential fresh refids starting from `nextFreshRefInEnv`
- **`all_refs_fresh_in_env_bool`** — boolean check for fresh refs
- Algorithmic call case: generates fresh refs, calls `populate_call_outputs`,
  then `call_connect_inputs_outputs` on the populated env

### Proof updates

- **AlgorithmicTypingSoundness.lean**: Call case updated for new rule shape; 2 new
  sorrys for `generateFreshRefs` freshness and nodup lemmas
- **TypesUtils.lean**: `call_connect_inputs_outputs_wf` signature simplified
  (no longer requires `hfresh`); new `populate_call_outputs_wf` lemma (sorry);
  both WF lemmas need proofs for `extend_with_star` preservation
- **Preservation.lean**: `inv_call` updated to extract `outRefs`, `env'`, and
  `populate_call_outputs` proof from new rule

### Sorry status

| File | Sorrys | Notes |
|------|--------|-------|
| `TypesUtils.lean` | 2 | `populate_call_outputs_wf`, `call_connect_inputs_outputs_wf` |
| `AlgorithmicTypingSoundness.lean` | 1 | freshness/nodup for `generateFreshRefs` |
| `Weakening.lean` | 1 | `call` case |
| `Preservation.lean` | 1 | dispatcher (`ret`, `call`) |

### Files changed

| File | Lines changed |
|------|--------------|
| `TypeChecking.lean` | +52/-2 |
| `Types.lean` | +3/-1 |
| `TypeCheckingAlgorithmic.lean` | +24/-6 |
| `AlgorithmicTypingSoundness.lean` | +25/-10 |
| `TypesUtils.lean` | +10/-19 |
| `Preservation.lean` | +9/-5 |

---

## Extract 6 large cases from `typecheck_stmt_weaken` into lemmas (Weakening.lean)

### Summary

Extracted 6 large induction case proofs (>80 lines each) from
`typecheck_stmt_weaken` into standalone private theorems. Reduces the main
theorem from ~1139 lines to ~517 lines.

### Infrastructure

- **`WeakenIH`** — type abbreviation for the induction hypothesis, capturing all
  10 parameters (subsumes, WellFormed envL', WellFormed env', site_tracked,
  var_tracked, RefsUnique, paths_to_nm, paths_from_nm, self_loop_only_empty,
  root ∈ refs). Used to make extracted lemma signatures readable.

### Extracted lemmas

| Lemma | Case | Lines |
|-------|------|-------|
| `weaken_let_bind_borrowImm` | `let a = &x` | ~116 |
| `weaken_let_bind_borrowMut` | `let a = &mut x` | ~101 |
| `weaken_let_bind_borrowField` | `let af = &a.T::f` | ~101 |
| `weaken_let_bind_borrowMutField` | `let af = &mut a.T::f` | ~85 |
| `weaken_let_bind_freeze` | `let c = freeze(a)` | ~130 |
| `weaken_var_assign_valid` | `x = a` (valid assign) | ~120 |

Each case in the main theorem is now a single `exact weaken_*` call.

### File stats

- `Weakening.lean`: +851/-649 lines (net +202, from 2803 to 3005 lines)
- Main theorem: 1139 → 517 lines
- 6 extracted lemmas: ~810 lines total
