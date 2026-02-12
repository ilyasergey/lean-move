# Preservation Proof Plan

## Problem

Two `sorry`s remain in `TypeSoundness.lean`:
1. `preservation` (line 533)
2. `initState_safe` (line 635)

## Key Issue: call/ret change function context

The current `preservation` returns `∃ env' rmap', WellTypedState m' env' lenv retType rmap'`
with the **same** `lenv` and `retType`. But:
- **call** pushes a callee frame with a different `lenv'` and `retType'`
- **ret** pops to the caller with yet another `lenv''` and `retType''`

## Required Structural Changes

### 1. Change `preservation` return type
```lean
∃ env' lenv' retType' rmap', WellTypedState m' env' lenv' retType' rmap'
```

### 2. Change `SafeExecState` — existentially quantify `lenv`/`retType`
```lean
def SafeExecState (state : ExecState) : Prop :=
  match state with
  | .running m => ∃ env lenv retType rmap, WellTypedState m env lenv retType rmap
  | .halted _ => True
  | .error (.danglingRef _) => False
  | .error _ => True
```

### 3. Add 4 fields to `WellTypedState`

| Field | Purpose | Used by |
|---|---|---|
| `blocks_typed` | All blocks in current frame type-check with their lenv envs | jump, branch |
| `lenv_empty_siteEnv` | lenv entries have empty siteEnv | jump, branch |
| `funEnv_typed` | Functions in funEnv are well-typed | call |
| `stack_safe` | After ret, restored caller frame is well-typed | ret |

The `stack_safe` field references `WellTypedState` recursively, but in a
strictly positive position (`∀ ... → ∃ ..., WellTypedState`), acceptable
for a `Prop`-valued structure.

### 4. Update downstream theorems
- `safe_step` — remove `lenv`/`retType` params, use existential SafeExecState
- `safe_run_no_danglingRef` — same
- `initState_safe` — return new SafeExecState
- `type_soundness` — use new SafeExecState

## Auxiliary Lemmas Needed

### A. Site consistency (siteStore ↔ siteEnv)
- `site_consistent_insert` — inserting matching (value, type) pair
- `site_consistent_delete_env` — removing entry from siteEnv
- `site_consistent_empty_siteEnv` — empty siteEnv is vacuously consistent

### B. Variable consistency (varStore ↔ varEnv)
- `var_consistent_weaken_siteEnv` — changing only siteEnv preserves var_consistent
- `var_consistent_update_invalidVar` — marking var as invalid
- `var_consistent_alloc` — after heap.alloc, old consistency preserved + new valid var

### C. Heap operations
- `heap_alloc_preserves_read` — alloc preserves reads at existing locations
- `heap_alloc_read_new` — reading newly allocated location succeeds
- `heap_alloc_preserves_readRef` — follows from above

### D. rmap_live / rmap_paths / siteEnv_refs_tracked
- `rmap_live_subset_refs` — if refs' ⊆ refs and heap unchanged
- `rmap_live_heap_alloc` — alloc only adds locations
- `siteEnv_refs_tracked_delete` — delete from siteEnv
- `siteEnv_refs_tracked_insert_basic` — insert .basic type
- `siteEnv_refs_tracked_insert_ref` — insert .ref type if r ∈ refs

### E. Stack safety through heap changes
- `stack_safe_heap_alloc` — alloc preserves stack_safe
- `stack_safe_heap_writeRef` — writeRef preserves stack_safe

## Preservation: 20 Cases Grouped

| Group | Cases | Key challenge |
|---|---|---|
| 1. Release | `release` | Only stmt changes; delete from siteEnv/pathEnv |
| 2. Simple site | `intLit`, `copy_val`, `readRef`, `freeze`, `binop`, `pack`, `unpack` | Insert/delete in siteStore↔siteEnv; heap/varStore unchanged |
| 3. Borrows | `borrowImm`, `borrowMut`, `copy_ref`, `borrowField`, `borrowMutField` | Extend rmap with new abstract ref; update pathEnv |
| 4. Variables | `move`, `assign_valid`, `assign_invalid` | varStore changes; for assign, heap.alloc |
| 5. writeRef | `writeRef` | Heap mutation; need check_outbound → rmap_live preserved |
| 6. Control flow | `jump`, `branch`×2 | Reset siteStore; need blocks_typed + lenv_empty_siteEnv |
| 7. Interprocedural | `call`, `ret` | Push/pop frame; need funEnv_typed + stack_safe |

## Implementation Order

1. Structural changes (new fields, new signatures) — compile with sorrys
2. Auxiliary lemmas (A–E)
3. Groups 1–2 (easy, ~10 cases)
4. Group 4 (variable cases)
5. Group 5 (writeRef)
6. Group 3 (borrows, rmap extension)
7. Group 6 (jump/branch)
8. Group 7 (call/ret)

Commit after each group compiles.
