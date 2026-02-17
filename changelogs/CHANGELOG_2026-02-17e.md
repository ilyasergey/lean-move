# Changelog — 2026-02-17e

## Extract all remaining inline cases from `typecheck_stmt_weaken` (Weakening.lean)

### Summary

Extracted 11 more induction case proofs from `typecheck_stmt_weaken` into standalone
private theorems. Combined with the 6 previously extracted cases, all 17 non-terminal
induction cases (except `call`) are now extracted. The main theorem body is reduced
from ~517 lines to ~113 lines — every case is a single `exact weaken_*` delegation call.

### Newly extracted lemmas (no pathEnv change)

| Lemma | Case | Lines |
|-------|------|-------|
| `weaken_let_bind_intLit` | `let a = n` | ~40 |
| `weaken_let_bind_copy_val` | `let a = copy(x)` (basic) | ~40 |
| `weaken_let_bind_move` | `let a = move(x)` | ~50 |
| `weaken_let_bind_binop` | `let c = a ⊕ b` | ~50 |
| `weaken_var_assign_invalid` | `x = a` (invalid assign) | ~55 |

### Newly extracted lemmas (pathEnv-changing)

| Lemma | Case | Lines |
|-------|------|-------|
| `weaken_let_bind_readRef` | `let c = *a` | ~75 |
| `weaken_write_ref` | `*a = b` | ~80 |
| `weaken_release` | `release(a)` | ~55 |
| `weaken_let_bind_copy_ref` | `let a = copy(x)` (ref) | ~115 |

### Newly extracted lemmas (complex non-pathEnv)

| Lemma | Case | Lines |
|-------|------|-------|
| `weaken_let_bind_pack` | `let b = pack(fields)` | ~50 |
| `weaken_unpack` | `unpack fields b` | ~55 |

### Main theorem structure

All cases now follow the uniform pattern:
```
| constructor_name <pattern_vars> =>
    exact weaken_constructor_name lenv _ env <args> <hypotheses>
      hsub hwfL hwfE hsite_tracked hvar_tracked huniq
      hpaths_to_nm hpaths_from_nm hself_loop_only_empty hroot ih
```

Remaining inline cases: `skip` (1 line), `jump` (2 lines), `branch` (12 lines),
`ret` (9 lines), `abort` (3 lines), `call` (sorry).

### File stats

- `Weakening.lean`: +719/-425 lines (net +294, from 3005 to 3299 lines)
- Main theorem: 517 → 113 lines
- 11 new extracted lemmas: ~665 lines total
- Total extracted lemmas: 17 (all non-terminal cases except `call`)

### Files changed

| File | Lines changed |
|------|--------------|
| `Weakening.lean` | +719/-425 |
