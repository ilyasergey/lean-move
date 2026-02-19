# Changelog — 2026-02-19b

## Change subsumption refs check from equality to List.Perm

### Summary

Changed `TypeEnv.subsumes` refs field from exact list equality (`=`) to permutation equivalence
(`List.Perm`). This fixes two commented-out type-soundness theorems in AllTests.lean
(`ext_writes_join_t_true/false_no_danglingRef`) that failed because different branches produce
different substitution orderings, making exact equality impossible when `.refid` placeholder refs
appear in `pathEnv.refs`.

### Problem

The `extension_writes_after_join` test has a join point (l3) whose varEnv contains `.refid 1` and
`.refid 305` from two branches. For `checkDecidable` to pass, these refs must be in l3's
`pathEnv.refs`. However, `subsumes_bool` checked refs via exact list equality (`==`) after applying
substitution σ. Since each branch produces a different σ, the mapped refs appear in different
orders — one branch satisfies `==` but the other fails.

### Solution

Replace exact equality with `List.Perm` (permutation), which is order-independent.

### Key changes

#### Types.lean
- `TypeEnv.subsumes` refs field: `envL.pathEnv.refs.map σ = env.pathEnv.refs` →
  `(envL.pathEnv.refs.map σ).Perm env.pathEnv.refs`

#### TypeCheckingAlgorithmic.lean
- `subsumes_bool` refs check: replaced `mapped == env.pathEnv.refs` with
  `mapped.length == target.length && mapped.eraseDups.length == mapped.length &&
   mapped.all (fun r => target.contains r)`

#### AlgorithmicTypingSoundness.lean
- Added helper lemma `perm_of_nodup_nodup_subset_length_eq`: derives `List.Perm` from both lists
  being nodup + same length + subset
- Updated `subsumes_bool_implies_subsumes` to produce `Perm` from the boolean checks

#### Weakening.lean (~50 proof sites)
- 4 function signatures changed: `not_borrowed_weaken`, `check_outbound_weaken`,
  `update_with_epsilon_path_inclusion`, `populate_call_outputs_subsumes`
- `rw [hrefs]` for membership → `hrefs.mem_iff.mp`/`hrefs.symm.mem_iff.mp`
- `rw [map_filter_ne ..., hrefs]` → `rw [map_filter_ne ...]; exact hrefs.filter _`
- `congr 1; rw [..., hrefs]` → `apply List.Perm.cons; rw [...]; exact hrefs`
- `subsumes_trans`: `rw [hrefs1, hrefs2]` → `exact (hrefs1.map σ2).trans hrefs2`

#### extension_writes_after_join.lean
- Added custom `t_l3_pathEnvDec` with `refs := [.root, .refid 1, .refid 305]` and empty paths
- Updated l3 entry in `t_lenvDec` to use `t_l3_pathEnvDec`

#### AllTests.lean
- Uncommented `ext_writes_join_t_true_no_danglingRef` and `ext_writes_join_t_false_no_danglingRef`

### File stats

| File | Changes |
|------|---------|
| `Types.lean` | 1 line |
| `TypeCheckingAlgorithmic.lean` | ~5 lines |
| `AlgorithmicTypingSoundness.lean` | ~50 lines |
| `Weakening.lean` | ~50 proof site updates |
| `extension_writes_after_join.lean` | ~8 lines |
| `AllTests.lean` | ~12 lines |

### Result

`lake build all` succeeds (328 jobs). All type-soundness tests pass including the two
previously commented-out theorems. No new sorrys introduced.
