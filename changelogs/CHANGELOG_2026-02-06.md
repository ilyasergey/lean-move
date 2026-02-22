# Changes Made on 2026-02-06

## Summary
1. Proved the pack case of `check_letBind_sound` and fixed all helper lemmas so TypeCheckingProofs.lean compiles as part of the build.
2. Fixed a bug in the assign valid typing rule (reversed `update_with_extension` arguments) and proved the assign case soundness.
3. Proved relational welltyped theorems for three expressivity examples via `check_fun_sound`.

## Changes

### LeanMove/Checker/TypeCheckingProofs.lean

**Fixed helper lemmas (all now compile):**

- `eraseDups_length_le` - Fixed parsing issue with nested `have :=` inside `by` blocks
- `filter_length_eq_implies` - Fixed `List.not_mem_nil` usage (`nomatch` instead)
- `nodup_of_length_eraseDups` - Removed unused simp arg
- `nodup_snd_pair_absurd` - Fixed `List.not_mem_nil` and `List.mem_map_of_mem` (`f` is implicit in this Lean version, use `(f := Prod.snd)`)
- `list_lookup_filter_ne` - Rewrote to use `fun p => p.fst != k` predicate (matching `AssocMap.insert`); used `split` on `List.filter`/`List.lookup` matches. Key insight: `List.lookup a ((k,v)::es)` checks `a == k` (search key on LEFT)
- `lookup_insert_ne` - Rewrote using `split` on `List.lookup` match
- `lookup_insert_eq` - Removed unused simp arg
- `foldlM_pack_preserves` - Fixed nil case (`Option.some.injEq` + `subst`); cons case uses `cases hlk : lookup siteEnv hd.snd` instead of broken `split at hfold` + `rename_i`
- `foldlM_pack_sound` - Fixed nil case (`nomatch`); cons case uses `cases hlk` approach; used `f` instead of `hd.fst` in `| head =>` branch (since `hd` is substituted by `cases hmem`)

**Proved pack case sorry:**
- The sorry at the pack case of `check_letBind_sound` is now closed using `foldlM_pack_sound` and `check_fields_distinct_implies_fnames_nodup`

### LeanMove/Checker.lean
- Added `import LeanMove.Checker.TypeCheckingAlgorithmic` and `import LeanMove.Checker.TypeCheckingProofs` to include proofs in the build

### LeanMove/Structures/AssocMap.lean
- Minor tactic fixes: replaced `aesop` with `simp` in two places in `notIn_uniqueKeys_insert`

### LeanMove/Checker/TypeChecking.lean (relational rules)
- **Bug fix**: Swapped reversed `update_with_extension` arguments in `var_assign_valid` rule
  - Was: `update_with_extension .root r [.root_to_var x]` (z=.root, meaning .root = &r.path — nonsensical)
  - Now: `update_with_extension r .root [.root_to_var x]` (z=r, meaning r = &.root.path — matches borrowMut pattern)
  - With z=.root, all paths from .root were destroyed, making WellFormed unpreservable

### LeanMove/Checker/TypeCheckingAlgorithmic.lean (algorithmic checker)
- **Bug fix**: Same `update_with_extension` argument swap in the assign valid case to match the relational rule fix

### LeanMove/Checker/TypeCheckingProofs.lean (assign case)
- **Proved assign case** (both valid and invalid branches):
  - **Valid case**: Follows the borrowMut WellFormed preservation pattern — uses `update_with_epsilon_wellformed`, `update_with_extension_wellformed`, `garbage_collect_wellformed`, `SiteEnv.insert_refs_not_root`, `SiteEnv.delete_refs_not_root`, then applies the induction hypothesis
  - **Invalid case**: Uses `MoveType.eq_of_beq`, `VarEnv.lookup_type_is_fresh`, `VarEnv.update_refs_are_fresh`, `SiteEnv.delete_refs_not_root` for WellFormed preservation, then applies the relational `var_assign_invalid` rule

### LeanMove/Tests/expressivity/accepted/alias_writes.lean

**Fixed local type declarations and proved algorithmic type checking:**

- Fixed local variable types in all four functions (`borrow_local_twice`, `borrow_local_twice_reverse`, `borrow_local_and_copy_ref`, `borrow_local_and_copy_ref_reverse`): changed Aref from `.varRef var_a` to `.refid N` to match what `nextFreshRef` generates during algorithmic type checking
  - `var_x`: `.refid 1` (first `nextFreshRef` from `refs=[.root]`)
  - `var_y`: `.refid 2` (second `nextFreshRef` from `refs=[.refid 1, .root]`)
- Added `#eval` debug checks for all four functions (check_fun returns `true`)
- Added step-by-step `#eval` debug checks for `borrow_local_twice` (11 incremental prefix checks)
- Proved all four algorithmic check theorems via `by decide` (replacing `sorry`)
  - Note: `rfl` hits kernel reduction limits; `native_decide` incorrectly returns `false` (Lean 4 native code compilation issue with deeply nested closures); `decide` works correctly

**Root cause:** The `assign` rule for invalid variables requires exact type equality (`τ == τ'`) between the local's declared type (from `varEnv`) and the site's type (from `siteEnv`). The algorithmic checker generates fresh refs via `nextFreshRef` (producing `.refid N`), so local declarations must use matching `.refid N` values, not `.varRef`.

### LeanMove/Tests/expressivity/accepted/alias_writes.lean (welltyped proofs)

- Added `import LeanMove.Checker.AlgorithmicTypingSoundness`
- Changed algorithmic check theorems from `by decide` to `by rfl` (faster)
- Proved all four `_welltyped` theorems using `check_fun_sound` with `VarEnv.insert_refs_are_fresh` chains
- Pattern: `simp only [... List.filter, List.lookup] at hlookup; split at hlookup; injection; exact TypeEnv.init_wellformed _ _ fresh_proof`

### LeanMove/Tests/expressivity/accepted/extension_after_call.lean

**Fixed local types to match `nextFreshRef` output and proved welltyped theorems:**

- Added imports for `TypeCheckingAlgorithmic` and `AlgorithmicTypingSoundness`
- Changed param type from `.varRef var_b` to `.refid 0` in both `fn_borrow` and `fn_write`
- Fixed local types to match `nextFreshRef` output:
  - `fn_borrow`: var_tl = `.refid 1`, returnType = `.refid 2`
  - `fn_write`: var_tl = `.refid 1`, var_x = `.refid 2`, var_y = `.refid 2` (recycled after `garbage_collect` in `writeRef`), returnType = `.refid 1`
- Added `#eval` checks, algorithmic check theorems (`by rfl`), and welltyped theorems via `check_fun_sound`

### LeanMove/Tests/expressivity/accepted/alias_write_after_join.lean

**Proved welltyped theorem for multi-block function with custom PathEnv:**

- Added `import LeanMove.Checker.AlgorithmicTypingSoundness`
- Proved `t_varEnv_fresh`, `t_branch_varEnv_fresh`, `t_l3_varEnv_fresh` (VarEnv freshness)
- Proved `t_l3_pathEnv_wf` (PathEnv.WellFormed for custom paths function with refs_complete and varref_tracked)
- Proved `t_lenv_wf` (all 4 envs in lenv are well-formed) using `rfl` for concrete lookups and `beq = false` derivations for the exfalso case
- Proved `t_welltyped` via `check_fun_sound`

**Key proof techniques:**
- For concrete lookups on TypeEnv (which has a function-valued `paths` field), use `rfl` instead of `native_decide` (TypeEnv doesn't have DecidableEq)
- For exfalso (abstract label not in lenv): convert `l ≠ "lN"` to `(l == "lN") = false` via `cases h : l == "lN"`, then `simp [h3, h2, h1, h0, List.lookup]` reduces the match chain
- For PathEnv.WellFormed with negation hypotheses: `simp [hroot, hr1, hr2]` handles the if-chain reduction

## Technical Notes

### Key Lean 4 pitfalls discovered
1. `List.mem_map_of_mem` has `f` as an **implicit** argument (not explicit); use `(f := Prod.snd)` syntax
2. `List.not_mem_nil` applied with `_` gives `False` not `a ∉ []`; use `nomatch hmem` instead
3. `split at hfold` on `Option.bind` decomposes the outer match (some/none), not the inner application-specific match; use `cases hlk : lookup ...` to split on the inner match directly
4. After `cases hmem with | head =>`, the list head variable `hd` is substituted with the matched element, so `hd.fst` becomes invalid; use the explicit field/site variable names instead
5. `have := expr; omega` inside inline `by` blocks causes parsing failures; pull into separate `have` bindings
