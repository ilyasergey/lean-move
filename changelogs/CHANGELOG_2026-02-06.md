# Changes Made on 2026-02-06

## Summary
1. Proved the pack case of `check_letBind_sound` and fixed all helper lemmas so TypeCheckingProofs.lean compiles as part of the build.
2. Fixed a bug in the assign valid typing rule (reversed `update_with_extension` arguments) and proved the assign case soundness.

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

## Technical Notes

### Key Lean 4 pitfalls discovered
1. `List.mem_map_of_mem` has `f` as an **implicit** argument (not explicit); use `(f := Prod.snd)` syntax
2. `List.not_mem_nil` applied with `_` gives `False` not `a ∉ []`; use `nomatch hmem` instead
3. `split at hfold` on `Option.bind` decomposes the outer match (some/none), not the inner application-specific match; use `cases hlk : lookup ...` to split on the inner match directly
4. After `cases hmem with | head =>`, the list head variable `hd` is substituted with the matched element, so `hd.fst` becomes invalid; use the explicit field/site variable names instead
5. `have := expr; omega` inside inline `by` blocks causes parsing failures; pull into separate `have` bindings
