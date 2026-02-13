# Changes Made on 2026-02-13

## Refactor: Uniform freshness checks across all TypeEnv components

Changed freshness checking from considering only `PathEnv.refs` to considering
all three TypeEnv components (pathEnv, varEnv, siteEnv). This ensures that
fresh reference IDs generated during type checking don't collide with any
existing ref in the environment.

### Types.lean — New definitions
- `getTypeRef` — extracts the `Aref` from a `MoveType` (if it's a `.ref`)
- `collectVarEnvRefs` — collects all `Aref` values from VarEnv types
- `collectSiteEnvRefs` — collects all `Aref` values from SiteEnv types
- `freshRefInEnv` — propositional freshness across all three components
- `freshRefInEnvBool` — boolean version for algorithmic checking
- `nextFreshRefInEnv` — computes fresh ref by finding max refid across all components

### TypeChecking.lean (relational rules)
Changed `freshRef r env.pathEnv` → `freshRefInEnv r env` in rules:
- `let_bind_copy_ref`
- `let_bind_borrowImm`
- `let_bind_borrowMut`
- `let_bind_borrowField`
- `let_bind_borrowMutField`
- `let_bind_freeze`
- `var_assign_valid`

### TypeCheckingAlgorithmic.lean (algorithmic checker)
Changed `nextFreshRef env.pathEnv` → `nextFreshRefInEnv env` and
`freshRefBool r env.pathEnv` → `freshRefInEnvBool r env` in all corresponding cases.

### AlgorithmicTypingSoundness.lean
Updated soundness proofs to use `nextFreshRefInEnv_fresh`, `nextFreshRefInEnv_not_root`,
`nextFreshRefInEnv_not_varRef` in place of the old PathEnv-only versions.

### TypesUtils.lean — New freshness lemmas
- `freshRefInEnv_iff_freshRefInEnvBool` — bridge between Prop and Bool versions
- `nextFreshRefInEnv_fresh` — `nextFreshRefInEnv` produces a ref fresh in all components
- `nextFreshRefInEnv_not_root` — result is never `.root`
- `nextFreshRefInEnv_is_refid` — result is always `.refid n`
- `nextFreshRefInEnv_not_varRef` — result is never `.varRef v`
- Preservation lemmas for `TypeEnv.WellFormed` updated accordingly

### TypeSoundness.lean
- Updated inversion lemmas (`inv_copy`, `inv_borrowImm`, `inv_borrowMut`, `inv_freeze`,
  `inv_assign`) to extract the new `freshRefInEnv`/`freshRefInEnvBool` hypotheses
- Updated `inv_ret` to use `MoveType.compatible` (matches updated relational rule)
- Added `preservation_copy_ref` scaffold (with one `sorry` for `rmap_paths`)

## Fix: Update examples for new refid generation

Since `nextFreshRefInEnv` considers all env components (not just pathEnv.refs),
it produces larger refid values. Updated all affected examples:

### extension_after_call.lean
- `fn_borrow` returnType: `.refid 2` → `.refid 4`
- `fn_write` returnType: `.refid 1` → `.refid 4`

### alias_write_after_join.lean
- Local `var_y` refid: `42` → `2`
- Label `l3` env refids: `.refid 1` → `.refid 4`, `.refid 2` → `.refid 5`
- Updated `t_varEnv_fresh` and `t_l3_varEnv_fresh` proofs

### subtree_writes_release.lean
- Label `l3` env refids: `.refid 1` → `.refid 5`, `.refid 2` → `.refid 7`, `.refid 3` → `.refid 8`
- Updated `t_l3_varEnv`, `t_l3_pathEnv`, and all freshness proofs

### mutable_borrows_are_not_unique.lean
- Added `set_option maxRecDepth 4096` for both `fields_check` and `fields_write_check`
  theorems (functions too large for default kernel reduction depth)

### deref_borrow_field_ok.lean
- Updated `borrowField` refid: `.refid 1` → `.refid 2` (since varEnv refs now counted)
- Updated `freshRefInEnv` proofs to handle new three-component freshness

### imm_borrow_after_mut.lean
- Added relational well-typedness proof `r_welltyped` with `check_fun_sound` bridge
- Updated freshness proofs for the new `freshRefInEnv` requirements
