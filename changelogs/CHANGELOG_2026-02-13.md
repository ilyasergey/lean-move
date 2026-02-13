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

## Fix: Swap `update_with_epsilon` argument order in `copy_ref`

The `copy_ref` typing rule was calling `update_with_epsilon s t pe` (z=s_orig,
x=t_fresh), which resets s_orig's paths using t's empty paths. The correct
call is `update_with_epsilon t s pe` (z=t_fresh, x=s_orig), which adds t to
refs and inherits s_orig's existing paths.

### Files changed
- **TypeChecking.lean**: swapped `update_with_epsilon s t` → `update_with_epsilon t s` in `let_bind_copy_ref`
- **TypeCheckingAlgorithmic.lean**: same swap in algorithmic copy_ref case
- **AlgorithmicTypingSoundness.lean**: updated soundness proof to use t's freshness properties
  (`nextFreshRefInEnv_not_root`, `nextFreshRefInEnv_not_varRef`)
- **TypeSoundness.lean**: updated `inv_copy`, `preservation_copy_ref` hypothesis and proof

## Prove `rmap_paths` for `preservation_copy_ref`

Proved the `rmap_paths` invariant for the copy_ref preservation case, handling
the 4-case analysis of `update_with_epsilon t s_orig pe`:

- **(t, t)**: self-loop via ε — trivially reflected since rmap'(t) = rmap(s_orig)
- **(t, r2)**: paths = G(s_orig, r2) — reduces to old rmap_paths for (s_orig, r2)
- **(r1, t)**: paths = G(r1, s_orig) — reduces to old rmap_paths for (r1, s_orig)
- **(r1, r2)**: paths unchanged — directly from old rmap_paths

### Key technique
Uses `rw` (not `subst`) for case-splitting equalities `r1 = t` / `r2 = t` to
avoid Lean 4's `subst` eliminating the RHS variable `t` from scope.

### Reusable lemma: `rmap_paths_update_with_epsilon`
Extracted the 4-case proof into a standalone lemma parameterized by:
- `ht_fresh : t ∉ pe.refs` — freshness of new ref
- `hs_in_refs : s_orig ∈ pe.refs` — source ref is in PathEnv
- `hrmap_s_orig` — rmap maps s_orig to concrete location
- `hrmap_live` — that location is valid in heap
- `hold_paths` — old rmap_paths invariant

This lemma is reusable for other preservation cases using `update_with_epsilon`
(e.g., freeze, borrow without field extension).

### Previously remaining sorry (now resolved)
`s_orig ∈ env.pathEnv.refs` — resolved by adding `varEnv_refs_in_pathEnv` invariant
to `WellTypedState` (see below).

## Add `varEnv_refs_in_pathEnv`, `siteEnv_refs_in_pathEnv`, `live_refs_unique` to WellTypedState

Added three new invariant fields to `WellTypedState` and proved their preservation
across all existing preservation cases (intLit, copy_val, binop, pack, heap_alloc,
copy_ref, move, readRef, release, assign_valid, assign_invalid).

### TypeSoundness.lean — New WellTypedState fields

- **`varEnv_refs_in_pathEnv`**: every ref in a `.validVar` varEnv entry is in `pathEnv.refs`
- **`siteEnv_refs_in_pathEnv`**: every ref in a siteEnv entry is in `pathEnv.refs`
- **`live_refs_unique`**: each abstract ref appears at most once across valid varEnv
  entries and siteEnv entries (3-part conjunction: var-site, site-site, var-var)

### Preservation proof patterns by case

| Case | Pattern | Key technique |
|------|---------|--------------|
| intLit, copy_val | insert basic into siteEnv | `simp [lookup_insert_same]` closes `s'=s` since basic ≠ ref |
| binop | delete+delete+insert basic | Chain of `lookup_delete_ne` reductions |
| pack | deleteAll+insert basic | `lookup_deleteAll_some` reduces to old env |
| heap_alloc | env unchanged | Fields pass through directly |
| copy_ref | insert ref t, update_with_epsilon | Freshness of `t` + `List.mem_cons` for pathEnv |
| move | invalidate x, insert τ from x | `lookup_insert_same` contradiction for invalidVar; `rw [hs'.2.1] at hvar` for ref equality |
| readRef | delete src, delete_ref_node r | `live_refs_unique r` proves `r' ≠ r` for surviving entries |
| release | delete site, delete_ref_node r | Same pattern as readRef |
| assign_valid | complex siteEnv (insert+delete+delete) | Helper `hse_reduce` reduces all lookups to old env |
| assign_invalid | update varEnv x, delete siteEnv a | Site-site/var-site contradiction when `x'=x` via `hsite` |

### Key techniques

- **Captured variables before struct literals**: `r`, `hlookup`, etc. from outer `obtain`
  are not accessible inside `by` blocks within `exact { ... }` struct literals. Fixed by
  introducing `have hlive_r := hwt.live_refs_unique r` etc. before the struct.
- **`rw` instead of `subst`**: `subst heq` where `heq : x1 = x` eliminates `x` from
  scope. Used `rw [heq1, lookup_insert_same]` instead to preserve variable availability.
- **MoveType injection**: `cases this` on `MoveType.ref a b c = MoveType.ref d e f` fails;
  use `simp only [Option.some.injEq, MoveType.ref.injEq]` to extract component equalities.

### Sorry eliminated

The `s_orig ∈ env.pathEnv.refs` sorry in `preservation_copy_ref` is now resolved via
`hwt.varEnv_refs_in_pathEnv x τ_ref s_orig isBor ms hvar`.
