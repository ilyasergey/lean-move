# Changes Made on 2026-02-12

## Refactor: Move regex definitions and lemmas to Regex.lean

Moved all regex-related definitions and soundness lemmas from the algorithmic
checker files into `Regex.lean`, consolidating them with the existing regex
infrastructure. All call sites resolve via `open Regex`.

### Regex.lean — New definitions and theorems
- `regexBeq` — boolean structural equality for `Regex α` (moved from `TypeCheckingAlgorithmic.lean`)
- `regexSubsumedBy` — conservative language inclusion check (moved from `TypeCheckingAlgorithmic.lean`)
- `regexBeq_refl` — reflexivity of `regexBeq` (moved from `AlgorithmicTypingSoundness.lean`)
- `regexBeq_eq` — soundness: `regexBeq r1 r2 = true → r1 = r2` (moved from `AlgorithmicTypingSoundness.lean`)
- `eq_regexBeq` — completeness: `r1 = r2 → regexBeq r1 r2 = true` (moved from `AlgorithmicTypingSoundness.lean`)
- `is_empty_sound` — `is_empty r = true → ∀ s, ¬ interpret_regex r s` (moved from `AlgorithmicTypingSoundness.lean`)
- `regexSubsumedBy_sound` — `regexSubsumedBy r1 r2 = true → L(r1) ⊆ L(r2)` (moved from `AlgorithmicTypingSoundness.lean`)

### TypeCheckingAlgorithmic.lean
- Removed `regexBeq` and `regexSubsumedBy` definitions (now in `Regex.lean`)

### AlgorithmicTypingSoundness.lean
- Removed `regexBeq_refl`, `regexBeq_eq`, `eq_regexBeq` lemmas (now in `Regex.lean`)
- Removed `is_empty_sound`, `regexSubsumedBy_sound` theorems (now in `Regex.lean`)

### Checker.lean
- Removed dead import of deleted `AlgorithmicTypingCompleteness`

## Refactor: Extract generic type/environment lemmas into TypesUtils.lean

Extracted ~590 lines of generic type and environment invariant definitions and
preservation lemmas from `AlgorithmicTypingSoundness.lean` into a new
`LeanMove/Checker/TypesUtils.lean`. These lemmas depend only on `Types.lean` and
`TypeChecking.lean` (not on the algorithmic checker), making them available for
future semantic type soundness proofs.

### TypesUtils.lean (new)
Import: `import LeanMove.Checker.TypeChecking`

**freshRef / nextFreshRef properties:**
- `freshRef_iff_freshRefBool`, `nextFreshRef_fresh`, `freshRefBool_implies_freshRef`, `nextFreshRef_fresh_prop`
- `nextFreshRef_not_root`, `nextFreshRef_is_refid`, `nextFreshRef_not_varRef`

**PathEnv definitions and preservation:**
- `delete_ref_node_refs`, `delete_ref_node_paths_involving_r`, `delete_ref_node_paths_not_involving_r`
- `isBorrowPath` (def), `PathEnv.WellFormed` (structure), `PathEnv.init_wellformed`
- `delete_ref_node_wellformed`

**SiteEnv.RefsNotRoot + preservation:**
- `SiteEnv.RefsNotRoot` (def), `empty_refs_not_root`, `insert_refs_not_root`
- `delete_refs_not_root`, `deleteAll_refs_not_root`, `addFieldSites_refs_not_root`

**VarEnv.RefsNotRoot / RefsAreFresh + preservation:**
- `VarEnv.RefsNotRoot`, `VarEnv.RefsAreFresh` definitions
- Insert/update/lookup preservation lemmas for both invariants
- `moveTypeRefsNotRoot`, `moveTypeIsFreshRef`, `Aref.isFreshRef` definitions
- `Aref.Compatible_preserves_freshRef`, `MoveType.compatible_preserves_freshRef`

**TypeEnv.WellFormed + operation preservation:**
- `TypeEnv.WellFormed` (structure), `init_wellformed`
- Preservation for: `insert_siteEnv`, `delete_siteEnv`, `deleteAll_siteEnv`, `update_varEnv`, `insert_update`, `insert_pathEnv`, `delete_insert_pathEnv`, `delete_delete_insert`, `deleteAll_insert`
- `update_with_extension_wellformed`, `update_with_epsilon_wellformed`
- `garbage_collect_wellformed`, `consume_ref_transfer_wellformed`
- `TypeEnv.equiv_refl`

**Standalone generic lemmas:**
- `varRef_fresh_when_not_borrowed` — uses relational `not_borrowed`, pure env property
- `call_connect_inputs_outputs_wf` — uses relational `call_connect_inputs_outputs`

### AlgorithmicTypingSoundness.lean
- Added `import LeanMove.Checker.TypesUtils`
- Removed ~800 lines of generic definitions and lemmas (now in TypesUtils.lean)
- Reduced from ~1900 to ~1097 lines
- Remaining: all `*_bool_sound/complete` bridge lemmas, private helpers, core soundness theorems (`check_letBind_sound`, `check_stmt_sound`, `check_fun_sound`)
