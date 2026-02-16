# Changelog — 2026-02-16c

## Fix sorrys in AlgorithmicTypingSoundness.lean (sorry-free)

### Summary
Eliminated the 2 remaining `sorry`s in `subsumes_bool_implies_subsumes`, making
`AlgorithmicTypingSoundness.lean` completely sorry-free. These sorrys were in the
proof that the boolean `TypeEnv.subsumes_bool` implies the relational `TypeEnv.subsumes`.

### New helper lemmas (~120 lines)

**`refSubstStep`** — extracted the foldl step function from `computeRefSubst` as
a standalone definition, enabling clean inductive proofs.

**`refSubstStep_foldl_none`** — foldl starting from `none` always returns `none`.

**`computeRefSubst_foldl_keys_refid`** — the foldl preserves the invariant that
all keys in the accumulator are `.refid n` values, given the input pairs have
refid keys. Proof by induction on the input list, case-splitting on lookup/
injectivity/consistency conditions.

**`computeRefSubst_keys_refid`** — all keys in the substitution produced by
`computeRefSubst` are `.refid n`. Bridges from `computeRefSubst` (which uses an
inline lambda) to `refSubstStep` via `change`, then applies the foldl invariant
with a filterMap proof showing the initial pairs only have refid keys.

**`applySubstArefList_non_refid`** — `applySubstArefList` is identity on arefs
that are not refids. Since all keys are refids, `List.lookup` returns `none`.

**`applySubstMoveTypeList_eq`** — bridges list-based and function-based substitution:
`applySubstMoveTypeList σ τ = applySubstMoveType (applySubstArefList σ) τ`.

**`MoveType_base_compatible_bool_sound`** — boolean base type compatibility
implies the relational version. Uses `BasicMoveType.eq_of_beq` (not `beq_iff_eq`,
since `BasicMoveType` lacks `LawfulBEq`).

**`varenv_subst_equiv_bool_sound`** — if `varenv_subst_equiv_bool` returns true,
then `VarEnvSubstEquiv` holds. Uses `AssocMap.lookup_some` for membership,
`MoveType.eq_of_beq` for valid entries, and `MoveType_base_compatible_bool_sound`
for invalid entries.

### Sorry fixes in `subsumes_bool_implies_subsumes`

- **Sorry 1** (σ identity on non-refids): Now uses `applySubstArefList_non_refid`
  with `computeRefSubst_keys_refid`.
- **Sorry 2** (VarEnvSubstEquiv): Now uses `varenv_subst_equiv_bool_sound`.

### Technical notes
- `BasicMoveType` and `MoveType` have manual `beq` definitions (not from `DecidableEq`),
  so they lack `LawfulBEq`. Use `*.eq_of_beq` instead of `beq_iff_eq`.
- `AssocMap.lookup_some` (not `lookup_mem_entries`) relates lookup results to
  list membership.

### Files changed
- `LeanMove/Typing/Algorithmic/AlgorithmicTypingSoundness.lean` — +130/-2 lines
