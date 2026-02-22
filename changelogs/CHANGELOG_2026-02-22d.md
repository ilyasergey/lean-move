# Changelog — 2026-02-22d

## Simplify type-checking test environments with order-independent refid matching

### Summary

Eliminated boilerplate and magic refid numbers from type-checking test files. Test
environments now use high-level constructors (`mkLabelEnvDec`, `mkLabelEnv`,
`freshenBlockEnv`) and an order-independent backtracking search (`extendRefSubst`)
during subsumption checking, so test authors never need to reverse-engineer the
algorithmic checker's internal refid assignments.

### Problem

Each type-checking test required a hand-written `LabelEnvDec` (or `LabelEnv`) with
abstract reference ids (`.refid N`) that exactly matched the checker's dynamically
assigned values, in the exact order. This was fragile — any change to the checker's
allocation order broke tests — and obscured the test's intent behind implementation
details. Multi-block tests (branches, loops) were especially painful because
intermediate references from control-flow joins had to match precisely.

### Approach

1. **Single-block functions**: `mkLabelEnvDec f` / `mkLabelEnv f` derive the initial
   environment from the function definition — no manual path environment needed.

2. **Multi-block functions**: `freshenBlockEnv f env` replaces template `.refid` values
   with fresh ids outside the function's parameter/local range. During subsumption,
   `extendRefSubst` extends the variable-derived σ by backtracking search over
   unmapped refids, validated by `regexSubsumedBy` path checks. This makes refid
   ordering irrelevant.

3. **Soundness**: `findRefExtension_keys_refid` and `findRefExtension_values_not_root`
   prove the extended σ preserves the invariants required by `subsumes_bool_implies_subsumes`.

### Key changes

#### TypeCheckingAlgorithmic.lean (+82 lines)
- **`unmappedRefs(σ, refsL)`**: envL refids not yet mapped by σ (non-refid arefs excluded)
- **`unmatchedRefs(σ, refsL, refsE)`**: env refs not claimed by σ targets or identity-mapped
- **`findRefExtension(σ, unmapped, unmatched, refsL, envL, env)`**: structurally recursive
  backtracking search that pairs unmapped envL refids with unmatched env refs, validated by
  full path subsumption
- **`extendRefSubst(σ, refsL, refsE, envL, env)`**: wrapper that computes unmapped/unmatched
  sets and invokes `findRefExtension`
- **`TypeEnv.subsumes_bool`**: updated to call `extendRefSubst` after `computeRefSubst`

#### AlgorithmicTypingSoundness.lean (+179/-89 lines)
- **`findRefExtension_keys_refid`**: all keys in extended σ are `.refid n`
  (from match guard + induction via `List.exists_of_findSome?_eq_some`)
- **`findRefExtension_values_not_root`**: all values in extended σ are not `.root`
  (from `.root => none` guard + induction)
- **`extendRefSubst_keys_refid`** / **`extendRefSubst_values_not_root`**: lift to
  `extendRefSubst` wrapper
- **`subsumes_bool_implies_subsumes`**: updated for new `extendRefSubst` match structure

#### DecidableTypeEnv.lean (+76 lines)
- **`mkInitEnvDec(f)`**: initial `TypeEnvDec` from function params + locals
- **`mkLabelEnvDec(f)`**: single-block `LabelEnvDec` from function definition
- **`maxFunDefRefId(f)`**: max `.refid` value from params + locals
- **`collectPathEnvDecRefIds`** / **`collectEnvDecRefIds`**: collect all refid Nats
- **`applySubstPathEnvDec`** / **`applySubstSiteEnvList`** / **`applySubstEnvDec`**:
  substitution across decidable environment components
- **`freshenBlockEnv(f, env)`**: replace template refids with fresh ones

#### TypeChecking.lean (+15 lines)
- **`mkInitEnv(f)`**: propositional version of `mkInitEnvDec`
- **`mkLabelEnv(f)`**: propositional version of `mkLabelEnvDec`

#### Test files (26 files, -478/+498 net ~0 lines)

**Single-block accepted** (use `mkLabelEnvDec`):
- `alias_writes`, `borrow_in_loop_fixed_ok`, `call_rule_ok`, `deref_borrow_field_ok`,
  `extension_after_call`, `imm_borrow_after_mut`, `multible_mutable_return_values`,
  `mutable_borrows_are_not_unique`, `return_param_ref_ok`

**Single-block rejected** (use `mkLabelEnv`):
- `borrow_field_non_ref`, `borrow_in_loop`, `dangling_ref`, `deref_non_ref`,
  `imm_borrow_after_mut_call_invalid`, `imm_borrow_after_mut_fields_invalid`,
  `mutable_borrows_are_not_unique_calls_invalid`, `return_aliased_mut`,
  `return_local_borrow`, `return_mut_with_outstanding_borrow`, `simple_dangling`,
  `uninitialized_var`, `unpack_non_record`, `use_after_move`

**Multi-block** (use `mkInitEnvDec` + `freshenBlockEnv`):
- `alias_write_after_join`, `extension_writes_after_join`, `subtree_writes_release`

#### metatheory.md (+33 lines)
- Added "Test environment construction" subsection documenting `freshenBlockEnv`
  and `extendRefSubst`

### Result

`lake build` succeeds (349 jobs). All existing tests pass unchanged. No sorrys remain
in the `findRefExtension` soundness lemmas.
