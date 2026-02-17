# Changelog — 2026-02-17d

## Prove all WF lemmas for call rule (TypesUtils.lean + AlgorithmicTypingSoundness.lean)

### Summary

Eliminated all sorrys in `TypesUtils.lean` and `AlgorithmicTypingSoundness.lean` related
to the call rule. These lemmas prove that `extend_with_star`, `populate_call_outputs`,
and `call_connect_inputs_outputs` preserve `TypeEnv.WellFormed`, and that
`generateFreshRefs` produces fresh, distinct, non-root refs.

### TypesUtils.lean (+255 lines)

**`refid_ge_start_fresh`** — any `.refid n` with `n ≥ getRefId(nextFreshRefInEnv env)`
is fresh in the env. Key technique: unfold `nextFreshRefInEnv` in hypothesis before
introducing local let bindings (avoids omega mismatch).

**`extend_with_star_wellformed`** (~40 lines) — proves `PathEnv.WellFormed` is preserved
by `extend_with_star` when `target ≠ .root`. Uses `hmem_ext` helper for membership
reasoning across the conditional `refs` extension, and `if_neg` for path case analysis.

**`foldl_preserves_wf_mem`** — generic `List.foldl` preservation with membership tracking.
Proves `P (l.foldl f init)` given `P init` and `∀ acc b, b ∈ l → P acc → P (f acc b)`.

**`extend_star_inner_foldl_wf`** — composes `foldl_preserves_wf_mem` with
`extend_with_star_wellformed` for the inner foldl loops in `call_connect_inputs_outputs`.

**`siteEnv_filterMap_{ref,mut,imm}_not_root`** (3 lemmas) — refs extracted from SiteEnv
by the three filterMap patterns used in `call_connect_inputs_outputs` are not `.root`.

**`call_connect_inputs_outputs_wf`** (~45 lines) — proves `TypeEnv.WellFormed` preservation
through the three nested foldl loops (Rule 1: imm outputs × inputs, Rule 2: mut outputs ×
mut inputs, Rule 3: imm output pairs). Uses nested `foldl_preserves_wf_mem` applications.

**`populate_call_outputs_wf`** (~60 lines) — proves `TypeEnv.WellFormed` preservation
through recursive output population. New preconditions `hout_not_root` and `hout_not_varRef`
ensure fresh refs are well-formed. Induction on `as` with generalization over `env`, `rets`,
`outRefs`. Each ref-typed case constructs intermediate WellFormed via
`update_with_epsilon_wellformed` + `SiteEnv.insert_refs_not_root`.

### AlgorithmicTypingSoundness.lean (+41/-3 lines)

**Four `generateFreshRefs` lemmas:**
- `generateFreshRefs_fresh` — all generated refs satisfy `freshRefInEnvBool`. Uses
  `refid_ge_start_fresh` with `Nat.le_add_right`.
- `generateFreshRefs_nodup` — generated list has no duplicates. Uses `pairwise_map` +
  `nodup_range` from Lean 4 core (not Mathlib's `List.Nodup.map`).
- `generateFreshRefs_not_root` — all generated refs are `.refid`, not `.root`. Uses
  `Aref.noConfusion`.
- `generateFreshRefs_not_varRef` — all generated refs are `.refid`, not `.varRef`. Uses
  `Aref.noConfusion`.

**Call site updated** (~line 1514): replaced two `by sorry` with lemma calls; added
`generateFreshRefs_not_root` and `generateFreshRefs_not_varRef` arguments to
`populate_call_outputs_wf`.

### Sorry status

Both `TypesUtils.lean` and `AlgorithmicTypingSoundness.lean` are now sorry-free.

| File | Remaining sorrys | Notes |
|------|-----------------|-------|
| `TypesUtils.lean` | 0 | All WF lemmas proved |
| `AlgorithmicTypingSoundness.lean` | 0 | All freshness/nodup lemmas proved |
| `Weakening.lean` | 1 | `call` case |
| `Preservation.lean` | 1 | dispatcher (`ret`, `call`) |

### Files changed

| File | Lines changed |
|------|--------------|
| `TypesUtils.lean` | +255 |
| `AlgorithmicTypingSoundness.lean` | +41/-3 |
