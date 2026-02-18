# Changelog — 2026-02-18

## Prove `call` case in `typecheck_stmt_weaken`: eliminate all sorrys from Weakening.lean

### Summary

Completed the weakening theorem for the `call` statement case — the last remaining `sorry`
in `Weakening.lean`. This is the most complex case in the weakening proof because it involves
function environment lookup, fresh reference generation, two-phase environment modification
(`populate_call_outputs` + `call_connect_inputs_outputs`), and threading the `TypeEnv.subsumes`
relation through all of these operations.

### Key new lemmas in Weakening.lean (~1900 new lines)

#### Precondition transfer lemmas
| Lemma | Purpose |
|-------|---------|
| `types_conform_SiteEnvSubstEquiv` | Transfer `types_conform` across σ-substitution |
| `all_fresh_sites_subsumes` | Transfer `all_fresh_sites` across subsumes |
| `check_mutable_inputs_isolated_subsumes` | Transfer mutable input isolation across subsumes |

#### `populate_call_outputs` subsumes preservation
| Lemma | Purpose |
|-------|---------|
| `populate_call_outputs_subsumes` | Core compositional lemma: if `envL` subsumes `env`, then after populate on both sides, `envL'` subsumes `envE'` (with extended σ mapping fresh refs) |
| `populate_call_outputs_exists'` | Existence: if populate succeeds for `envL`, it succeeds for `env` with corresponding fresh refs |
| `populate_call_outputs_wf` | Well-formedness preservation through populate |
| `populate_call_outputs_site_tracked` | Site-tracked preservation through populate |
| `populate_call_outputs_var_tracked` | Var-tracked preservation through populate |
| `populate_call_outputs_RefsUnique` | Refs-uniqueness preservation through populate |
| `populate_call_outputs_self_loop_only_empty` | Self-loop invariant preservation through populate |
| `populate_call_outputs_paths_to_nm` / `_from_nm` | Non-member path emptiness through populate |
| `populate_call_outputs_funEnv` | FunEnv unchanged through populate |

#### `call_connect_inputs_outputs` subsumes preservation
| Lemma | Purpose |
|-------|---------|
| `extend_with_star_path_inclusion` | Single `extend_with_star` preserves path inclusion under σ |
| `inner_foldl_ews_path_incl` | Inner foldl (unconditional) preserves path inclusion |
| `outer_foldl_ews_path_incl` | Outer foldl (unconditional, Rule 1 & 2) preserves path inclusion |
| `inner_foldl_cond_ews_path_incl` | Inner foldl (conditional, Rule 3) preserves path inclusion |
| `outer_foldl_cond_ews_path_incl` | Outer foldl (conditional, Rule 3) preserves path inclusion |
| `path_inclusion_via_triple_foldl` | Composes all three rules; takes filter lists as parameters with σ-equalities to avoid match-compilation mismatch |
| `call_connect_subsumes` | Top-level: `call_connect_inputs_outputs` preserves subsumes |
| `call_connect_varEnv` / `siteEnv` / `funEnv` / `refs_eq` / `refs_mono` | Structural preservation through call_connect |
| `call_connect_inputs_outputs_wf` | Well-formedness preservation through call_connect |
| `call_connect_paths_to_nm` / `_from_nm` | Non-member path emptiness through call_connect |
| `call_connect_self_loop_only_empty` | Self-loop invariant through call_connect |

#### σ-mapping lemmas for filter lists
| Lemma | Purpose |
|-------|---------|
| `filterMap_ref_map_σ` | Generic ref filterMap preserves σ-relationship |
| `filterMap_immRef_map_σ` | Immutable ref filterMap (io list) σ-relationship |
| `filterMap_mutRef_map_σ` | Mutable ref filterMap (mo/mi lists) σ-relationship |
| `filterMap_allRef_map_σ` | All ref filterMap (inputs list) σ-relationship |

#### foldl refs preservation lemmas
| Lemma | Purpose |
|-------|---------|
| `inner_foldl_ews_refs_eq` / `outer_foldl_ews_refs_eq` | Unconditional foldl preserves refs |
| `inner_foldl_cond_ews_refs_eq` / `outer_foldl_cond_ews_refs_eq` | Conditional foldl preserves refs |

#### Main theorem
| Lemma | Purpose |
|-------|---------|
| `weaken_call` | The extracted `call` case: assembles all of the above |

### Technical insight: match-compilation mismatch

A key challenge was that Lean 4's match compiler creates unique `match_N` auxiliary definitions
for each match expression. Two syntactically identical matches in different definitions produce
different `match_N` constants, causing `rw` to fail (requires syntactic equality). The solution
was `path_inclusion_via_triple_foldl`, which takes filter lists as generic parameters with
explicit σ-mapping equalities, uses `subst` to convert E-side lists to `.map σ` form, then
relies on `exact` (which uses definitional equality) to bridge the gap.

### Other changes

| File | Change |
|------|--------|
| `Types.lean` | Added `funEnv` equality handling to `TypeEnv.subsumes` usage sites |
| `TypesUtils.lean` | New helper lemmas for `SiteEnvSubstEquiv`, `VarEnvSubstEquiv`, `makeFreshRefs` |
| `TypeChecking.lean` | Minor: updated `call` constructor arg order |
| `Preservation.lean` | Fixed `inv_call` pattern to match updated `typecheck_stmt.call` constructor |
| `AlgorithmicTypingSoundness.lean` | Fixed callers of `update_with_epsilon_wellformed` / `update_with_extension_wellformed` |
| `InitState.lean` | New lemmas for initial state properties |
| `Defs.lean` | New `SoundnessAssumptions` fields |
| `DecidableTypeEnv.lean` | New decidable checking lemmas |
| `AssocMap.lean` | New `notIn` / `lookup` helper lemmas |

### File stats

| File | Changes |
|------|---------|
| `Weakening.lean` | +2006 lines (net, from ~3300 to ~5200) |
| `TypesUtils.lean` | +147/-7 |
| `InitState.lean` | +46/-8 |
| `DecidableTypeEnv.lean` | +47 |
| `Preservation.lean` | +40/-12 |
| `AlgorithmicTypingSoundness.lean` | +25/-14 |
| Other files | minor |
| **Total** | **+2238/-99** |

### Result

**Weakening.lean is now sorry-free.** All 18 induction cases of `typecheck_stmt_weaken`
(including `call`) are fully proved. The full project builds successfully (300/300 jobs).
