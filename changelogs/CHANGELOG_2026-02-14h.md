# Changes Made on 2026-02-14 (Part 8)

## Add WellTypedState invariants 18–20 and complete preservation_freeze

Added three new WellTypedState fields (invariants about PathEnv paths) and proved them for all preservation cases and `initState_safe`. Completed the `rmap_paths` proof for `preservation_freeze`, eliminating its last `sorry`.

### New WellTypedState fields (Defs.lean)

- **Field 18 `paths_from_non_member_empty`**: non-member refs (except root) have no outgoing paths to other refs
- **Field 19 `paths_to_non_member_empty`**: non-member refs (except root) have no incoming paths from other refs
- **Field 20 `self_loop_only_empty`**: self-loops only accept the empty path (`p = []`)

### DecidableTypeEnv.lean — strengthened PathEnvDec well-formedness

- Strengthened `PathEnvDec.wellFormed_bool` checks 3–4: now verify that **all** stored entry keys have source/target in `refs` (previously only checked root-adjacent entries)
- Added `PathEnvDec.toPathEnv_non_member_from` and `toPathEnv_non_member_to`: if `r ∉ refs` and `r ≠ .root`, then `paths(r, v)` and `paths(u, r)` are empty for `u ≠ v`
- Added `check_fun_dec_lenv_non_member_from`, `check_fun_dec_lenv_non_member_to`: lift non-member emptiness to all label environments
- Added `check_fun_dec_lenv_self_loop`: self-loops in `PathEnvDec.toPathEnv` are always `ε`, so `interpret_regex` gives `p = []`

### TypesUtils.lean — regex helper lemmas (+254 lines)

- `interpret_regex_union_empty_left/right`: union with `.empty` simplifies
- `interpret_regex_concat_epsilon_left/right`: concat with `.epsilon` simplifies
- `interpret_regex_empty_false`: `.empty` never matches
- `only_matches_empty_sound`: if `only_matches_empty r = true` then `interpret_regex r p → p = []`
- `check_outbound`/`check_inbound`: verify all outgoing/incoming paths from a ref are empty
- `check_outbound_sound`/`check_inbound_sound`: soundness of the above checks

### InitState.lean — SoundnessAssumptions extensions

- Added `lenv_paths_from_non_member`, `lenv_paths_to_non_member`, `lenv_self_loop` fields to `SoundnessAssumptions`
- Updated `SoundnessAssumptions.of_check` with three new parameters
- Wired fields 18–20 into `initState_safe` WellTypedState constructor

### Preservation.lean — fields 18–20 for all cases + freeze rmap_paths

**Fields 18–19** propagation patterns:
- 7 same-pathEnv cases: passthrough
- 2 `delete_ref_node` cases (readRef, release): `by_cases` on deleted ref membership
- 2 fresh-ref cases (copy_ref, borrowImm): `by_cases` on fresh ref, contradiction via `update_with_extension`
- 1 `garbage_collect` case (assign_valid): unfold + `by_cases` through layers
- 1 `consume_ref_transfer` case (freeze): `by_cases` on `r`/`r'`, using `paths_from/to_non_member_empty`

**Field 20** propagation patterns:
- 7 same-pathEnv: passthrough
- 2 `delete_ref_node`: `by_cases u = r`, subst gives empty regex
- 3 extension cases: unfold operation, `by_cases u = t` (fresh ref), contradiction or passthrough
- 1 `consume_ref_transfer`: `by_cases u = r` (empty) and `u = r'` (cross-edge eliminated by field 18)

**`rmap_paths` for freeze** — completed proof handling `consume_ref_transfer pe r r'`:
- Case A (`r2 ≠ r'`): old paths unchanged, `rmap'.map = rmap.map` for both refs via `if_neg`
- Case B1 (self-loop `r' → r'`): `self_loop_only_empty` gives `p = []`, then `show` the goal with `if_pos rfl`
- Case B1-neg (`r1 ≠ r'`, target `r'`): contradiction via `paths_to_non_member_empty`
- Case B2 (from `G(r1, r)`): `hwt.rmap_paths r1 r` + `rw [hrmap]` bridges old rmap to new `rmap'`

### TypeSoundness.lean

- Updated `type_soundness_dec` to pass `check_fun_dec_lenv_non_member_from`, `check_fun_dec_lenv_non_member_to`, `check_fun_dec_lenv_self_loop` to `SoundnessAssumptions.of_check`

### Remaining sorry

- Preservation dispatcher: borrowMut, borrowField, borrowMutField, writeRef, jump, branch, ret, call, unpack

### Files modified

1. **`LeanMove/Typing/Soundness/Defs.lean`** — +11 lines (3 new WellTypedState fields)
2. **`LeanMove/Typing/Algorithmic/DecidableTypeEnv.lean`** — +183/-62 lines (strengthened checks, 6 new theorems)
3. **`LeanMove/Typing/TypesUtils.lean`** — +254 lines (regex helper lemmas)
4. **`LeanMove/Typing/Soundness/InitState.lean`** — +37 lines (SoundnessAssumptions extensions)
5. **`LeanMove/Typing/Soundness/Preservation.lean`** — +202 lines (fields 18–20 for all cases + freeze rmap_paths)
6. **`LeanMove/Typing/TypeSoundness.lean`** — +6/-5 lines (pass new theorems)
