# Changelog — 2026-03-10

## Multi-variant enum soundness: zero sorrys, flat encoding, decidable certificate

### Summary

Completed the multi-variant enum soundness proof with zero sorrys.
Replaced the earlier `enum_field_compatibility` / `checkEnumSingleVariant`
approach with **flat encoding**: every enum value carries all fields from
all variants using qualified names (`qualifyField vname f`), with inactive
variants filled by `defaultValue`. This makes `readPath_HasType_transfer`
and `typeAtPathV_HasType_determined` unconditionally true, eliminating the
single-variant restriction entirely.

### Key changes

**Flat encoding (`Defs.lean`, `Smallstep.lean`, `MoveLight.lean`)**:
- `HasType.variant` now uses `allEnumQualifiedFieldTypes` (depends only on
  enum name, not variant name) — two values of the same enum type always
  have the same field type map
- `buildFlatVariantFields` in semantics iterates all variants, filling
  inactive fields with `defaultValue`
- `qualifyField : Id → Field → Field` produces `"vname.f"` to prevent
  cross-variant field name collisions
- `readPath_HasType_transfer` and `typeAtPathV_HasType_determined` proved
  unconditionally (no `containsEnum` check needed)
- Removed `enum_field_compatibility` from WellTypedState and all ~45 proof sites

**New WellTypedState invariants (`Defs.lean`, `InitState.lean`)**:
- `enum_qualified_nodup`: qualified field names unique per enum definition
- `enum_names_nodup`: enum type names unique in EnumEnv
- `enum_variant_nodup`: variant names unique within each enum
- `enum_fields_nodup`: field names unique within each variant
- `defaultValues_typed`: `defaultValue` produces well-typed fill values

**Decidable soundness (`InitState.lean`, `TypeSoundness.lean`)**:
- Added 4 new boolean checks to `checkDecidable` (23 conjuncts total)
- Removed `checkEnumSingleVariant`
- Updated `of_check` destructuring patterns and projection chains
- `type_soundness_dec` now supports multi-variant enums

**List utility lemmas (`ListUtils.lean`)**:
- Moved 6 generic list lemmas from Preservation.lean to ListUtils.lean:
  `lookup_append_left`, `lookup_append_right`, `list_map_lookup_transfer`,
  `list_map_lookup_pair`, `flatMap_map_lookup_transfer`,
  `flatMap_map_lookup_pair`

**Preservation proof (`Preservation.lean`)**:
- `buildFlatVariantFields_eq_map` rewrite lemma for factoring pair
  construction out of if/match expressions
- `buildFlatVariantFields_HasType` proved using explicit `@` generic
  lemma calls to resolve higher-order unification
- All `enum_field_compatibility` proof sites removed
- All `enum_mutable_no_extension` sites proved
- Zero sorrys in entire file

**Multi-variant enum soundness test (`AllTests.lean`)**:
- `enum_match_no_danglingRef`: decidable type soundness certificate for
  the 3-variant `Threes { One{pos0:u64}, Two{}, Three{pos0:u64} }` enum
  via `type_soundness_dec_no_danglingRef` with `native_decide`

**Documentation**:
- `metatheory.md`: Updated Part IV (Enum Extension) to reflect flat
  encoding approach, multi-variant support, zero sorrys; updated
  WellTypedState field count (30 → 35); added enum well-formedness
  invariants section; updated type soundness signatures with `enumEnv`;
  removed single-variant limitation
- `LIMITATIONS.md`: Updated enum/variant/vector entries to "Done"

### Files changed

| File | Changes |
|------|---------|
| `MoveLight.lean` | +`qualifyField`, `allEnumFieldTypes`, `allEnumQualifiedFieldTypes`, `buildFlatVariantFields`, `defaultValue` |
| `Smallstep.lean` | +flat variant construction via `buildFlatVariantFields` |
| `ListUtils.lean` | +6 generic list utility theorems (moved from Preservation.lean) |
| `Defs.lean` | Flat `HasType.variant`, removed `enum_field_compatibility`, +5 enum well-formedness fields |
| `InitState.lean` | +4 decidable checks, removed `checkEnumSingleVariant`, proved all enum invariants |
| `Preservation.lean` | +`buildFlatVariantFields_eq_map`/`_HasType`, removed ~45 `enum_field_compatibility` sites |
| `TypeSoundness.lean` | Updated projection chains for 23 conjuncts |
| `AlgorithmicTypeChecking.lean` | Updated for flat encoding |
| `AlgorithmicTypingSoundness.lean` | Updated for flat encoding |
| `Progress.lean` | Updated for flat variant cases |
| `Weakening.lean` | Updated for flat variant cases |
| `StackSafeUtils.lean` | Updated signatures |
| `TypeChecking.lean` | Minor updates for enum env threading |
| `AllTests.lean` | +`enum_match_no_danglingRef` multi-variant soundness test |
| `metatheory.md` | Updated Part IV, WellTypedState description, soundness signatures |
| `LIMITATIONS.md` | Updated enum/vector/variant_switch entries to Done |

### Build

393 jobs, zero sorrys. Multi-variant enum soundness fully proved.
