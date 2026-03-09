# Changelog — 2026-03-07

## Enum type checker, soundness proof, and runtime tests (WIP)

### Summary

Continued work on enum support. Added relational and algorithmic typing
rules for all enum constructs (packVariant, unpackVariant, variantSwitch),
preservation and weakening stubs, progress proofs, and runtime test
infrastructure. Build passes but some preservation cases use `sorry`.

### Key changes

- **TypeChecking.lean**: Relational rules for `let_bind_packVariant`,
  `unpackVariant_rule`, `unpackVariant_ref_rule`, `variantSwitch_rule`
- **AlgorithmicTypeChecking.lean**: Executable type checker cases for all
  enum constructs; `addRefFieldSites` iterated fresh ref allocation
- **Progress.lean**: All enum progress cases proved (zero sorrys);
  `variantMismatch` classified as acceptable error
- **Preservation.lean**: Stubs for preservation_packVariant,
  preservation_unpackVariant, preservation_variantSwitch
- **Weakening.lean**: Enum weakening cases for subsumption transfer
- **InitState.lean**: `hasType_bool_sound` extended for variant values;
  `checkEnumSingleVariant` for single-variant restriction
- **Defs.lean**: `HasType.variant` constructor; `ValueMatchesType`,
  `typeAtPathV`, `readPath_HasType_transfer` extended for variant values;
  `enum_field_compatibility` WellTypedState field; `variantCompatible`

### Build

Compiles with `sorry` stubs in Preservation.lean enum cases.
