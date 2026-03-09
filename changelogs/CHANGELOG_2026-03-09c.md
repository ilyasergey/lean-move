# Changelog — 2026-03-09c

## enum_mutable_no_extension: WellTypedState invariant and InitState proof

### Summary

Added `enum_mutable_no_extension` invariant to `WellTypedState` and proved
it for the initial state (`InitState.lean`). Added supporting infrastructure:
`readPath_HasType_transfer_no_enum`, `typeAtPathV_HasType_determined_no_enum`,
`enum_mutable_no_extension_transfer`, and `checkParamEnumNoExtension` in
`SoundnessAssumptions`. Replaced 18 of 25 `enum_mutable_no_extension := sorry`
sites with proofs. 7 sorrys remain, all in `Preservation.lean`.

### Changes

**Defs.lean**:
- Added `enum_mutable_no_extension` field (field 27) to `WellTypedState`:
  for mutable borrows of enum-containing types, no other tracked ref maps
  to the same heap location with an extending path suffix
- Added `enum_mutable_no_extension_transfer` theorem for passthrough cases
  where borrow sources are sub-maps and rmap is unchanged
- Added `readPath_HasType_transfer_no_enum`: when `containsEnum bt = false`,
  `readPath v1 path != none` implies `readPath v2 path != none` for any two
  values of the same type
- Added `typeAtPathV_HasType_determined_no_enum`: same-structure guarantee
  for non-enum types
- Added helper `readPath_some_of_HasType_record_lookup_some` and related
  structural lemmas

**InitState.lean**:
- Added `isProperListPrefix` and `not_isProperListPrefix_no_extension`:
  decidable check that no path is a proper prefix of another
- Added `checkParamEnumNoExtension`: checks that no two function parameters
  with mutable enum borrows share a heap location with extending paths
- Added `param_enum_no_extension` field to `SoundnessAssumptions`
- Replaced `true &&` (formerly `checkEnumSingleVariant`) with
  `checkParamEnumNoExtension f.params args &&` in `checkDecidable`
- Proved `enum_mutable_no_extension` for initial state using
  `param_enum_no_extension` assumption
- Zero sorrys in InitState.lean

**Preservation.lean**:
- Filled 12 `enum_mutable_no_extension` passthrough sites using
  `enum_mutable_no_extension_transfer`
- 7 sorrys remain at lines: 1946, 2477, 3207, 3208, 6296, 6781, 11097
  (borrow, borrowField, writeRef StackSafe x2, ret, call, unpackVariant)

**StackSafeUtils.lean**:
- Updated `stackSafe_heap_writeRef` type signature with enum_mutable
  parameters (preparation for StackSafe changes)

### Build

393 jobs, 7 sorrys (all in Preservation.lean).
