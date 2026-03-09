# Changelog — 2026-03-09

## Complete enum support and move MVIR test files

### Summary

Completed the enum type checker soundness proof (for single-variant
enums) and moved all `.mvir` test files to `Tests/MVIR/`.

### Key changes

- **Preservation.lean**: All 4 enum preservation cases fully proved
  (packVariant, unpackVariant owned/ref, variantSwitch) — zero sorrys
- **AlgorithmicTypingSoundness.lean**: Enum cases in algorithmic typing
  soundness proved
- **Runtime tests**: `AllTests.lean` extended with enum runtime tests
  covering packVariant, unpackVariant (owned and ref), and variantSwitch
- **Metatheory docs**: Part IV (Enum Extension) added to `metatheory.md`
- **File reorganisation**: All 13 `.mvir` test files moved from
  `Tests/` to `Tests/MVIR/`; `include_str` paths updated throughout

### Build

393 jobs, zero sorrys. Full enum support with single-variant soundness
certificate.
