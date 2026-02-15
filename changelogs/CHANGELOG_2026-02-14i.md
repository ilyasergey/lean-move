# Changelog — 2026-02-14i

## Preservation: borrowMut proof + borrowImm/borrowMut unification

### New proof
- **`preservation_borrowMut`**: Proves preservation for mutable borrow of a basic-typed variable. Identical runtime semantics to `borrowImm` — only the `BorrowingKind` in the type environment differs.
- Wired up in the preservation dispatcher, removing one `sorry`.

### Refactoring: unified borrow proof
- **`preservation_borrow`**: Extracted ~190-line unified proof parameterized by `bk : BorrowingKind`, containing the full `WellTypedState` construction shared by both borrow cases.
- **`preservation_borrowImm`** and **`preservation_borrowMut`** are now thin ~8-line wrappers that do inversion + step simplification, then delegate to `preservation_borrow`.
- Net reduction: ~190 lines of duplicated proof eliminated.

### SoundnessAssumptions refactoring
- **`checkDecidable`** now takes `LabelEnvDec` instead of `LabelEnv`, with `allWellFormed_bool` as a 5th conjunct.
- **`of_check`** derives path non-member and self-loop properties internally from `allWellFormed_bool`, removing 3 separate hypotheses (`hlenv_from`, `hlenv_to`, `hlenv_self_loop`).
- **`type_soundness_dec`** updated to use simplified `of_check` signature.

### Files changed
- `LeanMove/Typing/Soundness/Preservation.lean` — unified borrow proof, borrowMut case
- `LeanMove/Typing/Soundness/InitState.lean` — checkDecidable/of_check refactoring
- `LeanMove/Typing/TypeSoundness.lean` — updated type_soundness_dec
