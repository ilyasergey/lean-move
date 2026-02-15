# Changelog — 2026-02-15c

## Remove Ssreflect dependency, upgrade to Lean 4.27

### Dependency removal
- Removed `require ssreflect` from `lakefile.lean`.
- Removed `import Ssreflect.Lang` from all 28 files that imported it.
- Rewrote 2 proofs in `AssocMap.lean` that used Ssreflect tactics (`sby`, `move`, `scase`)
  with standard Lean 4 tactics (`cases`, `congr`, `induction`, `split`).
- Rewrote 2 proofs in `TypesUtils.lean` (`delete_ref_node_paths_involving_r`,
  `delete_ref_node_paths_not_involving_r`) replacing `move`/`scase` with `intro`/`rcases`.

### Lean 4.27 compatibility fixes
- Updated `lean-toolchain` from `v4.24.0` to `v4.27.0`.
- Updated `batteries` and `mathlib` tags from `v4.24.0` to `v4.27.0`.
- **`DecidableEquality.lean`**: Lean 4.27 fails to generate equational theorems for
  mutual recursive definitions over nested inductives. Added 20 manual `@[simp]` lemmas
  for `BasicMoveType.beq`/`beqEntries` reduction rules; moved `beq`/`beqEntries` from
  `where`-clause to top-level `mutual` block; updated proofs to use named simp lemmas.
- **`InitState.lean`**: Same issue with `hasType_bool` (also uses `where`-clause mutual).
  Added 21 manual `@[simp]` lemmas for `hasType_bool` reduction rules; updated
  `hasType_bool_sound` proofs to use them.

### Files changed
- `lean-toolchain` — v4.24.0 → v4.27.0
- `lakefile.lean` — removed ssreflect, updated batteries/mathlib to v4.27.0
- `lake-manifest.json` — updated dependency versions
- `LeanMove/Structures/AssocMap.lean` — rewrote Ssreflect proofs
- `LeanMove/Structures/DecidableEquality.lean` — mutual def restructure + simp lemmas
- `LeanMove/Typing/TypesUtils.lean` — rewrote Ssreflect proofs
- `LeanMove/Typing/Soundness/InitState.lean` — hasType_bool simp lemmas
- 21 example/lang files — removed `import Ssreflect.Lang`
