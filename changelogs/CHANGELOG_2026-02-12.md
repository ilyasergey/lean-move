# Changes Made on 2026-02-12

## Refactor: Move regex definitions and lemmas to Regex.lean

Moved all regex-related definitions and soundness lemmas from the algorithmic
checker files into `Regex.lean`, consolidating them with the existing regex
infrastructure. All call sites resolve via `open Regex`.

### Regex.lean — New definitions and theorems
- `regexBeq` — boolean structural equality for `Regex α` (moved from `TypeCheckingAlgorithmic.lean`)
- `regexSubsumedBy` — conservative language inclusion check (moved from `TypeCheckingAlgorithmic.lean`)
- `regexBeq_refl` — reflexivity of `regexBeq` (moved from `AlgorithmicTypingSoundness.lean`)
- `regexBeq_eq` — soundness: `regexBeq r1 r2 = true → r1 = r2` (moved from `AlgorithmicTypingSoundness.lean`)
- `eq_regexBeq` — completeness: `r1 = r2 → regexBeq r1 r2 = true` (moved from `AlgorithmicTypingSoundness.lean`)
- `is_empty_sound` — `is_empty r = true → ∀ s, ¬ interpret_regex r s` (moved from `AlgorithmicTypingSoundness.lean`)
- `regexSubsumedBy_sound` — `regexSubsumedBy r1 r2 = true → L(r1) ⊆ L(r2)` (moved from `AlgorithmicTypingSoundness.lean`)

### TypeCheckingAlgorithmic.lean
- Removed `regexBeq` and `regexSubsumedBy` definitions (now in `Regex.lean`)

### AlgorithmicTypingSoundness.lean
- Removed `regexBeq_refl`, `regexBeq_eq`, `eq_regexBeq` lemmas (now in `Regex.lean`)
- Removed `is_empty_sound`, `regexSubsumedBy_sound` theorems (now in `Regex.lean`)

### Checker.lean
- Removed dead import of deleted `AlgorithmicTypingCompleteness`
