# Changelog — 2026-02-22b

## MVIR Parser, `Stmt.call` integration, `patch_root_outbound` weakening proofs, and pretty-printer

### Summary

This change introduces three major pieces of functionality:

1. **`patch_root_outbound` + `extend_with_star_no_outbound`**: New path environment operations
   in the type checker that refine how mutable call outputs interact with later borrows.
   After extending mutable outputs from inputs (Rule 2 of `call_connect_inputs_outputs`),
   `patch_root_outbound` sets each mutable output's outbound path to `.root` to `ε`, restoring
   aliasing detection for subsequent borrows. All Weakening.lean proofs updated accordingly.

2. **`Stmt.call` in examples**: Two hand-written examples (`multible_mutable_return_values` and
   `mutable_borrows_are_not_unique_calls_invalid`) updated to use `Stmt.call` instead of inlining
   the callee body. Runtime tests updated with function environments for call dispatch.

3. **MVIR Parser infrastructure**: Complete two-phase parser (`.mvir` text → intermediate AST →
   MoveLight `FunDef`) with 13 parse tests covering all existing `.mvir` example programs, alpha-
   equivalence checking, and a pretty-printer that converts `FunDef` values back to readable Lean
   code using the macro syntax.

### Problem

After adding `patch_root_outbound` as a new step in `call_connect_inputs_outputs` (between Rule 2
and Rule 3), the Weakening.lean proofs broke: the subsumption lemma `call_connect_subsumes_self`
and the path inclusion lemma `path_inclusion_via_triple_foldl` both needed to account for the new
patching step. Additionally, two example files still inlined callee bodies instead of using the
new `Stmt.call` construct, and the MVIR parser needed a pretty-printer for inspecting translated
output.

### Key changes

#### Types.lean (+31 lines)
- **`extend_with_star_no_outbound`**: Like `extend_with_star` but only adds inbound paths (from
  other refs to the target) with no outbound paths from the target. Used for mutable call outputs
  because the callee's return rule (`ret_mutable_writable_bool` + `ret_mutable_no_aliases_bool`)
  guarantees mutable returned refs are immediately writable.
- **`patch_root_outbound`**: After extending mutable outputs with no outbound, patches their
  outbound to `.root` to `ε`. This restores aliasing detection: when a later `borrowImm`/
  `borrowMut` creates ref `r3` via `update_with_extension(r3, .root, path)`, the path from
  `mout` to `r3` becomes `G(mout, .root) ∘ path = ε ∘ path = path ≠ ∅`, so
  `check_outbound_bool` blocks writes through `mout` when conflicting borrows exist.

#### TypeChecking.lean (+22/-8 lines)
- `call_connect_inputs_outputs` now has 4 steps:
  1. Rule 1: `extend_with_star` for immutable outputs from inputs
  2. Rule 2: `extend_with_star_no_outbound` for mutable outputs from mutable inputs
  3. **Patch** (new): `patch_root_outbound` for mutable outputs
  4. Rule 3: conditional `extend_with_star` for immutable output pairs

#### TypesUtils.lean (+209 lines)
- `extend_with_star_no_outbound_wellformed`: PathEnv.WellFormed preservation
- `extend_with_star_no_outbound_refs_mono`: monotonicity of refs
- `extend_with_star_no_outbound_refs_eq`: refs equality lemma
- `extend_with_star_no_outbound_paths_from/to_non_member`: path emptiness for non-members
- `extend_with_star_no_outbound_self_loop`: self-loop only accepts nil
- `extend_with_star_no_outbound_target_mem`: target membership after extension

#### Weakening.lean (+526 lines, net ~+440)
- **`patch_root_outbound` helper lemmas** (new, ~110 lines):
  - `patch_root_outbound_self_loop_only_empty`
  - `patch_root_outbound_refs_eq`
  - `patch_root_outbound_paths_from_nm` / `patch_root_outbound_paths_to_nm`
  - `patch_root_outbound_path_incl` (substitution-based path inclusion)
  - `patch_root_outbound_path_mono` (monotonicity for isolated mutable outputs)
- **`call_connect_refs_mono`**: Updated for `extend_with_star_no_outbound` refs monotonicity
- **`path_inclusion_via_triple_foldl`**: Added patch step between Rule 2 and Rule 3,
  using `patch_root_outbound_path_incl`
- **`call_connect_subsumes_self`**: Added `h_patch` step using `patch_root_outbound_path_mono`
- **`outer_foldl_cond_ews_patch_refs_eq`**: New helper for refs equality through patching

#### multible_mutable_return_values.lean (rewritten)
- `borrow` now returns `[⟨.u64, some true⟩, ⟨.u64, some true⟩]` with `ret [s1, s3]`
- `write` uses `(call([ws1, ws2], "borrow", [ws0]))` instead of inlining both field borrows
- Added `borrow_sig : FunSig` and `write_funEnv : FunEnv` mapping `"borrow"` to its signature
- Type-checking tests updated with function environment

#### mutable_borrows_are_not_unique_calls_invalid.lean (+48 lines)
- Added `borrow_f : FunDef` (the callee returning `&mut s.f`)
- Added `borrow_f_sig : FunSig` and `call_funEnv : FunEnv`
- `call_and_write_invalid` uses `(call([s1], "borrow_f", [s0]))` instead of inline
  `borrowMutField`

#### AllTests.lean (runtime tests, +20 lines)
- Added `rtFunEnv` / `rtFte` for `multible_mutable_return_values`: maps `"borrow"` →
  `borrow` FunDef for runtime dispatch
- Added `rtFunEnv2` / `rtFte2` for `mutable_borrows_are_not_unique_calls_invalid`: maps
  `"borrow_f"` → `borrow_f` FunDef
- Updated `run` and `type_soundness_dec` calls to pass function environments

#### MVIR Parser (new, ~1315 lines across 4 files)
- **Syntax.lean** (112 lines): Intermediate MVIR AST types (`MvirExpr`, `MvirStmt`, `MvirBlock`,
  `MvirFunDef`, `MvirModule`, `MvirFile`)
- **Parser.lean** (583 lines): Parsec-based parser for `.mvir` text; handles `copy`, `move`,
  `&`/`&mut`, field borrows, struct pack/unpack, function calls, `jump_if` with fallthrough,
  multi-return, line comments, `//# publish` directives
- **Translate.lean** (404 lines): MVIR → MoveLight ANF translation; expression flattening into
  `letBind` chains with fresh sites; struct type resolution; `jump_if` → `branch` with
  fallthrough label; sequential `refid` assignment for local ref-typed variables
- **PrettyPrint.lean** (196 lines): MoveLight `FunDef` → readable Lean code using macro syntax
  (`letsite`, `;;`, `copy`, `borrowMutField`, `call(...)`, `*a ::= b`, `ret`, etc.)

#### Parse Tests (new, ~1348 lines across 13 files)
- **TestUtils.lean** (344 lines): Alpha-equivalence checker (`alphaEquivFunDef`) with bijective
  site/aref/label renaming, permutation-tolerant `letBind` matching, and convenience functions
  (`parseAndTranslate`, `findFun`, `findFunInModule`)
- **12 test files** (one per `.mvir` example): Each embeds MVIR source, checks parse success,
  translation success, and (where hand-written examples exist) alpha-equivalence
- **Test_PrettyPrint.lean** (174 lines): Pretty-printer tests with output verification —
  tests simple functions (borrow_f, write with call) and multi-block (branch with entry/else/then)
- **AllParseTests.lean**: Imports all 13 test files; buildable via `lake build parsing`

#### Build Integration
- **lakefile.lean**: Added `parsing` build target; default `lake build` now includes parse tests
- **Lang.lean**: Added `import LeanMove.Lang.MoveIR.MoveIR`
- **MoveIR.lean**: Re-exports Syntax, Parser, Translate, PrettyPrint

### File stats

| File | Lines changed |
|------|---------------|
| `Types.lean` | +31 |
| `TypeChecking.lean` | +22/-8 |
| `TypesUtils.lean` | +209 |
| `Weakening.lean` | +526 (net ~+440) |
| `multible_mutable_return_values.lean` | rewritten (~135 lines) |
| `mutable_borrows_are_not_unique_calls_invalid.lean` | +48 |
| `AllTests.lean` | +20 |
| Parser infrastructure (4 new files) | +1,315 |
| Parse tests (13 new files + AllParseTests) | +1,371 |
| `lakefile.lean` | +8 |
| `Lang.lean` | +1 |
| Other examples (3 files, minor) | ~10 |

### Result

`lake build` succeeds (348 jobs). All 12 accepted examples type-check, all rejected examples
are still rejected. All 13 parse tests pass (including alpha-equivalence checks for examples
with hand-written counterparts). Pretty-printer output verified for simple, call-based, and
multi-block programs.
