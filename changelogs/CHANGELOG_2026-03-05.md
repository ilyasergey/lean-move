# Changelog — 2026-03-05

## Add enum support: AST, parser, translator, semantics, type checker stubs, and tests

### Summary

Added full enum/variant support to MoveLight across the entire pipeline:
MVIR syntax → parser → translator → MoveLight AST → macros → pretty
printers → semantics → type checker stubs → parsing tests. All 13 enum
`.mvir` test files from the Sui bytecode-verifier-transactional-tests
now parse and translate successfully.

### Design

Enums are modeled as tagged records:
- **Type level**: `BasicMoveType.tenum enumName variants` where `variants`
  maps variant names to their field type maps
- **Runtime**: `Value.variant variantName fields` (a tagged list of field-value pairs)
- Three unpack modes: owned (`E.V{f: x} = move(e)`),
  immutable borrow (`&E.V{f: x} = freeze(e)`),
  mutable borrow (`&mut E.V{f: x} = copy(e)`)

### Phase 1: MoveLight AST (`MoveLight.lean`)
- `BasicMoveType.tenum : Id → AssocMap Id (AssocMap Field BasicMoveType) → BasicMoveType`
- `Value.variant : Id → List (Field × Value) → Value`
- `Expr.packVariant : Id → Id → List (Field × Site) → Expr`
- `Stmt.unpackVariant : Id → List (Field × Site) → Site → Stmt → Stmt`
- `Stmt.variantSwitch : Site → List (Id × Label) → Stmt`
- `beqVariantEntries` mutual function + BEq simp lemmas + refl/soundness proofs
- `PathElement.variantField` for enum field paths

### Phase 2: Macros (`Macros.lean`)
- CPS macros: `packVariant(ename, vname, fields)`, `unpackVariant(vname, fields, src)`,
  `variantSwitch src cases`

### Phase 3: MVIR Syntax (`Syntax.lean`)
- `MvirExpr.packVariant`, `MvirStmt.unpackVariant`, `MvirStmt.variantSwitch`
- `MvirStmt.jumpIfFalse` for `jump_if_false` statements
- `MvirEnumDef` structure, `MvirModule.enums` field

### Phase 4: Parser (`Parser.lean`)
- Enum declaration parsing (`parseEnumDef`, `parseVariantDef`)
- Variant pack expression (`Enum.Variant<T>{f: e, ...}`)
- `variant_switch` statement
- Owned, `&`, and `&mut` variant unpack statements
- Binary operator parsing (`==`, `!=`, `>=`, `<=`, `>`, `<`, `+`, `-`, `/`, `%`)
- `jump_if_false` statement
- `commaSepTrailing` for trailing commas in struct/enum fields
- Integer literal suffix skip (`1u64`, `0u8`)
- `parseAbilities` handles `has {` (no abilities listed)

### Phase 5: Translator (`Translate.lean`)
- `ResolvedEnum` structure, `TransState.enums` field
- `resolveEnumDefs` resolves enum variant field types
- `resolveBasicType` extended with enum type name lookup
- `flattenExpr` handles `packVariant`
- `translateStmts` handles `unpackVariant`, `variantSwitch`, `jumpIfFalse`
- `jumpIfFalse` swaps branch labels (jump when condition is false)

### Phase 6: Pretty Printers
- `PrettyPrint.lean` (MoveLight): `tenum`, `packVariant`, `unpackVariant`, `variantSwitch` cases
- `MoveIR/PrettyPrint.lean`: `ppVariantMap`, `ppVariantEntries` for enum types

### Phase 7: Semantics (`Smallstep.lean`)
- Step cases for `packVariant` (construct variant value), `unpackVariant`
  (destructure variant, consume source site), `variantSwitch` (read variant
  tag through reference, dispatch to matching label)
- `readPath`/`writePath` extended for `Value.variant` (field access on variants)

### Phase 8: Type Checker Stubs
- **TypeChecking.lean**: Relational typing rules for `packVariant`, `unpackVariant`,
  `variantSwitch` with `sorry` proofs
- **AlgorithmicTypeChecking.lean**: Pattern match cases for enum constructs
  (packVariant builds single-variant tenum — known limitation)
- **Defs.lean**: ~14 `variant` cases in `cases v with` blocks
- **Types.lean**: `tenum`/`variantField` cases in `BasicMoveType`/`PathElement` functions
- **Progress.lean**: Zero sorrys — variantSwitch case fully proved with
  `lookup_mem_assoc` helper
- **Preservation.lean**: `sorry` stubs for packVariant, unpackVariant, variantSwitch
- **InitState.lean**: variant/tenum cases in `hasType_bool_sound`
- **Weakening.lean**, **StackSafeUtils.lean**, **AlgorithmicTypingSoundness.lean**:
  variant cases added

### Phase 9: Tests
- **Test_enum_match.lean**: Alpha-equivalence test comparing parsed `enum_match.mvir`
  against hand-written `FunDef` with packVariant, unpackVariant, variantSwitch macros
- **Test_enum_all_parse.lean**: All 13 enum `.mvir` files verified to parse and translate
  with exact function count guards
- **enum_match.lean** (typechecking): Parsing guards for enum_match.mvir
- Both test files added to `AllParseTests.lean`

### Files changed

| File | Changes |
|------|---------|
| `MoveLight.lean` | +tenum, variant, packVariant, unpackVariant, variantSwitch, BEq |
| `Macros.lean` | +3 CPS macros for enum constructs |
| `MoveIR/Syntax.lean` | +MvirEnumDef, enum MvirExpr/MvirStmt constructors, jumpIfFalse |
| `MoveIR/Parser.lean` | +enum/variant parsing, binop parsing, jump_if_false, commaSepTrailing |
| `MoveIR/Translate.lean` | +ResolvedEnum, enum translation, jumpIfFalse handling |
| `MoveIR/PrettyPrint.lean` | +variant type pretty printing |
| `Lang/PrettyPrint.lean` | +enum stmt/expr/type pretty printing |
| `Smallstep.lean` | +enum step cases, readPath/writePath for variants |
| `TypeChecking.lean` | +relational typing rules (sorry proofs) |
| `AlgorithmicTypeChecking.lean` | +pattern match cases for enum constructs |
| `Types.lean` | +tenum/variantField cases |
| `Defs.lean` | +variant cases in HasType, rmap proofs |
| `Progress.lean` | +variantSwitch proof (zero sorrys), lookup_mem_assoc |
| `Preservation.lean` | +sorry stubs for enum preservation |
| `InitState.lean` | +variant/tenum cases in hasType_bool_sound |
| `Weakening.lean` | +variant cases |
| `StackSafeUtils.lean` | +variant cases |
| `AlgorithmicTypingSoundness.lean` | +variant cases |
| `TestUtils.lean` | +enum alpha-equivalence (alphaVariantCases, alphaVariantMap) |
| `Test_enum_match.lean` | New: alpha-equivalence parsing test |
| `Test_enum_all_parse.lean` | New: all 13 enum files parse+translate test |
| `enum_match.lean` | New: typechecking test (parsing guards only) |
| 13 `.mvir` files | New: enum test cases from Sui bytecode-verifier |

### Build

368 jobs, all passing. Remaining sorrys are in Preservation.lean (enum
preservation stubs) and InitState.lean (variant HasType).
