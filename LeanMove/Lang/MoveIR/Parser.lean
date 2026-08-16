/-
 Copyright Ilya Sergey

 Licensed under the Apache License, Version 2.0 (the "License");
 you may not use this file except in compliance with the License.
 You may obtain a copy of the License at

      https://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software
 distributed under the License is distributed on an "AS IS" BASIS,
 WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 See the License for the specific language governing permissions and
 limitations under the License.
-/

import Std.Internal.Parsec.String
import LeanMove.Lang.MoveIR.Syntax

/-! ## MVIR Parser

Parsec-based parser for Move IR (.mvir) files. Parses into the intermediate
MVIR AST defined in `Syntax.lean`.
-/

namespace LeanMove.Lang.MoveIR.Parser

open Std.Internal.Parsec.String
open Std.Internal.Parsec
open LeanMove.Lang.MoveIR
open LeanMove.Lang.MoveLight (IntType)

/- ====================================================== -/
/-       Utility Combinators                               -/
/- ====================================================== -/

/-- Skip whitespace and line comments (both `//` and `//# ...`) -/
partial def skipWsAndComments : Parser Unit := do
  ws
  if ← isEof then return ()
  let isComment ← (attempt (do skipString "//"; pure true)) <|> pure false
  if isComment then
    let _ ← manyChars (satisfy (· ≠ '\n'))
    skipWsAndComments
  else
    pure ()

/-- Parse a specific keyword string, then skip whitespace -/
def keyword (s : String) : Parser Unit := do
  skipString s
  skipWsAndComments

/-- Parse a specific character, then skip whitespace -/
def symbol (c : Char) : Parser Unit := do
  skipChar c
  skipWsAndComments

/-- Check if a character is valid as an identifier start -/
def isIdentStart (c : Char) : Bool :=
  c.isAlpha || c == '_'

/-- Check if a character is valid in an identifier -/
def isIdentChar (c : Char) : Bool :=
  c.isAlphanum || c == '_'

/-- Parse an identifier (letters, digits, underscores) -/
def ident : Parser String := do
  let first ← satisfy isIdentStart
  let rest ← manyChars (satisfy isIdentChar)
  let name := String.ofList [first] ++ rest
  skipWsAndComments
  pure name

/-- Parse a natural number literal -/
def natLit : Parser Nat := do
  let n ← digits
  skipWsAndComments
  pure n

/-- Parse zero or more comma-separated items -/
partial def commaSep (p : Parser α) : Parser (List α) := do
  let first? ← (attempt (do let x ← p; pure (some x))) <|> pure none
  match first? with
  | none => pure []
  | some first =>
    let rest ← commaSepRest p
    pure (first :: rest)
where
  commaSepRest (p : Parser α) : Parser (List α) := do
    let hasComma ← (attempt (do symbol ','; pure true)) <|> pure false
    if hasComma then
      let x ← p
      let rest ← commaSepRest p
      pure (x :: rest)
    else
      pure []

/-- Parse one or more comma-separated items -/
partial def commaSep1 (p : Parser α) : Parser (List α) := do
  let first ← p
  let rest ← commaSepRest p
  pure (first :: rest)
where
  commaSepRest (p : Parser α) : Parser (List α) := do
    let hasComma ← (attempt (do symbol ','; pure true)) <|> pure false
    if hasComma then
      let x ← p
      let rest ← commaSepRest p
      pure (x :: rest)
    else
      pure []

/-- Parse zero or more comma-separated items, tolerating a trailing comma -/
partial def commaSepTrailing (p : Parser α) : Parser (List α) := do
  let first? ← (attempt (do let x ← p; pure (some x))) <|> pure none
  match first? with
  | none => pure []
  | some first =>
    let rest ← commaSepRestTrailing p
    pure (first :: rest)
where
  commaSepRestTrailing (p : Parser α) : Parser (List α) := do
    let hasComma ← (attempt (do symbol ','; pure true)) <|> pure false
    if hasComma then
      let next? ← (attempt (do let x ← p; pure (some x))) <|> pure none
      match next? with
      | some x =>
        let rest ← commaSepRestTrailing p
        pure (x :: rest)
      | none => pure []  -- trailing comma
    else
      pure []

/-- Parse items separated by `*` (for tuple return types like `&mut u64 * &mut u64`) -/
partial def starSep1 (p : Parser α) : Parser (List α) := do
  let first ← p
  let rest ← starSepRest p
  pure (first :: rest)
where
  starSepRest (p : Parser α) : Parser (List α) := do
    let hasStar ← (attempt (do symbol '*'; pure true)) <|> pure false
    if hasStar then
      let x ← p
      let rest ← starSepRest p
      pure (x :: rest)
    else
      pure []

/- ====================================================== -/
/-       Type Parser                                       -/
/- ====================================================== -/

/-- Parse a MVIR type -/
partial def parseType : Parser MvirType := do
  -- Check for reference types: &mut T or &T
  let isRef ← (attempt (do keyword "&mut"; pure (some true))) <|>
               (attempt (do symbol '&'; pure (some false))) <|>
               pure none
  match isRef with
  | some isMut =>
    let inner ← parseBaseType
    pure (.ref isMut inner)
  | none => parseBaseType
where
  /-- Parse a non-reference type -/
  parseBaseType : Parser MvirType := do
    let name ← ident
    match name with
    | "u8" => pure (.int .u8)
    | "u16" => pure (.int .u16)
    | "u32" => pure (.int .u32)
    | "u64" => pure (.int .u64)
    | "u128" => pure (.int .u128)
    | "u256" => pure (.int .u256)
    | "bool" => pure .bool
    | "vector" =>
      symbol '<'
      let inner ← parseType
      symbol '>'
      pure (.vector inner)
    | "Self" =>
      symbol '.'
      let structName ← ident
      pure (.struct s!"Self.{structName}")
    | other => pure (.struct other)

/- ====================================================== -/
/-       Expression Parser                                 -/
/- ====================================================== -/

/-- Parse a field borrow suffix: `.StructName::fieldName` -/
def parseFieldSuffix : Parser (String × String) := do
  symbol '.'
  let structName ← ident
  keyword "::"
  let fieldName ← ident
  pure (structName, fieldName)

mutual

/-- Parse a primary expression (no `&`, `&mut`, `*` prefix) -/
partial def parsePrimaryExpr : Parser MvirExpr := do
  let c ← peek!
  match c with
  | '(' =>
    symbol '('
    let e ← parseExpr
    -- MVIR writes a cast as `(expr as u8)`, so it is recognised here rather
    -- than as an operator: the `as` can only appear inside the parentheses.
    let cast? ← (attempt (do keyword "as"; let t ← parseType; pure (some t))) <|> pure none
    symbol ')'
    match cast? with
    | some (.int w) => pure (.cast w e)
    | some _ => fail "cast target must be an integer type"
    | none => pure e
  | _ =>
    let name ← attempt ident <|> fail "expected expression"
    match name with
    | "copy" =>
      symbol '('
      let var ← ident
      symbol ')'
      pure (.copy var)
    | "move" =>
      symbol '('
      let var ← ident
      symbol ')'
      pure (.move var)
    | "freeze" =>
      symbol '('
      let inner ← parseExpr
      symbol ')'
      pure (.freeze inner)
    | "true" => pure (.boolLit true)
    | "false" => pure (.boolLit false)
    | "Self" =>
      symbol '.'
      let funcName ← ident
      symbol '('
      let args ← commaSep parseExpr
      symbol ')'
      pure (.call funcName args)
    | other =>
      -- Vector operations: any identifier starting with "vec_"
      if other.startsWith "vec_" then
        symbol '<'
        let ty ← parseType
        symbol '>'
        symbol '('
        let args ← commaSep parseExpr
        symbol ')'
        pure (.vecOp other ty args)
      else
        -- Check for Enum.Variant pattern: Name.Name<T>{...} or Name.Name{...}
        let isDot ← (attempt (do
          let c ← peek!
          pure (c == '.'))) <|> pure false
        if isDot then
          -- Try variant pack: Enum.Variant<T>{...} or Enum.Variant{...}
          let vp? ← (attempt (do
            symbol '.'
            let variantName ← ident
            -- Skip optional type arguments <T>
            let _ ← (attempt (do
              symbol '<'
              let _ ← parseType
              symbol '>')) <|> pure ()
            symbol '{'
            let fields ← commaSep parsePackField
            symbol '}'
            pure (some (variantName, fields)))) <|> pure none
          match vp? with
          | some (variantName, fields) =>
            pure (.packVariant other variantName fields)
          | none =>
            -- Fallback: bare identifier
            pure (.copy other)
        else
          -- Check if it's a struct pack: Name { ... }
          let isBrace ← (attempt (do let c ← peek!; pure (c == '{'))) <|> pure false
          if isBrace then
            symbol '{'
            let fields ← commaSep parsePackField
            symbol '}'
            pure (.pack other fields)
          else
            -- Bare identifier (treat as implicit copy reference)
            pure (.copy other)

/-- Parse a field in a struct pack: `fieldName: expr` -/
partial def parsePackField : Parser (String × MvirExpr) := do
  let fieldName ← ident
  symbol ':'
  let value ← parseExpr
  pure (fieldName, value)

/-- Parse a unary expression (with prefix operators `&`, `&mut`, `*`) -/
partial def parseUnaryExpr : Parser MvirExpr := do
  skipWsAndComments
  if ← isEof then fail "unexpected eof in expression"
  let c ← peek!
  match c with
  | '&' =>
    -- Borrow expression (local or field)
    let isMut ← (attempt (do keyword "&mut"; pure true)) <|>
                 (do symbol '&'; pure false)
    parseBorrowBody isMut
  | '*' =>
    -- Deref expression
    symbol '*'
    let inner ← parseUnaryExpr
    pure (.deref inner)
  | '!' =>
    -- Boolean negation. `!=` is a binary operator, so only a `!` that is *not*
    -- immediately followed by `=` is the unary `Not`.
    --
    -- The lookahead `fail`s rather than reporting `false`: `attempt` rolls the
    -- position back on *error* only, so a lookahead that consumed the `!` and
    -- then returned `false` would drop into the fallback with the `!` already
    -- eaten. `skipChar`, not `symbol`, so that no whitespace is skipped before
    -- the `=` test — `! =` is a negation, `!=` is not.
    --
    -- The fallback is currently unreachable: `parseExpr` consumes a binary `!=`
    -- via `parseBinOp` after a complete left operand, so a `!` reaching here
    -- always starts a unary operator. Both spellings are therefore rejected the
    -- same way today; the point of restoring the position is that the branch
    -- stays correct if the grammar ever does reach it.
    let neg ← (attempt (do
      skipChar '!'
      let eof ← isEof
      if !eof then
        let next ← peek!
        if next == '=' then fail "`!=` is a binary operator, not a unary `!`"
      skipWsAndComments
      pure true)) <|> pure false
    if neg then
      let inner ← parseUnaryExpr
      pure (.unop "!" inner)
    else
      -- A `!=` in operand position is a syntax error; the `!` is still unconsumed.
      parsePrimaryExpr
  | _ =>
    if c.isDigit then
      let n ← natLit
      -- The width suffix (`1u8`) is significant: it is what distinguishes
      -- `LdU8` from `LdU64`. An unsuffixed literal defaults to `u64`, matching
      -- the MVIR convention. `keyword` is a bare `skipString`, so alternation
      -- order would matter if one suffix were a prefix of another — none is
      -- (`u16` vs `u128` already differ at the third character).
      let w ← (attempt (do keyword "u8"; pure IntType.u8)) <|>
              (attempt (do keyword "u16"; pure IntType.u16)) <|>
              (attempt (do keyword "u32"; pure IntType.u32)) <|>
              (attempt (do keyword "u64"; pure IntType.u64)) <|>
              (attempt (do keyword "u128"; pure IntType.u128)) <|>
              (attempt (do keyword "u256"; pure IntType.u256)) <|>
              pure IntType.u64
      pure (.intLit n w)
    else
      parsePrimaryExpr

/-- Try to parse a binary operator. Returns the operator string if found. -/
partial def parseBinOp : Parser (Option String) :=
  binaryOperators.foldr
    (fun op rest => (attempt (do keyword op; pure (some op))) <|> rest)
    (pure none)

/-- Parse a full expression: unary expression optionally followed by a binary operator -/
partial def parseExpr : Parser MvirExpr := do
  let lhs ← parseUnaryExpr
  let op? ← parseBinOp
  match op? with
  | some op =>
    let rhs ← parseUnaryExpr
    pure (.binop op lhs rhs)
  | none => pure lhs

/-- Parse the body of a borrow expression after `&` or `&mut`.
    Handles both local borrows (`&x`) and field borrows (`&copy(s).S::f`). -/
partial def parseBorrowBody (isMut : Bool) : Parser MvirExpr := do
  let inner ← parseBorrowInner
  -- Check for field suffix .StructName::field
  let suffix? ← (attempt (do let s ← parseFieldSuffix; pure (some s))) <|> pure none
  match suffix? with
  | some (structName, fieldName) =>
    pure (.fieldBorrow isMut inner structName fieldName)
  | none =>
    -- No field suffix → must be a local borrow like &x
    match inner with
    | .copy var => pure (.borrowLocal isMut var)
    | _ => fail "expected identifier for local borrow"

/-- Parse the inner expression of a borrow (limited forms: copy(x), move(x), (expr), ident) -/
partial def parseBorrowInner : Parser MvirExpr := do
  let c ← peek!
  match c with
  | '(' =>
    -- Parenthesized expression (possibly nested borrow)
    symbol '('
    let e ← parseExpr
    symbol ')'
    pure e
  | _ =>
    let name ← ident
    match name with
    | "copy" =>
      symbol '('
      let var ← ident
      symbol ')'
      pure (.copy var)
    | "move" =>
      symbol '('
      let var ← ident
      symbol ')'
      pure (.move var)
    | other =>
      -- Bare identifier (for local borrows: &a)
      pure (.copy other)

end

/- ====================================================== -/
/-       Statement Parser                                  -/
/- ====================================================== -/

/-- Parse remaining variable names in a multi-assignment (after first comma) -/
partial def parseMoreVars : Parser (List String) := do
  let hasComma ← (attempt (do symbol ','; pure true)) <|> pure false
  if hasComma then
    let v ← ident
    let rest ← parseMoreVars
    pure (v :: rest)
  else
    pure []

/-- Parse a field in an unpack: `fieldName: varName` -/
def parseUnpackField : Parser (String × String) := do
  let fieldName ← ident
  symbol ':'
  let varName ← ident
  pure (fieldName, varName)

/-- Parse a single statement -/
partial def parseStmt : Parser MvirStmt := do
  skipWsAndComments
  let c ← peek!
  match c with
  | '*' =>
    -- writeRef: *expr = expr;
    symbol '*'
    let target ← parseExpr
    symbol '='
    let value ← parseExpr
    symbol ';'
    pure (.writeRef target value)
  | '&' =>
    -- &mut Enum.Variant<T>{ f: var, ... } = expr;  (mutable borrow variant unpack)
    -- &Enum.Variant<T>{ f: var, ... } = expr;  (immutable borrow variant unpack)
    let isMut ← (attempt (do keyword "&mut"; pure true)) <|>
                 (do symbol '&'; pure false)
    let enumName ← ident
    symbol '.'
    let variantName ← ident
    -- Skip optional type arguments <T>
    let _ ← (attempt (do
      symbol '<'
      let _ ← parseType
      symbol '>')) <|> pure ()
    symbol '{'
    let fields ← commaSep parseUnpackField
    symbol '}'
    symbol '='
    let rhs ← parseExpr
    symbol ';'
    pure (.unpackVariant (some isMut) enumName variantName fields rhs)
  | _ =>
    let name ← attempt ident <|> fail "expected statement"
    match name with
    | "jump_if_false" =>
      symbol '('
      let cond ← parseExpr
      symbol ')'
      let label ← ident
      symbol ';'
      pure (.jumpIfFalse cond label)
    | "jump_if" =>
      symbol '('
      let cond ← parseExpr
      symbol ')'
      let label ← ident
      symbol ';'
      pure (.jumpIf cond label)
    | "jump" =>
      let label ← ident
      symbol ';'
      pure (.jump label)
    | "return" =>
      -- Check for void return (just semicolon)
      let isSemicolon ← (attempt (do symbol ';'; pure true)) <|> pure false
      if isSemicolon then
        pure (.ret [])
      else
        let exprs ← commaSep1 parseExpr
        symbol ';'
        pure (.ret exprs)
    | "abort" =>
      let e ← parseExpr
      symbol ';'
      pure (.abort e)
    | "variant_switch" =>
      let enumName ← ident
      symbol '('
      let src ← parseExpr
      symbol ')'
      symbol '{'
      let cases ← commaSep (do
        let vname ← ident
        symbol ':'
        let label ← ident
        pure (vname, label))
      symbol '}'
      symbol ';'
      pure (.variantSwitch enumName src cases)
    | "_" =>
      -- Discard assignment: _ = expr;
      symbol '='
      let rhs ← parseExpr
      symbol ';'
      pure (.assign ["_"] rhs)
    | other =>
      -- Bare Self.method(args); call as statement (no assignment)
      if other == "Self" then
        let isDot ← (attempt (do let c ← peek!; pure (c == '.'))) <|> pure false
        if isDot then
          symbol '.'
          let funcName ← ident
          symbol '('
          let args ← commaSep parseExpr
          symbol ')'
          symbol ';'
          pure (.assign ["_"] (.call funcName args))
        else
          fail "expected '.' after 'Self'"
      -- Bare vec_op<T>(args); as statement (no assignment)
      else if other.startsWith "vec_" then
        let isAngle ← (attempt (do let c ← peek!; pure (c == '<'))) <|> pure false
        if isAngle then
          symbol '<'
          let ty ← parseType
          symbol '>'
          symbol '('
          let args ← commaSep parseExpr
          symbol ')'
          symbol ';'
          pure (.assign ["_"] (.vecOp other ty args))
        else
          -- Fall through to assignment parsing
          let moreVars ← parseMoreVars
          let allVars := other :: moreVars
          symbol '='
          let rhs ← parseExpr
          symbol ';'
          pure (.assign allVars rhs)
      else
        -- Check for Enum.Variant unpack: EnumName.VariantName<T>{ f: var, ... } = expr;
        let isDot ← (attempt (do let c ← peek!; pure (c == '.'))) <|> pure false
        if isDot then
          let vu? ← (attempt (do
            symbol '.'
            let variantName ← ident
            -- Skip optional type arguments <T>
            let _ ← (attempt (do
              symbol '<'
              let _ ← parseType
              symbol '>')) <|> pure ()
            symbol '{'
            let fields ← commaSep parseUnpackField
            symbol '}'
            symbol '='
            let rhs ← parseExpr
            symbol ';'
            pure (some (variantName, fields, rhs)))) <|> pure none
          match vu? with
          | some (variantName, fields, rhs) =>
            pure (.unpackVariant none other variantName fields rhs)
          | none =>
            fail s!"unexpected '.' after '{other}'"
        else
        -- Check if it's an unpack: StructName { f: v, ... } = expr;
        let isBrace ← (attempt (do let c ← peek!; pure (c == '{'))) <|> pure false
        if isBrace then
          symbol '{'
          let fields ← commaSep parseUnpackField
          symbol '}'
          symbol '='
          let rhs ← parseExpr
          symbol ';'
          pure (.unpack other fields rhs)
        else
          -- Regular assignment or multi-assignment: x = e; or x, y = e;
          let moreVars ← parseMoreVars
          let allVars := other :: moreVars
          symbol '='
          let rhs ← parseExpr
          symbol ';'
          pure (.assign allVars rhs)

/- ====================================================== -/
/-       Block Parser                                      -/
/- ====================================================== -/

/-- Parse a list of statements until the next statement fails to parse
    (hits a label declaration, closing brace, or EOF) -/
partial def parseStmts : Parser (List MvirStmt) := do
  skipWsAndComments
  if ← isEof then return []
  let c ← peek!
  if c == '}' then return []
  -- Try to parse a statement. If it fails (e.g., at "label"), attempt backtracks.
  let stmt? ← (attempt (do let s ← parseStmt; pure (some s))) <|> pure none
  match stmt? with
  | some stmt =>
    let rest ← parseStmts
    pure (stmt :: rest)
  | none => pure []

/-- Parse a labeled block: `label L: stmts` -/
def parseBlock : Parser MvirBlock := do
  keyword "label"
  let label ← ident
  symbol ':'
  let stmts ← parseStmts
  pure { label, stmts }

/-- Parse zero or more blocks. Uses `attempt` to try each block and stop
    when parsing fails (at closing brace or EOF). -/
partial def parseBlocks : Parser (List MvirBlock) := do
  skipWsAndComments
  if ← isEof then return []
  let c ← peek!
  if c == '}' then return []
  let block? ← (attempt (do let b ← parseBlock; pure (some b))) <|> pure none
  match block? with
  | some block =>
    let rest ← parseBlocks
    pure (block :: rest)
  | none => pure []

/- ====================================================== -/
/-       Function & Struct Parsers                         -/
/- ====================================================== -/

/-- Parse a function parameter: `name: type` -/
def parseParam : Parser MvirParam := do
  let name ← ident
  symbol ':'
  let ty ← parseType
  pure { name, type := ty }

/-- Parse a local variable declaration: `let name: type;` -/
def parseLocal : Parser MvirParam := do
  keyword "let"
  let name ← ident
  symbol ':'
  let ty ← parseType
  symbol ';'
  pure { name, type := ty }

/-- Parse zero or more local declarations. Uses `attempt` to try each local
    and stop when parsing fails (at label or other non-local). -/
partial def parseLocals : Parser (List MvirParam) := do
  skipWsAndComments
  let loc? ← (attempt (do let l ← parseLocal; pure (some l))) <|> pure none
  match loc? with
  | some loc =>
    let rest ← parseLocals
    pure (loc :: rest)
  | none => pure []

/-- Parse return type(s) after `:` (or nothing for void functions) -/
def parseReturnTypes : Parser (List MvirType) := do
  let hasColon ← (attempt (do symbol ':'; pure true)) <|> pure false
  if hasColon then
    starSep1 parseType
  else
    pure []

/-- Parse a function definition: `[public] [entry] name(params): retTypes { locals; blocks }` -/
def parseFunDef : Parser MvirFunDef := do
  -- Skip optional function modifiers (public, entry)
  let _ ← (attempt (keyword "public")) <|> pure ()
  let _ ← (attempt (keyword "entry")) <|> pure ()
  let name ← ident
  symbol '('
  let params ← commaSep parseParam
  symbol ')'
  let returnTypes ← parseReturnTypes
  symbol '{'
  let locals ← parseLocals
  let blocks ← parseBlocks
  symbol '}'
  pure { name, params, returnTypes, locals, blocks }

/-- Parse struct/enum abilities: `has copy, drop, store` or `has` with no abilities -/
def parseAbilities : Parser (List String) := do
  let hasKw ← (attempt (do keyword "has"; pure true)) <|> pure false
  if hasKw then
    -- Peek: if next char is '{', no abilities listed
    let c ← peek!
    if c == '{' then pure []
    else commaSep1 ident
  else
    pure []

/-- Parse a struct field: `fieldName: type` -/
def parseStructField : Parser MvirStructField := do
  let name ← ident
  symbol ':'
  let ty ← parseType
  pure { name, type := ty }

/-- Parse a struct definition: `struct S has ... { fields }` -/
def parseStructDef : Parser MvirStructDef := do
  keyword "struct"
  let name ← ident
  let abilities ← parseAbilities
  symbol '{'
  let fields ← commaSepTrailing parseStructField
  symbol '}'
  pure { name, abilities, fields }

/-- Parse a variant definition: `VariantName { fields }` -/
def parseVariantDef : Parser (String × List MvirStructField) := do
  let vname ← ident
  symbol '{'
  let fields ← commaSepTrailing parseStructField
  symbol '}'
  pure (vname, fields)

/-- Parse an enum definition: `enum E has ... { V1 { fields }, V2 { fields } }` -/
def parseEnumDef : Parser MvirEnumDef := do
  keyword "enum"
  let name ← ident
  -- Skip optional type parameters like <T>
  let _ ← (attempt (do
    symbol '<'
    let _ ← ident  -- type parameter name
    symbol '>')) <|> pure ()
  let abilities ← parseAbilities
  symbol '{'
  let variants ← commaSepTrailing parseVariantDef
  symbol '}'
  pure { name, abilities, variants }

/- ====================================================== -/
/-       Module Parser                                     -/
/- ====================================================== -/

/-- Parse module members (interleaved struct, enum, and function definitions). -/
partial def parseModuleMembers :
    Parser (List MvirStructDef × List MvirEnumDef × List MvirFunDef) := do
  skipWsAndComments
  if ← isEof then return ([], [], [])
  let c ← peek!
  if c == '}' then return ([], [], [])
  -- Try struct definition first
  let sd? ← (attempt (do let sd ← parseStructDef; pure (some sd))) <|> pure none
  match sd? with
  | some sd =>
    let (structs, enums, funs) ← parseModuleMembers
    pure (sd :: structs, enums, funs)
  | none =>
    -- Try enum definition
    let ed? ← (attempt (do let ed ← parseEnumDef; pure (some ed))) <|> pure none
    match ed? with
    | some ed =>
      let (structs, enums, funs) ← parseModuleMembers
      pure (structs, ed :: enums, funs)
    | none =>
      -- Try function definition
      let fd? ← (attempt (do let fd ← parseFunDef; pure (some fd))) <|> pure none
      match fd? with
      | some fd =>
        let (structs, enums, funs) ← parseModuleMembers
        pure (structs, enums, fd :: funs)
      | none => pure ([], [], [])

/-- Parse a module address: `0xN` -/
def parseAddress : Parser String := do
  let _ ← pstring "0x"
  let hexStr ← many1Chars (satisfy fun c =>
    c.isDigit || (c >= 'a' && c <= 'f') || (c >= 'A' && c <= 'F'))
  skipWsAndComments
  pure s!"0x{hexStr}"

/-- Parse a module: `module 0xN.name { structs; functions }` -/
def parseModule : Parser MvirModule := do
  keyword "module"
  let addr ← parseAddress
  symbol '.'
  let name ← ident
  symbol '{'
  let (structs, enums, functions) ← parseModuleMembers
  symbol '}'
  pure { address := addr, name, structs, enums, functions }

/- ====================================================== -/
/-       Top-Level File Parser                             -/
/- ====================================================== -/

/-- Parse zero or more modules. Uses `attempt` to try each module. -/
partial def parseModules : Parser (List MvirModule) := do
  skipWsAndComments
  if ← isEof then return []
  let m? ← (attempt (do let m ← parseModule; pure (some m))) <|> pure none
  match m? with
  | some m =>
    let rest ← parseModules
    pure (m :: rest)
  | none => pure []

/-- Parse a complete MVIR file -/
def parseFile : Parser MvirFile := do
  skipWsAndComments
  let modules ← parseModules
  skipWsAndComments
  pure { modules }

/-- Run the MVIR parser on a string -/
def parseMvir (input : String) : Except String MvirFile :=
  Parser.run parseFile input

end LeanMove.Lang.MoveIR.Parser
