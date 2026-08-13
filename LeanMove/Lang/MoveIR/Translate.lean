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

import LeanMove.Lang.MoveLight
import LeanMove.Lang.MoveIR.Syntax

/-! ## MVIR → MoveLight Translation

Translates the intermediate MVIR AST to MoveLight's A-normal form representation.
This involves:
1. Flattening nested expressions into sequences of `letBind` with fresh sites
2. Resolving struct types (Self.S → trecord)
3. Converting `jump_if` to `branch` with fallthrough label
4. Assigning Arefs to parameters (paramRef) and locals (refid)
-/

namespace LeanMove.Lang.MoveIR.Translate

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Lang.MoveIR
open AssocMap

/- ====================================================== -/
/-       Translation State                                 -/
/- ====================================================== -/

/-- Resolved struct definition with its MoveLight type -/
structure ResolvedStruct where
  name : String
  basicType : BasicMoveType
  fieldMap : AssocMap Field BasicMoveType
deriving Repr

instance : Inhabited ResolvedStruct where
  default := { name := "", basicType := .u64, fieldMap := empty }

/-- Resolved enum definition with its MoveLight type -/
structure ResolvedEnum where
  name : String
  basicType : BasicMoveType
  variants : AssocMap Id (AssocMap Field BasicMoveType)
deriving Repr

instance : Inhabited ResolvedEnum where
  default := { name := "", basicType := .u64, variants := empty }

/-- Translation state for ANF conversion -/
structure TransState where
  nextSiteId : Nat := 0
  nextRefId : Nat := 1  -- start from 1; 0 is sometimes special
  structs : List ResolvedStruct := []
  enums : List ResolvedEnum := []
  moduleName : String := ""
deriving Repr, Inhabited

abbrev TransM := StateM TransState

/-- Generate a fresh site -/
def freshSite : TransM Site := do
  let s ← get
  set { s with nextSiteId := s.nextSiteId + 1 }
  pure (.site s.nextSiteId)

/-- Generate a fresh refid -/
def freshRefId : TransM Aref := do
  let s ← get
  set { s with nextRefId := s.nextRefId + 1 }
  pure (.refid s.nextRefId)

/- ====================================================== -/
/-       Struct Type Resolution                            -/
/- ====================================================== -/

/-- Resolve a MVIR type to BasicMoveType using the struct definitions in scope -/
partial def resolveBasicType (structs : List ResolvedStruct)
    (enums : List ResolvedEnum) : MvirType → BasicMoveType
  | .u64 => .u64
  | .u8 => .u8
  | .bool => .tbool
  | .unit => .tunit
  | .struct name =>
    -- Look up struct by name (try both "Self.S" and "S" forms)
    let shortName := if name.startsWith "Self." then name.drop 5 else name
    match structs.find? (fun s => s.name == shortName) with
    | some rs => rs.basicType
    | none =>
      -- Try enum lookup (enum names are module-qualified, so match suffix)
      match enums.find? (fun e => e.name == shortName || e.name.endsWith ("." ++ shortName)) with
      | some re => re.basicType
      | none => .u64 -- fallback for unknown types
  | .vector inner => .tvec (resolveBasicType structs enums inner)
  | .ref _ inner => resolveBasicType structs enums inner

/-- Resolve a MVIR type to MoveType -/
def resolveType (structs : List ResolvedStruct) (enums : List ResolvedEnum)
    (aref : Aref) : MvirType → MoveType
  | .ref true inner => .ref (resolveBasicType structs enums inner) aref .siteBorrowMut
  | .ref false inner => .ref (resolveBasicType structs enums inner) aref .siteBorrowImm
  | other => .basic (resolveBasicType structs enums other)

/-- Resolve a MVIR type to ParamType (for return types) -/
def resolveParamType (structs : List ResolvedStruct) (enums : List ResolvedEnum) :
    MvirType → ParamType
  | .ref true inner => ⟨resolveBasicType structs enums inner, some true⟩
  | .ref false inner => ⟨resolveBasicType structs enums inner, some false⟩
  | other => ⟨resolveBasicType structs enums other, none⟩

/-- Build a BasicMoveType.trecord from struct fields -/
def buildRecordType (structs : List ResolvedStruct) (enums : List ResolvedEnum)
    (fields : List MvirStructField) : BasicMoveType :=
  let fieldMap := fields.foldl (fun acc f =>
    insert acc ⟨f.name⟩ (resolveBasicType structs enums f.type)) empty
  .trecord fieldMap

/-- Resolve struct definitions within a module.
    Must be called before translating functions since structs may reference each other.
    Uses iterative resolution: each pass resolves one more level of struct nesting.
    After n passes (where n = number of structs), all nesting is fully resolved. -/
partial def resolveStructDefs (_moduleName : String) (defs : List MvirStructDef) :
    List ResolvedStruct :=
  let resolveOnce (current : List ResolvedStruct) : List ResolvedStruct :=
    defs.map fun sd =>
      let bt := buildRecordType current [] sd.fields
      let fieldMap := sd.fields.foldl (fun acc f =>
        insert acc ⟨f.name⟩ (resolveBasicType current [] f.type)) empty
      { name := sd.name, basicType := bt, fieldMap }
  -- Start with placeholder stubs, then iterate n times to resolve all nesting levels
  let initial := defs.map fun sd =>
    { name := sd.name, basicType := .u64, fieldMap := empty }
  let rec iterate (current : List ResolvedStruct) : Nat → List ResolvedStruct
    | 0 => current
    | n + 1 => iterate (resolveOnce current) n
  iterate initial defs.length

/-- Resolve enum definitions within a module. Called after struct resolution.
    Enum names are qualified with the module name to avoid cross-module collisions. -/
partial def resolveEnumDefs (moduleName : String) (structs : List ResolvedStruct)
    (defs : List MvirEnumDef) : List ResolvedEnum :=
  defs.map fun ed =>
    let qualifiedName := moduleName ++ "." ++ ed.name
    let variants := ed.variants.foldl (fun acc (vname, fields) =>
      let fieldMap := fields.foldl (fun fm f =>
        insert fm ⟨f.name⟩ (resolveBasicType structs [] f.type)) empty
      insert acc vname fieldMap) empty
    { name := qualifiedName, basicType := .tenum qualifiedName, variants }

/- ====================================================== -/
/-       Expression Flattening (ANF conversion)            -/
/- ====================================================== -/

/-- Result of flattening: a list of letBind entries and the final result site -/
structure FlatResult where
  bindings : List (Site × Expr)
  result : Site
deriving Repr, Inhabited

/-- Wrap a list of bindings around a continuation statement -/
def wrapBindings (bindings : List (Site × Expr)) (cont : Stmt) : Stmt :=
  bindings.foldr (fun (s, e) acc => .letBind s e acc) cont

/-- Flatten a MVIR expression into ANF bindings -/
partial def flattenExpr (e : MvirExpr) : TransM FlatResult := do
  let structs := (← get).structs
  let enums := (← get).enums
  match e with
  | .copy var =>
    let s ← freshSite
    pure { bindings := [(s, .usage (.copy ⟨var⟩))], result := s }
  | .move var =>
    let s ← freshSite
    pure { bindings := [(s, .usage (.move ⟨var⟩))], result := s }
  | .borrowLocal false var =>
    let s ← freshSite
    pure { bindings := [(s, .usage (.borrowImm ⟨var⟩))], result := s }
  | .borrowLocal true var =>
    let s ← freshSite
    pure { bindings := [(s, .usage (.borrowMut ⟨var⟩))], result := s }
  | .intLit n =>
    let s ← freshSite
    pure { bindings := [(s, .intLit n)], result := s }
  | .boolLit _ =>
    -- MoveLight doesn't have a boolLit expression; encode as intLit 0/1
    let s ← freshSite
    pure { bindings := [(s, .intLit (if e matches .boolLit true then 1 else 0))], result := s }
  | .fieldBorrow isMut inner structName fieldName =>
    -- Flatten inner expression first, then field borrow
    let innerR ← flattenExpr inner
    let s ← freshSite
    -- Look up struct type for the field borrow
    let shortName := if structName.startsWith "Self." then structName.drop 5 else structName
    let bt := match structs.find? (fun rs => rs.name == shortName) with
      | some rs => rs.basicType
      | none => .u64
    let expr := if isMut then
      Expr.borrowMutField innerR.result bt ⟨fieldName⟩
    else
      Expr.borrowField innerR.result bt ⟨fieldName⟩
    pure { bindings := innerR.bindings ++ [(s, expr)], result := s }
  | .deref inner =>
    let innerR ← flattenExpr inner
    let s ← freshSite
    pure { bindings := innerR.bindings ++ [(s, .readRef innerR.result)], result := s }
  | .freeze inner =>
    let innerR ← flattenExpr inner
    let s ← freshSite
    pure { bindings := innerR.bindings ++ [(s, .freeze innerR.result)], result := s }
  | .pack structName fields =>
    -- Flatten each field value
    let mut allBindings : List (Site × Expr) := []
    let mut fieldSites : List (Field × Site) := []
    for (fname, fexpr) in fields do
      let fr ← flattenExpr fexpr
      allBindings := allBindings ++ fr.bindings
      fieldSites := fieldSites ++ [(⟨fname⟩, fr.result)]
    let s ← freshSite
    pure { bindings := allBindings ++ [(s, .pack structName fieldSites)], result := s }
  | .call _funcName args =>
    -- Calls should be handled at statement level (x = Self.f(args)).
    -- This branch handles the rare case of a call in expression context.
    -- Flatten arguments but note the call itself needs Stmt.call, not Expr.
    let mut allBindings : List (Site × Expr) := []
    for arg in args do
      let ar ← flattenExpr arg
      allBindings := allBindings ++ ar.bindings
    let s ← freshSite
    pure { bindings := allBindings, result := s }
  | .binop op lhs rhs =>
    let lhsR ← flattenExpr lhs
    let rhsR ← flattenExpr rhs
    let s ← freshSite
    let binopKind := match op with
      | "+" => Binop.add
      | "-" => Binop.sub
      | "*" => Binop.mul
      | "/" => Binop.div
      | "%" => Binop.mod
      | "==" => Binop.eq
      | "<" => Binop.lt
      | "&&" => Binop.and
      | "||" => Binop.or
      -- FIXME: `!=`, `>=`, `<=` and `>` parse but have no MoveLight Binop, so they
      -- fall through to `add` here and are silently mistranslated. Adding the
      -- Neq/Ge/Le/Gt opcodes would remove this fallback.
      | _ => Binop.add -- fallback
    pure { bindings := lhsR.bindings ++ rhsR.bindings ++
           [(s, .binop binopKind lhsR.result rhsR.result)], result := s }
  | .unop op operand =>
    let operandR ← flattenExpr operand
    let s ← freshSite
    let unopKind := match op with
      | "!" => Unop.not
      | _ => Unop.not -- only `!` is produced by the parser
    pure { bindings := operandR.bindings ++ [(s, .unop unopKind operandR.result)],
           result := s }
  | .vecOp opName ty args =>
    let elemTy := resolveBasicType structs enums ty
    match opName with
    | "vec_len" =>
      -- vec_len<T>(ref) → Expr.vecLen ref
      match args with
      | [refArg] =>
        let refR ← flattenExpr refArg
        let s ← freshSite
        pure { bindings := refR.bindings ++ [(s, .vecLen refR.result)], result := s }
      | _ =>
        let s ← freshSite
        pure { bindings := [(s, .intLit 0)], result := s }
    | "vec_imm_borrow" =>
      -- vec_imm_borrow<T>(ref, idx) → Expr.vecImmBorrow ref idx
      match args with
      | [refArg, idxArg] =>
        let refR ← flattenExpr refArg
        let idxR ← flattenExpr idxArg
        let s ← freshSite
        pure { bindings := refR.bindings ++ idxR.bindings ++
               [(s, .vecImmBorrow refR.result idxR.result)], result := s }
      | _ =>
        let s ← freshSite
        pure { bindings := [(s, .intLit 0)], result := s }
    | "vec_mut_borrow" =>
      -- vec_mut_borrow<T>(ref, idx) → Expr.vecMutBorrow ref idx
      match args with
      | [refArg, idxArg] =>
        let refR ← flattenExpr refArg
        let idxR ← flattenExpr idxArg
        let s ← freshSite
        pure { bindings := refR.bindings ++ idxR.bindings ++
               [(s, .vecMutBorrow refR.result idxR.result)], result := s }
      | _ =>
        let s ← freshSite
        pure { bindings := [(s, .intLit 0)], result := s }
    | "vec_pop_back" =>
      -- vec_pop_back<T>(ref) → Expr.vecPopBack ref
      match args with
      | [refArg] =>
        let refR ← flattenExpr refArg
        let s ← freshSite
        pure { bindings := refR.bindings ++ [(s, .vecPopBack refR.result)], result := s }
      | _ =>
        let s ← freshSite
        pure { bindings := [(s, .intLit 0)], result := s }
    | _ =>
      -- vec_pack_0, vec_pack_N, vec_push_back, vec_swap, vec_unpack_N
      if opName.startsWith "vec_pack" then
        -- vec_pack_0<T>() or vec_pack_N<T>(e1,...,eN)
        let mut allBindings : List (Site × Expr) := []
        let mut argSites : List Site := []
        for arg in args do
          let ar ← flattenExpr arg
          allBindings := allBindings ++ ar.bindings
          argSites := argSites ++ [ar.result]
        let s ← freshSite
        pure { bindings := allBindings ++ [(s, .vecPack elemTy argSites)], result := s }
      else
        -- Fallback for unrecognized vec ops
        let s ← freshSite
        pure { bindings := [(s, .intLit 0)], result := s }
  | .packVariant enumName variantName fields =>
    -- Flatten each field value, then packVariant with full enum type
    let mut allBindings : List (Site × Expr) := []
    let mut fieldSites : List (Field × Site) := []
    for (fname, fexpr) in fields do
      let fr ← flattenExpr fexpr
      allBindings := allBindings ++ fr.bindings
      fieldSites := fieldSites ++ [(⟨fname⟩, fr.result)]
    let s ← freshSite
    -- Qualify enum name with module name
    let moduleName := (← get).moduleName
    let qualifiedEnumName := moduleName ++ "." ++ enumName
    pure { bindings := allBindings ++ [(s, .packVariant qualifiedEnumName variantName fieldSites)], result := s }

/- ====================================================== -/
/-       Statement Translation                             -/
/- ====================================================== -/

/-- Build a chain of Stmt.assign for multiple variable-site pairs -/
def buildAssigns (vars : List String) (sites : List Site) (cont : Stmt) : Stmt :=
  match vars, sites with
  | [], _ | _, [] => cont
  | [v], [s] => .assign ⟨v⟩ s cont
  | v :: vs, s :: ss => .assign ⟨v⟩ s (buildAssigns vs ss cont)

/-- Translate a list of MVIR statements to a CPS-chained MoveLight Stmt.
    `nextBlockLabel` is used for `jump_if` fallthrough.
    Expressions for the current statement are flattened BEFORE the continuation
    is translated, ensuring sites are numbered in order of appearance. -/
partial def translateStmts (stmts : List MvirStmt) (nextBlockLabel : Option String) :
    TransM Stmt := do
  match stmts with
  | [] => pure .skip
  | [stmt] => translateStmt stmt nextBlockLabel (pure .skip)
  | stmt :: rest =>
    -- Pass lazy continuation: current stmt's expressions are flattened first
    translateStmt stmt nextBlockLabel (translateStmts rest nextBlockLabel)
where
  /-- Translate a single MVIR statement. For non-terminal statements, `contM` is a lazy
      computation producing the continuation (evaluated AFTER flattening current expressions).
      For terminal statements, `contM` is not evaluated. -/
  translateStmt (stmt : MvirStmt) (nextBlockLabel : Option String) (contM : TransM Stmt) :
      TransM Stmt := do
    match stmt with
    | .jump label => pure (.jump label)
    | .jumpIf cond label =>
      let condR ← flattenExpr cond
      let fallthroughLabel := nextBlockLabel.getD "error_no_fallthrough"
      pure (wrapBindings condR.bindings (.branch condR.result label fallthroughLabel))
    | .jumpIfFalse cond label =>
      -- jump_if_false: jump to label when condition is FALSE (swap branches)
      let condR ← flattenExpr cond
      let fallthroughLabel := nextBlockLabel.getD "error_no_fallthrough"
      pure (wrapBindings condR.bindings (.branch condR.result fallthroughLabel label))
    | .ret exprs =>
      if exprs.isEmpty then
        pure (.ret [])
      else
        let mut allBindings : List (Site × Expr) := []
        let mut resultSites : List Site := []
        for e in exprs do
          let r ← flattenExpr e
          allBindings := allBindings ++ r.bindings
          resultSites := resultSites ++ [r.result]
        pure (wrapBindings allBindings (.ret resultSites))
    | .abort e =>
      let r ← flattenExpr e
      pure (wrapBindings r.bindings (.abort r.result))
    | .assign vars expr =>
      match expr with
      | .call funcName args =>
        -- Function call: x = Self.f(args) or x, y = Self.f(args)
        let mut allBindings : List (Site × Expr) := []
        let mut argSites : List Site := []
        for arg in args do
          let ar ← flattenExpr arg
          allBindings := allBindings ++ ar.bindings
          argSites := argSites ++ [ar.result]
        -- Create result sites for multi-return
        let mut resultSites : List Site := []
        for _ in vars do
          let s ← freshSite
          resultSites := resultSites ++ [s]
        -- Evaluate continuation AFTER flattening current expressions
        let contOrSkip ← contM
        -- Build the call statement, then assign each result to a variable
        let assigns := buildAssigns vars resultSites contOrSkip
        -- Qualify function name with module name
        let qualName := s!"{(← get).moduleName}.{funcName}"
        let callStmt := Stmt.call resultSites qualName argSites assigns
        pure (wrapBindings allBindings callStmt)
      | .vecOp opName ty args =>
        let structs := (← get).structs
        let enums := (← get).enums
        let elemTy := resolveBasicType structs enums ty
        match opName with
        | "vec_push_back" =>
          -- vec_push_back<T>(ref, val) → Stmt.vecPushBack ref val cont
          match args with
          | [refArg, valArg] =>
            let refR ← flattenExpr refArg
            let valR ← flattenExpr valArg
            let contOrSkip ← contM
            pure (wrapBindings (refR.bindings ++ valR.bindings)
              (.vecPushBack refR.result valR.result contOrSkip))
          | _ =>
            let contOrSkip ← contM
            pure contOrSkip
        | "vec_swap" =>
          -- vec_swap<T>(ref, idx1, idx2) → Stmt.vecSwap ref idx1 idx2 cont
          match args with
          | [refArg, idx1Arg, idx2Arg] =>
            let refR ← flattenExpr refArg
            let idx1R ← flattenExpr idx1Arg
            let idx2R ← flattenExpr idx2Arg
            let contOrSkip ← contM
            pure (wrapBindings (refR.bindings ++ idx1R.bindings ++ idx2R.bindings)
              (.vecSwap refR.result idx1R.result idx2R.result contOrSkip))
          | _ =>
            let contOrSkip ← contM
            pure contOrSkip
        | _ =>
          if opName.startsWith "vec_unpack" then
            -- vec_unpack_N<T>(src) → Stmt.vecUnpack T resultSites src cont
            match args with
            | [srcArg] =>
              let srcR ← flattenExpr srcArg
              let mut resultSites : List Site := []
              for _ in vars do
                let s ← freshSite
                resultSites := resultSites ++ [s]
              let contOrSkip ← contM
              let assigns := buildAssigns vars resultSites contOrSkip
              pure (wrapBindings srcR.bindings
                (.vecUnpack elemTy resultSites srcR.result assigns))
            | _ =>
              let contOrSkip ← contM
              pure contOrSkip
          else
            -- Other vec ops in statement position: flatten as expression
            let r ← flattenExpr expr
            if vars == ["_"] then
              let contOrSkip ← contM
              pure (wrapBindings r.bindings contOrSkip)
            else
              match vars with
              | [var] =>
                let contOrSkip ← contM
                let assignStmt := Stmt.assign ⟨var⟩ r.result contOrSkip
                pure (wrapBindings r.bindings assignStmt)
              | _ => pure .skip
      | _ =>
        -- Regular assignment: x = expr
        let r ← flattenExpr expr
        if vars == ["_"] then
          -- Discard: evaluate the expression and release the result site
          let contOrSkip ← contM
          let releaseStmt := Stmt.release r.result contOrSkip
          pure (wrapBindings r.bindings releaseStmt)
        else
          match vars with
          | [var] =>
            let contOrSkip ← contM
            let assignStmt := Stmt.assign ⟨var⟩ r.result contOrSkip
            pure (wrapBindings r.bindings assignStmt)
          | _ => pure .skip -- multi-assign without call: shouldn't happen
    | .writeRef target value =>
      let targetR ← flattenExpr target
      let valueR ← flattenExpr value
      let contOrSkip ← contM
      let writeStmt := Stmt.writeRef targetR.result valueR.result contOrSkip
      pure (wrapBindings (targetR.bindings ++ valueR.bindings) writeStmt)
    | .unpack _structName fields source =>
      let sourceR ← flattenExpr source
      -- Create sites for each unpacked field
      let mut fieldSites : List (Field × Site) := []
      for (fname, _varName) in fields do
        let s ← freshSite
        fieldSites := fieldSites ++ [(⟨fname⟩, s)]
      -- Evaluate continuation AFTER flattening current expressions
      let contOrSkip ← contM
      -- Build assigns for each unpacked variable
      let varNames := fields.map Prod.snd
      let sites := fieldSites.map Prod.snd
      let assigns := buildAssigns varNames sites contOrSkip
      let unpackStmt := Stmt.unpack fieldSites sourceR.result assigns
      pure (wrapBindings sourceR.bindings unpackStmt)
    | .unpackVariant _isMut _enumName variantName fields source =>
      let sourceR ← flattenExpr source
      -- Create sites for each unpacked field
      let mut fieldSites : List (Field × Site) := []
      for (fname, _varName) in fields do
        let s ← freshSite
        fieldSites := fieldSites ++ [(⟨fname⟩, s)]
      -- Evaluate continuation AFTER flattening current expressions
      let contOrSkip ← contM
      -- Build assigns for each unpacked variable
      let varNames := fields.map Prod.snd
      let sites := fieldSites.map Prod.snd
      let assigns := buildAssigns varNames sites contOrSkip
      let unpackStmt := Stmt.unpackVariant variantName fieldSites sourceR.result assigns
      pure (wrapBindings sourceR.bindings unpackStmt)
    | .variantSwitch _enumName source cases =>
      let sourceR ← flattenExpr source
      let casePairs := cases.map fun (vname, label) => (vname, label)
      pure (wrapBindings sourceR.bindings (.variantSwitch sourceR.result casePairs))

/- ====================================================== -/
/-       Function Translation                              -/
/- ====================================================== -/

/-- Translate a single block -/
def translateBlock (block : MvirBlock) (nextBlockLabel : Option String) :
    TransM Block := do
  let body ← translateStmts block.stmts nextBlockLabel
  pure { label := block.label, body }

/-- Translate all blocks in a function, passing next-block labels for fallthrough -/
def translateBlocks (blocks : List MvirBlock) : TransM (List Block) := do
  let mut result : List Block := []
  for i in List.range blocks.length do
    let block := blocks[i]!
    let nextLabel := if i + 1 < blocks.length then some blocks[i + 1]!.label else none
    let translated ← translateBlock block nextLabel
    result := result ++ [translated]
  pure result

/-- Translate a MVIR function definition to a MoveLight FunDef -/
def translateFunDef (mfun : MvirFunDef) : TransM FunDef := do
  let structs := (← get).structs
  let enums := (← get).enums
  -- Reset site counter for each function
  modify fun s => { s with nextSiteId := 0, nextRefId := 1 }
  -- Translate parameters: each gets .paramRef aref
  let params := mfun.params.map fun p =>
    (⟨p.name⟩, resolveType structs enums (.paramRef ⟨p.name⟩) p.type)
  -- Translate return types
  let returnType := mfun.returnTypes.map (resolveParamType structs enums)
  -- Translate locals: ref types get sequential .refid
  let mut locals : List LocalVar := []
  for loc in mfun.locals do
    let aref ← match loc.type with
      | .ref _ _ => freshRefId
      | _ => pure (.refid 0) -- won't be used for basic types
    let ty := resolveType structs enums aref loc.type
    locals := locals ++ [{ name := ⟨loc.name⟩, type := ty }]
  -- Translate blocks
  let blocks ← translateBlocks mfun.blocks
  pure { params, returnType, locals, blocks }

/- ====================================================== -/
/-       Module Translation                                -/
/- ====================================================== -/

/-- Translate a MVIR module to a list of (function_name, FunDef) pairs -/
def translateModule (mod : MvirModule) : TransM (List (String × FunDef)) := do
  -- Resolve struct definitions first, then enums (enums may reference structs)
  let resolvedStructs := resolveStructDefs mod.name mod.structs
  let resolvedEnums := resolveEnumDefs mod.name resolvedStructs mod.enums
  modify fun s => { s with structs := resolvedStructs, enums := resolvedEnums, moduleName := mod.name }
  -- Translate each function
  let mut result : List (String × FunDef) := []
  for mfun in mod.functions do
    let fd ← translateFunDef mfun
    result := result ++ [(mfun.name, fd)]
  pure result

/-- Translate a complete MVIR file to a list of (module_name, function_name, FunDef) triples -/
def translateFile (file : MvirFile) :
    List (String × String × FunDef) :=
  let action : TransM (List (String × String × FunDef)) := do
    let mut allFuns : List (String × String × FunDef) := []
    for mod in file.modules do
      let funs ← translateModule mod
      for (fname, fd) in funs do
        allFuns := allFuns ++ [(mod.name, fname, fd)]
    pure allFuns
  (action.run default).1

end LeanMove.Lang.MoveIR.Translate
