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

/-! ## Pretty-Printer for MoveLight AST

Converts MoveLight `FunDef` values into readable Lean code that uses
the macro syntax from `Macros.lean`. This is useful for inspecting
the output of MVIR → MoveLight translation.

The output uses the macro notation:
- `(letsite s ← copy x) ;; ...` for let-bindings
- `(x ::= s) ;; ...` for assignments
- `(*s1 ::= s2) ;; ...` for write-ref
- `ret [s1, s2]` for returns
- etc.
-/

namespace LeanMove.Lang.MoveIR.PrettyPrint

open LeanMove.Lang
open LeanMove.Lang.MoveLight

/- ====================================================== -/
/-       Atomic Pretty-Printers                           -/
/- ====================================================== -/

def ppSite : Site → String
  | .site n => s!"(.site {n})"
  | .root => ".root"

def ppVar : Var → String
  | ⟨id⟩ => s!"⟨\"{id}\"⟩"

def ppField : Field → String
  | ⟨id⟩ => s!"⟨\"{id}\"⟩"

def ppAref : Aref → String
  | .root => ".root"
  | .refid n => s!"(.refid {n})"
  | .paramRef v => s!"(.paramRef {ppVar v})"

def ppBorrowingKind : BorrowingKind → String
  | .siteBorrowImm => ".siteBorrowImm"
  | .siteBorrowMut => ".siteBorrowMut"

/- ====================================================== -/
/-       Type Pretty-Printers                             -/
/- ====================================================== -/

mutual
  partial def ppBasicMoveType : BasicMoveType → String
    | .u64 => ".u64"
    | .tbool => ".tbool"
    | .tunit => ".tunit"
    | .trecord m => s!".trecord {ppAssocMap m}"
    | .tvec t => s!"(.tvec {ppBasicMoveType t})"

  partial def ppAssocMap (m : AssocMap Field BasicMoveType) : String :=
    ppAssocMapEntries m.entries

  partial def ppAssocMapEntries : List (Field × BasicMoveType) → String
    | [] => "AssocMap.empty"
    | [(f, bt)] => s!"(AssocMap.insert AssocMap.empty {ppField f} {ppBasicMoveType bt})"
    | entries =>
      -- Build nested inserts: insert (insert empty f1 t1) f2 t2
      entries.foldl (fun acc (f, bt) =>
        s!"(AssocMap.insert {acc} {ppField f} {ppBasicMoveType bt})"
      ) "AssocMap.empty"
end

def ppMoveType : MoveType → String
  | .basic bt => s!".basic {ppBasicMoveType bt}"
  | .ref bt ar bk => s!".ref {ppBasicMoveType bt} {ppAref ar} {ppBorrowingKind bk}"

def ppParamType : ParamType → String
  | ⟨bt, none⟩ => s!"⟨{ppBasicMoveType bt}, none⟩"
  | ⟨bt, some true⟩ => s!"⟨{ppBasicMoveType bt}, some true⟩"
  | ⟨bt, some false⟩ => s!"⟨{ppBasicMoveType bt}, some false⟩"

/- ====================================================== -/
/-       Expression & Statement Pretty-Printers           -/
/- ====================================================== -/

def ppBinop : Binop → String
  | .add => ".add"
  | .sub => ".sub"
  | .mul => ".mul"
  | .div => ".div"
  | .mod => ".mod"
  | .eq => ".eq"
  | .lt => ".lt"
  | .nand => ".nand"

def ppFieldSitePairs : List (Field × Site) → String
  | [] => "[]"
  | pairs =>
    let items := pairs.map fun (f, s) => s!"({ppField f}, {ppSite s})"
    s!"[{", ".intercalate items}]"

def ppSiteList : List Site → String
  | [] => "[]"
  | sites =>
    let items := sites.map ppSite
    s!"[{", ".intercalate items}]"

def ppUsage : Usage → String
  | .copy v => s!"copy {ppVar v}"
  | .move v => s!"move {ppVar v}"
  | .borrowImm v => s!"&{ppVar v}"
  | .borrowMut v => s!"&mut {ppVar v}"

def ppExpr : Expr → String
  | .usage u => ppUsage u
  | .intLit n => s!"#{n}"
  | .borrowField s bt f =>
    s!"borrowField({ppSite s}, {ppBasicMoveType bt}, {ppField f})"
  | .borrowMutField s bt f =>
    s!"borrowMutField({ppSite s}, {ppBasicMoveType bt}, {ppField f})"
  | .binop op a b => s!"Expr.binop {ppBinop op} {ppSite a} {ppSite b}"
  | .readRef s => s!"*{ppSite s}"
  | .pack id fields => s!"pack(\"{id}\", {ppFieldSitePairs fields})"
  | .freeze s => s!"freeze {ppSite s}"
  | .vecPack t elems => s!"vecPack({ppBasicMoveType t}, {ppSiteList elems})"
  | .vecLen s => s!"vecLen({ppSite s})"
  | .vecImmBorrow s idx => s!"vecImmBorrow({ppSite s}, {ppSite idx})"
  | .vecMutBorrow s idx => s!"vecMutBorrow({ppSite s}, {ppSite idx})"
  | .vecPopBack s => s!"vecPopBack({ppSite s})"

/-- Pretty-print a statement using macro syntax.
    Returns a list of lines (each indented appropriately). -/
partial def ppStmt (indent : String) : Stmt → String
  -- Terminal statements
  | .skip => s!"{indent}Stmt.skip"
  | .jump l => s!"{indent}jump \"{l}\""
  | .branch s l1 l2 => s!"{indent}branch {ppSite s} \"{l1}\" \"{l2}\""
  | .ret sites => s!"{indent}ret {ppSiteList sites}"
  | .abort s => s!"{indent}abort {ppSite s}"
  -- Non-terminal: letBind
  | .letBind s e cont =>
    s!"{indent}(letsite {ppSite s} ← {ppExpr e}) ;;\n{ppStmt indent cont}"
  -- Non-terminal: call
  | .call results fname args cont =>
    s!"{indent}(call({ppSiteList results}, \"{fname}\", {ppSiteList args})) ;;\n{ppStmt indent cont}"
  -- Non-terminal: assign
  | .assign v s cont =>
    s!"{indent}({ppVar v} ::= {ppSite s}) ;;\n{ppStmt indent cont}"
  -- Non-terminal: writeRef
  | .writeRef a b cont =>
    s!"{indent}(*{ppSite a} ::= {ppSite b}) ;;\n{ppStmt indent cont}"
  -- Non-terminal: release
  | .release s cont =>
    s!"{indent}(release {ppSite s}) ;;\n{ppStmt indent cont}"
  -- Non-terminal: unpack
  | .unpack fields src cont =>
    s!"{indent}(unpack({ppFieldSitePairs fields}, {ppSite src})) ;;\n{ppStmt indent cont}"
  -- Non-terminal: vecUnpack
  | .vecUnpack t results src cont =>
    s!"{indent}(vecUnpack({ppBasicMoveType t}, {ppSiteList results}, {ppSite src})) ;;\n{ppStmt indent cont}"
  -- Non-terminal: vecPushBack
  | .vecPushBack ref val cont =>
    s!"{indent}(vecPushBack({ppSite ref}, {ppSite val})) ;;\n{ppStmt indent cont}"
  -- Non-terminal: vecSwap
  | .vecSwap ref idx1 idx2 cont =>
    s!"{indent}(vecSwap({ppSite ref}, {ppSite idx1}, {ppSite idx2})) ;;\n{ppStmt indent cont}"

/- ====================================================== -/
/-       FunDef Pretty-Printer                            -/
/- ====================================================== -/

def ppLocalVar : LocalVar → String
  | ⟨v, t⟩ => s!"    \{ name := {ppVar v}, type := {ppMoveType t} }"

def ppParam : Var × MoveType → String
  | (v, t) => s!"({ppVar v}, {ppMoveType t})"

def ppBlock (b : Block) : String :=
  let bodyStr := ppStmt "        " b.body
  s!"    \{ label := \"{b.label}\"\n      body :=\n{bodyStr}\n    }"

/-- Pretty-print a FunDef with a given name -/
def ppFunDef (name : String) (fd : FunDef) : String :=
  let paramsStr := ", ".intercalate (fd.params.map ppParam)
  let retStr := ", ".intercalate (fd.returnType.map ppParamType)
  let localsStr := if fd.locals.isEmpty then "[]"
    else "[\n" ++ ",\n".intercalate (fd.locals.map ppLocalVar) ++ "\n  ]"
  let blocksStr := ",\n".intercalate (fd.blocks.map ppBlock)
  s!"def {name} : FunDef := \{\n  params := [{paramsStr}]\n  returnType := [{retStr}]\n  locals := {localsStr}\n  blocks := [\n{blocksStr}\n  ]\n}"

/-- Pretty-print a list of (module_name, function_name, FunDef) triples.
    This is the format returned by `translateFile`. -/
def ppTranslateResults (results : List (String × String × FunDef)) : String :=
  let sections := results.map fun (modName, funName, fd) =>
    s!"-- Module: {modName}\n{ppFunDef funName fd}"
  "\n\n".intercalate sections

end LeanMove.Lang.MoveIR.PrettyPrint
