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

Converts MoveLight AST nodes into strings using the macro notation
from `LeanMove.Lang.Macros`. Output mirrors the hand-written example style,
making it easy to compare parsed/translated results with existing examples.
-/

namespace LeanMove.Lang.MoveLight.PP

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open AssocMap

def ppSite : Site → String
  | .site n => s!"s{n}"
  | .root => ".root"

def ppVar : Var → String
  | ⟨id⟩ => s!"var_{id}"

def ppField : Field → String
  | ⟨id⟩ => s!"field_{id}"

def ppAref : Aref → String
  | .root => ".root"
  | .refid n => s!".refid {n}"
  | .varRef v => s!".varRef {ppVar v}"

def ppBorrowingKind : BorrowingKind → String
  | .siteBorrowImm => ".siteBorrowImm"
  | .siteBorrowMut => ".siteBorrowMut"

mutual
  partial def ppBasicMoveType : BasicMoveType → String
    | .u64 => ".u64"
    | .tbool => ".tbool"
    | .tunit => ".tunit"
    | .trecord m => s!".trecord {ppFieldMap m}"

  partial def ppFieldMap (m : AssocMap Field BasicMoveType) : String :=
    ppFieldEntries m.entries

  partial def ppFieldEntries : List (Field × BasicMoveType) → String
    | [] => "AssocMap.empty"
    | [(f, bt)] => s!"(AssocMap.insert AssocMap.empty {ppField f} {ppBasicMoveType bt})"
    | (f, bt) :: rest => s!"(AssocMap.insert {ppFieldEntries rest} {ppField f} {ppBasicMoveType bt})"
end

def ppMoveType : MoveType → String
  | .basic bt => s!".basic {ppBasicMoveType bt}"
  | .ref bt aref bk => s!".ref {ppBasicMoveType bt} {ppAref aref} {ppBorrowingKind bk}"

def ppParamType : ParamType → String
  | ⟨bt, none⟩ => s!"⟨{ppBasicMoveType bt}, none⟩"
  | ⟨bt, some true⟩ => s!"⟨{ppBasicMoveType bt}, some true⟩"
  | ⟨bt, some false⟩ => s!"⟨{ppBasicMoveType bt}, some false⟩"

def ppBinop : Binop → String
  | .add => "+"
  | .sub => "-"
  | .mul => "*"
  | .div => "/"
  | .mod => "%"
  | .eq => "=="
  | .lt => "<"
  | .nand => "nand"

def ppExprMacro : Expr → String
  | .usage (.copy v) => s!"copy {ppVar v}"
  | .usage (.move v) => s!"move {ppVar v}"
  | .usage (.borrowImm v) => s!"&{ppVar v}"
  | .usage (.borrowMut v) => s!"&mut {ppVar v}"
  | .intLit n => s!"#{n}"
  | .borrowField src bt f =>
    s!"borrowField({ppSite src}, {ppBasicMoveType bt}, {ppField f})"
  | .borrowMutField src bt f =>
    s!"borrowMutField({ppSite src}, {ppBasicMoveType bt}, {ppField f})"
  | .binop op a b => s!"binop {ppBinop op} {ppSite a} {ppSite b}"
  | .readRef s => s!"*{ppSite s}"
  | .pack id fields =>
    let fs := fields.map fun (f, s) => s!"({ppField f}, {ppSite s})"
    "pack(\"" ++ id ++ "\", [" ++ ", ".intercalate fs ++ "])"
  | .freeze s => s!"freeze {ppSite s}"

def ppSiteList (sites : List Site) : String :=
  let ss := sites.map ppSite
  "[" ++ ", ".intercalate ss ++ "]"

private def mkIndent (n : Nat) : String := "".pushn ' ' n

partial def ppStmt (indent : Nat := 8) : Stmt → String
  | .skip => mkIndent indent ++ "Stmt.skip"
  | .jump l => mkIndent indent ++ s!"jump \"{l}\""
  | .branch cond l1 l2 =>
    mkIndent indent ++ s!"branch {ppSite cond} \"{l1}\" \"{l2}\""
  | .ret sites => mkIndent indent ++ s!"ret {ppSiteList sites}"
  | .abort s => mkIndent indent ++ s!"abort {ppSite s}"
  | .letBind s e cont =>
    mkIndent indent ++ s!"(letsite {ppSite s} ← {ppExprMacro e}) ;;\n" ++ ppStmt indent cont
  | .assign v s cont =>
    mkIndent indent ++ s!"({ppVar v} ::= {ppSite s}) ;;\n" ++ ppStmt indent cont
  | .writeRef a b cont =>
    mkIndent indent ++ s!"(*{ppSite a} ::= {ppSite b}) ;;\n" ++ ppStmt indent cont
  | .release s cont =>
    mkIndent indent ++ s!"(release {ppSite s}) ;;\n" ++ ppStmt indent cont
  | .unpack fields src cont =>
    let fs := fields.map fun (f, s) => s!"({ppField f}, {ppSite s})"
    mkIndent indent ++ "(unpack([" ++ ", ".intercalate fs ++ "], " ++ ppSite src ++ ")) ;;\n"
      ++ ppStmt indent cont
  | .call results fname args cont =>
    mkIndent indent ++
      s!"(call({ppSiteList results}, \"{fname}\", {ppSiteList args})) ;;\n"
      ++ ppStmt indent cont

def ppBlock (b : Block) : String :=
  let header := s!"    \{ label := \"{b.label}\"\n      body :=\n"
  let body := ppStmt 8 b.body
  header ++ body ++ "\n    }"

def ppParam (p : Var × MoveType) : String :=
  s!"({ppVar p.1}, {ppMoveType p.2})"

def ppLocal (l : LocalVar) : String :=
  s!"\{ name := {ppVar l.name}, type := {ppMoveType l.type} }"

def ppFunDef (fd : FunDef) : String :=
  let params := fd.params.map ppParam
  let retTypes := fd.returnType.map ppParamType
  let locals := fd.locals.map ppLocal
  let blocks := fd.blocks.map ppBlock
  s!"\{\n" ++
  "  params := [" ++ ", ".intercalate params ++ "]\n" ++
  "  returnType := [" ++ ", ".intercalate retTypes ++ "]\n" ++
  s!"  locals := [\n" ++
  (if locals.isEmpty then "" else
    "    " ++ ",\n    ".intercalate locals ++ "\n") ++
  s!"  ]\n" ++
  s!"  blocks := [\n" ++
  ",\n".intercalate blocks ++ "\n" ++
  s!"  ]\n" ++
  s!"}"

def ppTranslatedFunDefs (results : Except String (List (String × String × FunDef))) : String :=
  match results with
  | .error e => s!"Error: {e}"
  | .ok funs =>
    let entries := funs.map fun (modName, funName, fd) =>
      s!"-- Module: {modName}, Function: {funName}\n" ++
      s!"def {funName} : FunDef := " ++ ppFunDef fd
    "\n\n".intercalate entries

end LeanMove.Lang.MoveLight.PP
