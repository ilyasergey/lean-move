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

import LeanMove.Lang.MoveIR.MoveIR

/-! ## Test Utilities for MVIR Parser

Provides alpha-equivalence checking for comparing parsed MoveLight FunDefs
with hand-written examples. Site numbers, Aref.refid values, and block labels
may differ between parsed and hand-written versions, so we check structural
equality up to consistent renaming.

- **Sites**: bijective mapping per block (each parsed site maps to exactly one hand-written site)
- **Arefs**: bijective mapping (refids matched up to permutation; paramRefs match by name)
- **Labels**: bijective mapping (block labels are internal names that can differ)
- **Variable names**: exact match (these come from the MVIR source)
-/

namespace LeanMove.Tests.Parsing.TestUtils

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Lang.MoveIR
open LeanMove.Lang.MoveIR.Parser
open LeanMove.Lang.MoveIR.Translate

/- ====================================================== -/
/-       Alpha-Equivalence State                           -/
/- ====================================================== -/

/-- Mapping state for site, aref, and label renaming -/
structure AlphaState where
  siteMap : List (Site × Site) := []       -- left → right (bijective)
  siteMapRev : List (Site × Site) := []    -- right → left
  arefMap : List (Aref × Aref) := []       -- left → right (bijective)
  arefMapRev : List (Aref × Aref) := []   -- right → left
  labelMap : List (String × String) := []   -- left → right (bijective)
  labelMapRev : List (String × String) := [] -- right → left
deriving Repr, Inhabited

abbrev AlphaM := StateM AlphaState

/-- Look up a mapping -/
def lookupMapping (map : List (α × β)) (key : α) [BEq α] : Option β :=
  match map.find? (fun (k, _) => k == key) with
  | some (_, v) => some v
  | none => none

/-- Check or establish a site mapping (bijective) -/
def matchSite (l r : Site) : AlphaM Bool := do
  match l, r with
  | .root, .root => pure true
  | .root, _ | _, .root => pure false
  | .site _, .site _ =>
    let s ← get
    match lookupMapping s.siteMap l with
    | some r' => pure (r == r')
    | none =>
      -- Check reverse: r must not already be mapped to a different l
      match lookupMapping s.siteMapRev r with
      | some _ => pure false
      | none =>
        set { s with
          siteMap := (l, r) :: s.siteMap
          siteMapRev := (r, l) :: s.siteMapRev }
        pure true

/-- Check or establish an aref mapping (bijective).
    Refids are matched up to permutation — each left refid maps to exactly one right refid
    and vice versa. VarRefs must match exactly by name. -/
def matchAref (l r : Aref) : AlphaM Bool := do
  match l, r with
  | .root, .root => pure true
  | .paramRef v1, .paramRef v2 => pure (v1 == v2)
  | .refid _, .refid _ =>
    let s ← get
    match lookupMapping s.arefMap l with
    | some r' => pure (r == r')
    | none =>
      -- Check reverse: r must not already be mapped to a different l (bijective)
      match lookupMapping s.arefMapRev r with
      | some _ => pure false
      | none =>
        set { s with
          arefMap := (l, r) :: s.arefMap
          arefMapRev := (r, l) :: s.arefMapRev }
        pure true
  | _, _ => pure false

/-- Check or establish a label mapping (bijective) -/
def matchLabel (l r : String) : AlphaM Bool := do
  let s ← get
  match lookupMapping s.labelMap l with
  | some r' => pure (r == r')
  | none =>
    match lookupMapping s.labelMapRev r with
    | some _ => pure false
    | none =>
      set { s with
        labelMap := (l, r) :: s.labelMap
        labelMapRev := (r, l) :: s.labelMapRev }
      pure true

/- ====================================================== -/
/-       Alpha-Equivalence Checks                         -/
/- ====================================================== -/

mutual

/-- Check alpha-equivalence of BasicMoveType -/
partial def alphaBasicType (l r : BasicMoveType) : AlphaM Bool :=
  match l, r with
  | .u64, .u64 => pure true
  | .u8, .u8 => pure true
  | .tbool, .tbool => pure true
  | .tunit, .tunit => pure true
  | .trecord m1, .trecord m2 => alphaEntries m1.entries m2.entries
  | .tvec t1, .tvec t2 => alphaBasicType t1 t2
  | .tenum n1 vs1, .tenum n2 vs2 => do
    if n1 != n2 then return false
    alphaVariantMap vs1.entries vs2.entries
  | _, _ => pure false

/-- Check alpha-equivalence of variant switch cases (Id × Label pairs) -/
partial def alphaVariantCases (l r : List (Id × String)) : AlphaM Bool :=
  match l, r with
  | [], [] => pure true
  | (v1, lbl1) :: rest1, (v2, lbl2) :: rest2 => do
    if v1 != v2 then return false
    if !(← matchLabel lbl1 lbl2) then return false
    alphaVariantCases rest1 rest2
  | _, _ => pure false

/-- Check alpha-equivalence of variant maps (for tenum) -/
partial def alphaVariantMap (l r : List (Id × AssocMap Field BasicMoveType)) : AlphaM Bool :=
  match l, r with
  | [], [] => pure true
  | (v1, fs1) :: rest1, (v2, fs2) :: rest2 => do
    if v1 != v2 then return false
    if !(← alphaEntries fs1.entries fs2.entries) then return false
    alphaVariantMap rest1 rest2
  | _, _ => pure false

/-- Check alpha-equivalence of field entries -/
partial def alphaEntries (l r : List (Field × BasicMoveType)) : AlphaM Bool :=
  match l, r with
  | [], [] => pure true
  | (f1, t1) :: rest1, (f2, t2) :: rest2 => do
    if f1 != f2 then return false
    if !(← alphaBasicType t1 t2) then return false
    alphaEntries rest1 rest2
  | _, _ => pure false

/-- Check alpha-equivalence of MoveType -/
partial def alphaMoveType (l r : MoveType) : AlphaM Bool :=
  match l, r with
  | .basic bt1, .basic bt2 => alphaBasicType bt1 bt2
  | .ref bt1 a1 bk1, .ref bt2 a2 bk2 => do
    if !(← alphaBasicType bt1 bt2) then return false
    if !(← matchAref a1 a2) then return false
    pure (bk1 == bk2)
  | _, _ => pure false

/-- Check alpha-equivalence of Expr -/
partial def alphaExpr (l r : Expr) : AlphaM Bool :=
  match l, r with
  | .usage u1, .usage u2 =>
    match u1, u2 with
    | .copy v1, .copy v2 | .move v1, .move v2
    | .borrowImm v1, .borrowImm v2 | .borrowMut v1, .borrowMut v2 =>
      pure (v1 == v2)
    | _, _ => pure false
  | .intLit n1, .intLit n2 => pure (n1 == n2)
  | .borrowField s1 bt1 f1, .borrowField s2 bt2 f2 => do
    if !(← matchSite s1 s2) then return false
    if !(← alphaBasicType bt1 bt2) then return false
    pure (f1 == f2)
  | .borrowMutField s1 bt1 f1, .borrowMutField s2 bt2 f2 => do
    if !(← matchSite s1 s2) then return false
    if !(← alphaBasicType bt1 bt2) then return false
    pure (f1 == f2)
  | .binop op1 a1 b1, .binop op2 a2 b2 => do
    if op1 != op2 then return false
    if !(← matchSite a1 a2) then return false
    matchSite b1 b2
  | .readRef s1, .readRef s2 => matchSite s1 s2
  | .pack id1 fs1, .pack id2 fs2 => do
    if id1 != id2 then return false
    alphaFieldSites fs1 fs2
  | .freeze s1, .freeze s2 => matchSite s1 s2
  | .vecPack t1 es1, .vecPack t2 es2 => do
    if !(← alphaBasicType t1 t2) then return false
    alphaSiteList es1 es2
  | .vecLen s1, .vecLen s2 => matchSite s1 s2
  | .vecImmBorrow s1 i1, .vecImmBorrow s2 i2 => do
    if !(← matchSite s1 s2) then return false
    matchSite i1 i2
  | .vecMutBorrow s1 i1, .vecMutBorrow s2 i2 => do
    if !(← matchSite s1 s2) then return false
    matchSite i1 i2
  | .vecPopBack s1, .vecPopBack s2 => matchSite s1 s2
  | .packVariant e1 v1 _ fs1, .packVariant e2 v2 _ fs2 => do
    if e1 != e2 then return false
    if v1 != v2 then return false
    alphaFieldSites fs1 fs2
  | _, _ => pure false

/-- Check alpha-equivalence of field-site pairs -/
partial def alphaFieldSites (l r : List (Field × Site)) : AlphaM Bool :=
  match l, r with
  | [], [] => pure true
  | (f1, s1) :: rest1, (f2, s2) :: rest2 => do
    if f1 != f2 then return false
    if !(← matchSite s1 s2) then return false
    alphaFieldSites rest1 rest2
  | _, _ => pure false

/-- Check alpha-equivalence of site lists -/
partial def alphaSiteList (l r : List Site) : AlphaM Bool :=
  match l, r with
  | [], [] => pure true
  | s1 :: rest1, s2 :: rest2 => do
    if !(← matchSite s1 s2) then return false
    alphaSiteList rest1 rest2
  | _, _ => pure false

/-- Extract the prefix of consecutive letBinds from a Stmt.
    Returns the flat list of (site, expr) bindings and the first non-letBind statement. -/
partial def extractLetBindPrefix : Stmt → (List (Site × Expr) × Stmt)
  | .letBind s e c =>
    let (rest, terminal) := extractLetBindPrefix c
    ((s, e) :: rest, terminal)
  | other => ([], other)

/-- Try to match two binding lists in any order (permutation-tolerant).
    Uses backtracking to find a consistent site+expression mapping.
    For each left binding, tries each unmatched right binding. -/
partial def matchBindingsAnyOrder
    (left right : List (Site × Expr)) : AlphaM Bool := do
  match left with
  | [] => pure right.isEmpty
  | (sl, el) :: restL =>
    matchBindHelper sl el restL right []
where
  matchBindHelper (sl : Site) (el : Expr) (restL : List (Site × Expr))
      (remaining : List (Site × Expr)) (skipped : List (Site × Expr)) :
      AlphaM Bool := do
    match remaining with
    | [] => return false
    | (sr, er) :: rest =>
      let saved ← get
      let exprMatch ← alphaExpr el er
      if exprMatch then
        let siteMatch ← matchSite sl sr
        if siteMatch then
          let rightRest := skipped.reverse ++ rest
          let restMatch ← matchBindingsAnyOrder restL rightRest
          if restMatch then
            return true
      set saved
      matchBindHelper sl el restL rest ((sr, er) :: skipped)

/-- Check alpha-equivalence of Stmt.
    Uses permutation-tolerant matching for letBind sequences: consecutive letBinds
    are collected into a flat list and matched in any order (with backtracking).
    This handles cases where the translator and hand-written examples flatten
    sub-expressions in different orders (e.g., target-first vs value-first for writeRef). -/
partial def alphaStmt (l r : Stmt) : AlphaM Bool := do
  -- Extract leading letBind sequences from both
  let (lBinds, lRest) := extractLetBindPrefix l
  let (rBinds, rRest) := extractLetBindPrefix r
  if !lBinds.isEmpty || !rBinds.isEmpty then
    if lBinds.length != rBinds.length then return false
    if !(← matchBindingsAnyOrder lBinds rBinds) then return false
    alphaStmt lRest rRest
  else
    match lRest, rRest with
    | .skip, .skip => pure true
    | .jump l1, .jump l2 => matchLabel l1 l2
    | .branch s1 l1a l1b, .branch s2 l2a l2b => do
      if !(← matchSite s1 s2) then return false
      if !(← matchLabel l1a l2a) then return false
      matchLabel l1b l2b
    | .ret sites1, .ret sites2 => alphaSiteList sites1 sites2
    | .abort s1, .abort s2 => matchSite s1 s2
    | .unpack fs1 s1 c1, .unpack fs2 s2 c2 => do
      if !(← alphaFieldSites fs1 fs2) then return false
      if !(← matchSite s1 s2) then return false
      alphaStmt c1 c2
    | .call rs1 f1 as1 c1, .call rs2 f2 as2 c2 => do
      if !(← alphaSiteList rs1 rs2) then return false
      if f1 != f2 then return false
      if !(← alphaSiteList as1 as2) then return false
      alphaStmt c1 c2
    | .assign v1 s1 c1, .assign v2 s2 c2 => do
      if v1 != v2 then return false
      if !(← matchSite s1 s2) then return false
      alphaStmt c1 c2
    | .writeRef a1 b1 c1, .writeRef a2 b2 c2 => do
      if !(← matchSite a1 a2) then return false
      if !(← matchSite b1 b2) then return false
      alphaStmt c1 c2
    | .release s1 c1, .release s2 c2 => do
      if !(← matchSite s1 s2) then return false
      alphaStmt c1 c2
    | .vecUnpack t1 rs1 s1 c1, .vecUnpack t2 rs2 s2 c2 => do
      if !(← alphaBasicType t1 t2) then return false
      if !(← alphaSiteList rs1 rs2) then return false
      if !(← matchSite s1 s2) then return false
      alphaStmt c1 c2
    | .vecPushBack r1 v1 c1, .vecPushBack r2 v2 c2 => do
      if !(← matchSite r1 r2) then return false
      if !(← matchSite v1 v2) then return false
      alphaStmt c1 c2
    | .vecSwap r1 i1a i1b c1, .vecSwap r2 i2a i2b c2 => do
      if !(← matchSite r1 r2) then return false
      if !(← matchSite i1a i2a) then return false
      if !(← matchSite i1b i2b) then return false
      alphaStmt c1 c2
    | .unpackVariant v1 fs1 s1 c1, .unpackVariant v2 fs2 s2 c2 => do
      if v1 != v2 then return false
      if !(← alphaFieldSites fs1 fs2) then return false
      if !(← matchSite s1 s2) then return false
      alphaStmt c1 c2
    | .variantSwitch s1 cs1, .variantSwitch s2 cs2 => do
      if !(← matchSite s1 s2) then return false
      alphaVariantCases cs1 cs2
    | _, _ => pure false

end

/-- Check alpha-equivalence of Block (with label bijection) -/
def alphaBlock (l r : Block) : AlphaM Bool := do
  if !(← matchLabel l.label r.label) then return false
  alphaStmt l.body r.body

/-- Check alpha-equivalence of LocalVar -/
def alphaLocalVar (l r : LocalVar) : AlphaM Bool := do
  if l.name != r.name then return false
  alphaMoveType l.type r.type

/-- Check alpha-equivalence of parameter pairs -/
def alphaParam (l r : Var × MoveType) : AlphaM Bool := do
  if l.1 != r.1 then return false
  alphaMoveType l.2 r.2

/-- Check alpha-equivalence of FunDef -/
def alphaFunDef (l r : FunDef) : AlphaM Bool := do
  -- Check params
  if l.params.length != r.params.length then return false
  for i in List.range l.params.length do
    if !(← alphaParam l.params[i]! r.params[i]!) then return false
  -- Check return types (exact match, no renaming needed)
  if l.returnType != r.returnType then return false
  -- Check locals
  if l.locals.length != r.locals.length then return false
  for i in List.range l.locals.length do
    if !(← alphaLocalVar l.locals[i]! r.locals[i]!) then return false
  -- Check blocks (reset site mappings per block since sites are block-local;
  -- hand-written examples may reuse site numbers across parallel branches)
  if l.blocks.length != r.blocks.length then return false
  for i in List.range l.blocks.length do
    modify fun s => { s with siteMap := [], siteMapRev := [] }
    if !(← alphaBlock l.blocks[i]! r.blocks[i]!) then return false
  pure true

/-- Top-level alpha-equivalence check for FunDefs -/
def alphaEquivFunDef (l r : FunDef) : Bool :=
  (alphaFunDef l r |>.run default).1

/- ====================================================== -/
/-       Convenience Functions                             -/
/- ====================================================== -/

/-- Parse MVIR text and translate to MoveLight FunDefs -/
def parseAndTranslate (input : String) : Except String (List (String × String × FunDef)) := do
  let file ← parseMvir input
  pure (translateFile file)

/-- Find a function by name in parsed results -/
def findFun (results : List (String × String × FunDef)) (fname : String) : Option FunDef :=
  match results.find? (fun (_, n, _) => n == fname) with
  | some (_, _, fd) => some fd
  | none => none

/-- Find a function by module and name -/
def findFunInModule (results : List (String × String × FunDef)) (modName fname : String) :
    Option FunDef :=
  match results.find? (fun (m, n, _) => m == modName && n == fname) with
  | some (_, _, fd) => some fd
  | none => none

/-- Find a function by index in parsed results -/
def findFunAt (results : List (String × String × FunDef)) (idx : Nat) : Option FunDef :=
  match results[idx]? with
  | some (_, _, fd) => some fd
  | none => none

end LeanMove.Tests.Parsing.TestUtils
