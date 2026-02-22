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
import LeanMove.Typing.Algorithmic.DecidableTypeEnv
import LeanMove.Lang.Macros

/-!
# Subtree Writes Release

Source: https://github.com/tnowacki/sui/blob/example-tests/external-crates/move/crates/bytecode-verifier-transactional-tests/tests/reference_safety/expressivity/subtree_writes_release.mvir

This module demonstrates that "release is lossy in the graph" - writes to
references are safe even when there's complex aliasing, as long as references
are properly released.

Nested struct hierarchy:
- Tree { l: Sub1, r: Sub1 }
- Sub1 { l: Sub2, r: Sub2 }
- Sub2 { l: u64, r: u64 }

Original MVIR:
```
t(cond: bool, root: &mut Self.Tree) {
    let x: &mut Self.Sub1;
    let y: &mut u64;
label l0:
    jump_if (move(cond)) l2;
label l1:
    x = &mut copy(root).Tree::l;
    y = &mut (&mut copy(x).Sub1::l).Sub2::l;
    jump l3;
label l2:
    x = &mut copy(root).Tree::r;
    y = &mut (&mut copy(x).Sub1::r).Sub2::r;
    jump l3;
label l3:
    _ = move(x);
    // should be safe root.l.r is not borrowed
    *(&mut (&mut copy(root).Tree::l).Sub1::r) = Sub2 { l: 0, r: 0 };
    *move(y) = 0;
    return;
}
```
-/

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Typing
open AssocMap
open Regex

namespace LeanMove.Examples.Expressivity.SubtreeWritesRelease

-- Fields for nested structs
def field_l : Field := ⟨"l"⟩
def field_r : Field := ⟨"r"⟩

-- Sub2 { l: u64, r: u64 }
def sub2_entries : AssocMap Field BasicMoveType :=
  insert (insert empty field_l .u64) field_r .u64

-- Sub1 { l: Sub2, r: Sub2 }
def sub1_entries : AssocMap Field BasicMoveType :=
  insert (insert empty field_l (.trecord sub2_entries)) field_r (.trecord sub2_entries)

-- Tree { l: Sub1, r: Sub1 }
def tree_entries : AssocMap Field BasicMoveType :=
  insert (insert empty field_l (.trecord sub1_entries)) field_r (.trecord sub1_entries)

-- Abstract reference for the parameter
def root_var : Aref := .varRef ⟨"root"⟩

-- Variables
def var_cond : Var := ⟨"cond"⟩
def var_root : Var := ⟨"root"⟩
def var_x : Var := ⟨"x"⟩
def var_y : Var := ⟨"y"⟩

-- Sites
def s0 : Site := .site 0
def s1 : Site := .site 1
def s2 : Site := .site 2
def s3 : Site := .site 3
def s4 : Site := .site 4
def s5 : Site := .site 5
def s6 : Site := .site 6
def s7 : Site := .site 7
def s8 : Site := .site 8
def s9 : Site := .site 9
def s10 : Site := .site 10
def s11 : Site := .site 11
def s12 : Site := .site 12
def s13 : Site := .site 13 -- integer literal 0 for Sub2.l
def s14 : Site := .site 14 -- integer literal 0 for Sub2.r
def s15 : Site := .site 15 -- packed Sub2 struct
def s16 : Site := .site 16 -- integer literal 0 for *move(y)

/-
  t(cond: bool, root: &mut Self.Tree)
  Navigates the tree based on condition, performs writes.

  The function:
  1. Branches based on cond to select left or right Sub1
  2. In each branch, navigates deep to a u64 field
  3. After join, releases x and writes to root.l.r and y

  The writes are safe because "release is lossy in the graph" - when we
  move(x) the reference is released, removing it from the path graph.
-/
def t : FunDef := {
  params := [
    (var_cond, .basic .tbool),
    (var_root, .ref (.trecord tree_entries) root_var .siteBorrowMut)
  ]
  returnType := []
  locals := [
    -- Algorithmic checker assigns .refid 1 for borrowMutField of copy(root) (first borrow in body)
    { name := var_x, type := .ref (.trecord sub1_entries) (.refid 1) .siteBorrowMut },
    -- Algorithmic checker assigns .refid 3 for second borrowMutField chain (Sub2.field → u64)
    { name := var_y, type := .ref .u64 (.refid 3) .siteBorrowMut }
  ]
  blocks := [
    -- l0: branch on condition
    { label := "l0"
      body :=
        (letsite s0 ← move var_cond) ;;  -- s0 = move(cond)
        branch s0 "l2" "l1"              -- if s0 then l2 else l1
    },
    -- l1 (false branch): x = &mut root.l; y = &mut x.l.l
    { label := "l1"
      body :=
        -- x = &mut copy(root).Tree::l
        (letsite s1 ← copy var_root) ;;
        (letsite s2 ← borrowMutField(s1, .trecord tree_entries, field_l)) ;;
        (var_x ::= s2) ;;
        -- y = &mut (&mut copy(x).Sub1::l).Sub2::l
        (letsite s3 ← copy var_x) ;;
        (letsite s4 ← borrowMutField(s3, .trecord sub1_entries, field_l)) ;;  -- Sub2
        (letsite s5 ← borrowMutField(s4, .trecord sub2_entries, field_l)) ;;  -- u64
        (var_y ::= s5) ;;
        jump "l3"
    },
    -- l2 (true branch): x = &mut root.r; y = &mut x.r.r
    { label := "l2"
      body :=
        -- x = &mut copy(root).Tree::r
        (letsite s1 ← copy var_root) ;;
        (letsite s2 ← borrowMutField(s1, .trecord tree_entries, field_r)) ;;
        (var_x ::= s2) ;;
        -- y = &mut (&mut copy(x).Sub1::r).Sub2::r
        (letsite s3 ← copy var_x) ;;
        (letsite s4 ← borrowMutField(s3, .trecord sub1_entries, field_r)) ;;  -- Sub2
        (letsite s5 ← borrowMutField(s4, .trecord sub2_entries, field_r)) ;;  -- u64
        (var_y ::= s5) ;;
        jump "l3"
    },
    -- l3: release x, write to root.l.r, write through y
    { label := "l3"
      body :=
        -- _ = move(x) -- release x
        (letsite s6 ← move var_x) ;;
        -- *(&mut (&mut copy(root).Tree::l).Sub1::r) = Sub2 { l: 0, r: 0 }
        -- This is safe because root.l.r is not borrowed
        (letsite s7 ← copy var_root) ;;
        (letsite s8 ← borrowMutField(s7, .trecord tree_entries, field_l)) ;;  -- &mut Sub1
        (letsite s9 ← borrowMutField(s8, .trecord sub1_entries, field_r)) ;;  -- &mut Sub2
        -- Pack Sub2 { l: 0, r: 0 }
        (letsite s13 ← #0) ;;            -- s13 = 0 (integer literal for l)
        (letsite s14 ← #0) ;;            -- s14 = 0 (integer literal for r)
        (letsite s15 ← pack("Sub2", [(field_l, s13), (field_r, s14)])) ;;
        (*s9 ::= s15) ;;                 -- *s9 = Sub2 { l: 0, r: 0 }
        -- *move(y) = 0
        (letsite s10 ← move var_y) ;;
        (letsite s16 ← #0) ;;            -- s16 = 0 (integer literal)
        (*s10 ::= s16) ;;
        ret []
    }
  ]
}

-- -----------------------------------------------------
-- -           Algorithmic Type Checking Tests        --
-- -----------------------------------------------------

-- VarEnv at l1/l2 entry (after l0: cond consumed by move)
def t_branch_varEnv : VarEnv :=
  let ve := init_fun_varEnv t
  update ve var_cond (.invalidVar, .basic .tbool, .mutable)

-- VarEnv at l3 entry (x,y assigned/valid; cond still invalid)
-- Checker assigns refid 5 to x and refid 8 to y in both branches
def t_l3_varEnv : VarEnv :=
  let ve := t_branch_varEnv
  let ve := update ve var_x (.validVar, .ref (.trecord sub1_entries) (.refid 5) .siteBorrowMut, .mutable)
  update ve var_y (.validVar, .ref .u64 (.refid 8) .siteBorrowMut, .mutable)

-- Regex helpers matching the structural forms produced by the checker.
-- Forward paths: extend ε by field chars
private def fl := Regex.concat Regex.ε (Regex.char (PathElement.field field_l))
private def fr := Regex.concat Regex.ε (Regex.char (PathElement.field field_r))
private def fl2 := Regex.concat fl (Regex.char (PathElement.field field_l))
private def fr2 := Regex.concat fr (Regex.char (PathElement.field field_r))
private def fl3 := Regex.concat fl2 (Regex.char (PathElement.field field_l))
private def fr3 := Regex.concat fr2 (Regex.char (PathElement.field field_r))

-- Reverse paths: Brzozowski derivatives of ε
private def dfl := Regex.deriv Regex.ε (PathElement.field field_l)
private def dfr := Regex.deriv Regex.ε (PathElement.field field_r)
private def dfl2 := Regex.deriv dfl (PathElement.field field_l)
private def dfr2 := Regex.deriv dfr (PathElement.field field_r)
private def dfl3 := Regex.deriv dfl2 (PathElement.field field_l)
private def dfr3 := Regex.deriv dfr2 (PathElement.field field_r)

-- Abbreviations for ref pairs
private def r4 : Aref := .refid 4
private def r5 : Aref := .refid 5
private def r6 : Aref := .refid 6
private def r7 : Aref := .refid 7
private def r8 : Aref := .refid 8

-- l3 PathEnvDec: paths computed from both branches (l1 uses field_l, l2 uses field_r).
-- At jump "l3", the checker produces pathEnv.refs = [r8, r7, r6, r5, r4, .root, r0].
-- The l3 paths are unions of the left (field_l) and right (field_r) branch paths.
-- Self-loops (ε) and root paths (empty) are handled automatically by toPathEnv.
def t_l3_pathEnvDec : PathEnvDec :=
  { refs := [r8, r7, r6, r5, r4, .root, root_var]
    paths :=
      (AssocMap.empty
      -- r0 ↔ r4: ε (copy alias, same in both branches)
      |>.insert (root_var, .refid 4) Regex.ε
      |>.insert (.refid 4, root_var) Regex.ε
      -- r0 ↔ r5: union fl fr / union dfl dfr
      |>.insert (root_var, r5) (.union fl fr)
      |>.insert (r5, root_var) (.union dfl dfr)
      -- r0 ↔ r6: union fl fr / union dfl dfr (r6 is alias of r5)
      |>.insert (root_var, r6) (.union fl fr)
      |>.insert (r6, root_var) (.union dfl dfr)
      -- r0 ↔ r7: union fl2 fr2 / union dfl2 dfr2
      |>.insert (root_var, r7) (.union fl2 fr2)
      |>.insert (r7, root_var) (.union dfl2 dfr2)
      -- r0 ↔ r8: union fl3 fr3 / union dfl3 dfr3
      |>.insert (root_var, r8) (.union fl3 fr3)
      |>.insert (r8, root_var) (.union dfl3 dfr3)
      -- r4 ↔ r5: union fl fr / union dfl dfr
      |>.insert (.refid 4, r5) (.union fl fr)
      |>.insert (r5, .refid 4) (.union dfl dfr)
      -- r4 ↔ r6: union fl fr / union dfl dfr
      |>.insert (.refid 4, r6) (.union fl fr)
      |>.insert (r6, .refid 4) (.union dfl dfr)
      -- r5 ↔ r6: ε (alias, same in both branches)
      |>.insert (r5, r6) Regex.ε
      |>.insert (r6, r5) Regex.ε
      -- r5 ↔ r7: union fl fr / union dfl dfr
      |>.insert (r5, r7) (.union fl fr)
      |>.insert (r7, r5) (.union dfl dfr)
      -- r5 ↔ r8: union fl2 fr2 / union dfl2 dfr2
      |>.insert (r5, r8) (.union fl2 fr2)
      |>.insert (r8, r5) (.union dfl2 dfr2)
      -- r6 ↔ r7: union fl fr / union dfl dfr
      |>.insert (r6, r7) (.union fl fr)
      |>.insert (r7, r6) (.union dfl dfr)
      -- r6 ↔ r8: union fl2 fr2 / union dfl2 dfr2
      |>.insert (r6, r8) (.union fl2 fr2)
      |>.insert (r8, r6) (.union dfl2 dfr2)
      -- r7 ↔ r8: union fl fr / union dfl dfr
      |>.insert (r7, r8) (.union fl fr)
      |>.insert (r8, r7) (.union dfl dfr)
      -- r4 ↔ r7: union fl2 fr2 / union dfl2 dfr2
      |>.insert (.refid 4, r7) (.union fl2 fr2)
      |>.insert (r7, .refid 4) (.union dfl2 dfr2)
      -- r4 ↔ r8: union fl3 fr3 / union dfl3 dfr3
      |>.insert (.refid 4, r8) (.union fl3 fr3)
      |>.insert (r8, .refid 4) (.union dfl3 dfr3))
  }

-- Decidable label environment
def t_lenvDec : LabelEnvDec :=
  insert (insert (insert (insert AssocMap.empty
    "l0" { siteEnv := AssocMap.empty, varEnv := init_fun_varEnv t,
           pathEnv := init_fun_pathEnvDec t.params, funEnv := AssocMap.empty })
    "l1" { siteEnv := AssocMap.empty, varEnv := t_branch_varEnv,
           pathEnv := init_fun_pathEnvDec t.params, funEnv := AssocMap.empty })
    "l2" { siteEnv := AssocMap.empty, varEnv := t_branch_varEnv,
           pathEnv := init_fun_pathEnvDec t.params, funEnv := AssocMap.empty })
    "l3" { siteEnv := AssocMap.empty, varEnv := t_l3_varEnv,
           pathEnv := t_l3_pathEnvDec, funEnv := AssocMap.empty }

-- Theorem: t is well-typed (algorithmic, decidable)
set_option maxRecDepth 8192 in
theorem t_check : check_fun_dec t t_lenvDec = true := by rfl

-- Main theorem: t is well-typed (relational)
theorem t_welltyped : ∃ lenv, typecheck_fun t lenv :=
  ⟨_, check_fun_dec_sound _ _ t_check⟩

end LeanMove.Examples.Expressivity.SubtreeWritesRelease
