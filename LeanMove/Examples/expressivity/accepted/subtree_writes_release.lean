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

import Ssreflect.Lang

import LeanMove.Lang.MoveLight
import LeanMove.Checker.TypeChecking
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
open LeanMove.Checker
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
    (var_root, .ref (.trecord tree_entries) (.varRef var_root) .siteBorrowMut)
  ]
  returnType := .basic .tunit
  locals := [
    { name := var_x, type := .ref (.trecord sub1_entries) (.varRef var_root) .siteBorrowMut },
    { name := var_y, type := .ref .u64 (.varRef var_root) .siteBorrowMut }
  ]
  blocks := [
    -- l0: branch on condition
    { label := "l0"
      body :=
        (letsite s0 ← move var_cond) ;;  -- s0 = move(cond)
        Stmt.branch s0 "l2" "l1"         -- if s0 then l2 else l1
    },
    -- l1 (false branch): x = &mut root.l; y = &mut x.l.l
    { label := "l1"
      body :=
        -- x = &mut copy(root).Tree::l
        (letsite s1 ← copy var_root) ;;
        Stmt.letBind s2 (Expr.borrowMutField s1 (.trecord tree_entries) field_l) ;;
        (var_x ::= s2) ;;
        -- y = &mut (&mut copy(x).Sub1::l).Sub2::l
        (letsite s3 ← copy var_x) ;;
        Stmt.letBind s4 (Expr.borrowMutField s3 (.trecord sub1_entries) field_l) ;;  -- Sub2
        Stmt.letBind s5 (Expr.borrowMutField s4 (.trecord sub2_entries) field_l) ;;  -- u64
        (var_y ::= s5) ;;
        Stmt.jump "l3"
    },
    -- l2 (true branch): x = &mut root.r; y = &mut x.r.r
    { label := "l2"
      body :=
        -- x = &mut copy(root).Tree::r
        (letsite s1 ← copy var_root) ;;
        Stmt.letBind s2 (Expr.borrowMutField s1 (.trecord tree_entries) field_r) ;;
        (var_x ::= s2) ;;
        -- y = &mut (&mut copy(x).Sub1::r).Sub2::r
        (letsite s3 ← copy var_x) ;;
        Stmt.letBind s4 (Expr.borrowMutField s3 (.trecord sub1_entries) field_r) ;;  -- Sub2
        Stmt.letBind s5 (Expr.borrowMutField s4 (.trecord sub2_entries) field_r) ;;  -- u64
        (var_y ::= s5) ;;
        Stmt.jump "l3"
    },
    -- l3: release x, write to root.l.r, write through y
    { label := "l3"
      body :=
        -- _ = move(x) -- release x
        (letsite s6 ← move var_x) ;;
        -- *(&mut (&mut copy(root).Tree::l).Sub1::r) = Sub2 { l: 0, r: 0 }
        -- This is safe because root.l.r is not borrowed
        (letsite s7 ← copy var_root) ;;
        Stmt.letBind s8 (Expr.borrowMutField s7 (.trecord tree_entries) field_l) ;;  -- &mut Sub1
        Stmt.letBind s9 (Expr.borrowMutField s8 (.trecord sub1_entries) field_r) ;;  -- &mut Sub2
        -- Pack Sub2 { l: 0, r: 0 }
        (letsite s13 ← #0) ;;            -- s13 = 0 (integer literal for l)
        (letsite s14 ← #0) ;;            -- s14 = 0 (integer literal for r)
        Stmt.letBind s15 (Expr.pack "Sub2" [(field_l, s13), (field_r, s14)]) ;;
        Stmt.writeRef s9 s15 ;;          -- *s9 = Sub2 { l: 0, r: 0 }
        -- *move(y) = 0
        (letsite s10 ← move var_y) ;;
        (letsite s16 ← #0) ;;            -- s16 = 0 (integer literal)
        Stmt.writeRef s10 s16 ;;
        Stmt.ret []
    }
  ]
}

-- Theorem: t is well-typed
theorem t_welltyped : ∃ lenv, typecheck_fun t lenv := by
  sorry

end LeanMove.Examples.Expressivity.SubtreeWritesRelease
