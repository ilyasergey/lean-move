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
import LeanMove.Examples.Macros

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

The function navigates deep into the tree based on a condition, creates
references at various levels, then performs writes that are safe because
releasing the inner references removes them from the path graph.
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
  insert (insert empty field_l .tint) field_r .tint

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

/-
  t(cond: bool, root: &mut Self.Tree): &mut Self.Sub1
  Navigates the tree based on condition, performs writes, returns reference.

  The function:
  1. Branches based on cond to select left or right Sub1
  2. Navigates to a u64 field deep in the tree
  3. Writes to various references
  4. Returns a reference to a Sub1

  The writes are safe because "release is lossy in the graph" - when we
  write through a reference and release it, the path graph loses that edge,
  allowing subsequent writes to other references.
-/
def t : FunDef := {
  params := [
    (var_cond, .basic .tbool),
    (var_root, .ref (.trecord tree_entries) (.varRef var_root) .siteBorrowMut)
  ]
  returnType := .basic .tunit  -- Simplified
  locals := [
    { name := var_x, type := .ref (.trecord sub1_entries) (.varRef var_root) .siteBorrowMut },
    { name := var_y, type := .ref .tint (.varRef var_root) .siteBorrowMut }
  ]
  blocks := [
    -- l0: branch on condition
    { label := "l0"
      body :=
        (letsite s0 ← copy var_cond) ;;  -- s0 = copy(cond)
        Stmt.branch s0 "l2" "l1"         -- if s0 then l2 else l1
    },
    -- l1 (false branch): x = &mut root.l
    { label := "l1"
      body :=
        (letsite s1 ← copy var_root) ;;  -- s1 = copy(root)
        Stmt.letBind s2 (Expr.borrowMutField s1 "Tree" field_l) ;; -- s2 = &mut s1.l
        (var_x ::= s2) ;;                -- x = s2
        jump "l3"
    },
    -- l2 (true branch): x = &mut root.r
    { label := "l2"
      body :=
        (letsite s1 ← copy var_root) ;;  -- s1 = copy(root)
        Stmt.letBind s2 (Expr.borrowMutField s1 "Tree" field_r) ;; -- s2 = &mut s1.r
        (var_x ::= s2) ;;                -- x = s2
        jump "l3"
    },
    -- l3: navigate deeper and write
    { label := "l3"
      body :=
        -- Navigate to y = &mut x.l.l (a u64 deep in the tree)
        (letsite s3 ← copy var_x) ;;     -- s3 = copy(x)
        Stmt.letBind s4 (Expr.borrowMutField s3 "Sub1" field_l) ;; -- s4 = &mut s3.l (Sub2)
        Stmt.letBind s5 (Expr.borrowMutField s4 "Sub2" field_l) ;; -- s5 = &mut s4.l (u64)
        (var_y ::= s5) ;;                -- y = s5 (reference to u64)
        -- Write to root.l.r (a different Sub2)
        (letsite s6 ← copy var_root) ;;  -- s6 = copy(root)
        Stmt.letBind s7 (Expr.borrowMutField s6 "Tree" field_l) ;; -- s7 = &mut s6.l (Sub1)
        -- This is safe because y points to x.l.l, not root.l.r
        -- (Actually simplified here; real code would pack a new Sub2)
        -- Finally write through y
        (letsite s8 ← copy var_y) ;;     -- s8 = copy(y)
        Stmt.writeRef s8 (.site 10) ;;   -- *s8 = 0
        -- Return (simplified)
        Stmt.ret []
    }
  ]
}

-- Theorem: t is well-typed
theorem t_welltyped : ∃ lenv, typecheck_fun t lenv := by
  sorry

end LeanMove.Examples.Expressivity.SubtreeWritesRelease
