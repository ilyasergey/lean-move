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
# Extension After Call

Source: https://github.com/tnowacki/sui/blob/example-tests/external-crates/move/crates/bytecode-verifier-transactional-tests/tests/reference_safety/expressivity/extension_after_call.mvir

This module demonstrates borrowing and writing to nested struct fields.

Structs:
- Point { x: u64, y: u64 } - a point with copy, drop, store
- Box { tl: Point, br: Point } - a box with top-left and bottom-right points

Functions:
- borrow(b: &mut Box): &mut Point - returns a mutable ref to the top-left point
- write(b: &mut Box): &mut Point - borrows tl, writes zeros to both coords, returns ref
-/

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Checker
open AssocMap
open Regex

namespace LeanMove.Examples.Expressivity.ExtensionAfterCall

-- Fields
def field_x : Field := ⟨"x"⟩
def field_y : Field := ⟨"y"⟩
def field_tl : Field := ⟨"tl"⟩
def field_br : Field := ⟨"br"⟩

-- Point { x: u64, y: u64 }
def point_entries : AssocMap Field BasicMoveType :=
  insert (insert empty field_x .tint) field_y .tint

-- Box { tl: Point, br: Point }
def box_entries : AssocMap Field BasicMoveType :=
  insert (insert empty field_tl (.trecord point_entries)) field_br (.trecord point_entries)

-- Variables
def var_b : Var := ⟨"b"⟩
def var_tl : Var := ⟨"tl"⟩
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
  borrow(b: &mut Self.Box): &mut Self.Point
  Returns a mutable reference to the top-left point.

  label l0:
      tl = &mut copy(b).Box::tl;
      return copy(tl);
-/
def fn_borrow : FunDef := {
  params := [(var_b, .ref (.trecord box_entries) (.varRef var_b) .siteBorrowMut)]
  returnType := .basic .tunit  -- Simplified
  locals := [
    { name := var_tl, type := .ref (.trecord point_entries) (.varRef var_b) .siteBorrowMut }
  ]
  blocks := [
    { label := "l0"
      body :=
        (letsite s0 ← copy var_b) ;;     -- s0 = copy(b)
        Stmt.letBind s1 (Expr.borrowMutField s0 "Box" field_tl) ;; -- s1 = &mut s0.tl
        (var_tl ::= s1) ;;               -- tl = s1
        (letsite s2 ← copy var_tl)       -- s2 = copy(tl)
      terminator := ret [s2]             -- return s2
    }
  ]
}

/-
  write(b: &mut Self.Box): &mut Self.Point
  Borrows the top-left point, writes zeros to both coordinates.

  label l0:
      tl = &mut copy(b).Box::tl;
      x = &mut copy(tl).Point::x;
      y = &mut copy(tl).Point::y;
      *copy(x) = 0;
      *copy(y) = 0;
      return copy(tl);
-/
def fn_write : FunDef := {
  params := [(var_b, .ref (.trecord box_entries) (.varRef var_b) .siteBorrowMut)]
  returnType := .basic .tunit  -- Simplified
  locals := [
    { name := var_tl, type := .ref (.trecord point_entries) (.varRef var_b) .siteBorrowMut },
    { name := var_x, type := .ref .tint (.varRef var_b) .siteBorrowMut },
    { name := var_y, type := .ref .tint (.varRef var_b) .siteBorrowMut }
  ]
  blocks := [
    { label := "l0"
      body :=
        (letsite s0 ← copy var_b) ;;     -- s0 = copy(b)
        Stmt.letBind s1 (Expr.borrowMutField s0 "Box" field_tl) ;; -- s1 = &mut s0.tl
        (var_tl ::= s1) ;;               -- tl = s1
        (letsite s2 ← copy var_tl) ;;    -- s2 = copy(tl)
        Stmt.letBind s3 (Expr.borrowMutField s2 "Point" field_x) ;; -- s3 = &mut s2.x
        (var_x ::= s3) ;;                -- x = s3
        (letsite s4 ← copy var_tl) ;;    -- s4 = copy(tl)
        Stmt.letBind s5 (Expr.borrowMutField s4 "Point" field_y) ;; -- s5 = &mut s4.y
        (var_y ::= s5) ;;                -- y = s5
        (letsite s6 ← copy var_x) ;;     -- s6 = copy(x)
        Stmt.writeRef s6 (.site 10) ;;   -- *s6 = 0
        (letsite s7 ← copy var_y) ;;     -- s7 = copy(y)
        Stmt.writeRef s7 (.site 11) ;;   -- *s7 = 0
        (letsite s8 ← copy var_tl)       -- s8 = copy(tl)
      terminator := ret [s8]             -- return s8
    }
  ]
}

-- Theorems: both functions are well-typed
theorem borrow_welltyped : ∃ lenv, typecheck_fun fn_borrow lenv := by
  sorry

theorem write_welltyped : ∃ lenv, typecheck_fun fn_write lenv := by
  sorry

end LeanMove.Examples.Expressivity.ExtensionAfterCall
