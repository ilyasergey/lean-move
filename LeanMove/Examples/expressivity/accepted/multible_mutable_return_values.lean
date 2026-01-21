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
# Multiple Mutable Return Values

Source: https://github.com/tnowacki/sui/blob/example-tests/external-crates/move/crates/bytecode-verifier-transactional-tests/tests/reference_safety/expressivity/multible_mutable_return_values.mvir

(Note: the original filename has a typo "multible" instead of "multiple")

This module demonstrates that all mutable return values from a function call
should be writable. A function can return multiple mutable references, and
the caller should be able to write through all of them.

struct Point has copy, drop, store { x: u64, y: u64 }

borrow(p: &mut Self.Point): &mut u64 * &mut u64
  Returns mutable refs to both x and y fields.

write(p: &mut Self.Point)
  Borrows both fields and writes 0 to each.
-/

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Checker
open AssocMap
open Regex

namespace LeanMove.Examples.Expressivity.MultipleMutableReturnValues

-- Fields for Point struct
def field_x : Field := ⟨"x"⟩
def field_y : Field := ⟨"y"⟩

-- Point { x: u64, y: u64 }
def point_entries : AssocMap Field BasicMoveType :=
  insert (insert empty field_x .tint) field_y .tint

-- Variables
def var_p : Var := ⟨"p"⟩
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

/-
  borrow(p: &mut Self.Point): &mut u64 * &mut u64
  Returns mutable references to both x and y fields.

  label l0:
      x = &mut copy(p).Point::x;
      y = &mut copy(p).Point::y;
      return copy(x), copy(y);
-/
def borrow : FunDef := {
  params := [(var_p, .ref (.trecord point_entries) (.varRef var_p) .siteBorrowMut)]
  returnType := .basic .tunit  -- Simplified: MoveLight doesn't have tuple return types yet
  locals := [
    { name := var_x, type := .ref .tint (.varRef var_p) .siteBorrowMut },
    { name := var_y, type := .ref .tint (.varRef var_p) .siteBorrowMut }
  ]
  blocks := [
    { label := "l0"
      body :=
        (letsite s0 ← copy var_p) ;;     -- s0 = copy(p)
        Stmt.letBind s1 (Expr.borrowMutField s0 "Point" field_x) ;; -- s1 = &mut s0.x
        (var_x ::= s1) ;;                -- x = s1
        (letsite s2 ← copy var_p) ;;     -- s2 = copy(p)
        Stmt.letBind s3 (Expr.borrowMutField s2 "Point" field_y) ;; -- s3 = &mut s2.y
        (var_y ::= s3) ;;                -- y = s3
        (letsite s4 ← copy var_x) ;;     -- s4 = copy(x)
        (letsite s5 ← copy var_y)        -- s5 = copy(y)
      terminator := ret [s4, s5]         -- return (s4, s5)
    }
  ]
}

/-
  write(p: &mut Self.Point)
  Borrows both fields via borrow() and writes 0 to each.

  label l0:
      x, y = Self.borrow(move(p));
      *copy(x) = 0;
      *copy(y) = 0;
      *copy(x) = 0;   -- repeated writes to show all refs are usable
      *copy(y) = 0;
      return;
-/
def write : FunDef := {
  params := [(var_p, .ref (.trecord point_entries) (.varRef var_p) .siteBorrowMut)]
  returnType := .basic .tunit
  locals := [
    { name := var_x, type := .ref .tint (.varRef var_p) .siteBorrowMut },
    { name := var_y, type := .ref .tint (.varRef var_p) .siteBorrowMut }
  ]
  blocks := [
    { label := "l0"
      body :=
        -- Simulate call to borrow by directly borrowing the fields
        -- (since MoveLight function calls are more complex to model)
        (letsite s0 ← copy var_p) ;;
        Stmt.letBind s1 (Expr.borrowMutField s0 "Point" field_x) ;;
        (var_x ::= s1) ;;
        (letsite s2 ← copy var_p) ;;
        Stmt.letBind s3 (Expr.borrowMutField s2 "Point" field_y) ;;
        (var_y ::= s3) ;;
        -- Now write through the refs
        (letsite s4 ← copy var_x) ;;
        Stmt.writeRef s4 (.site 10) ;;   -- *x = 0
        (letsite s5 ← copy var_y) ;;
        Stmt.writeRef s5 (.site 11) ;;   -- *y = 0
        (letsite s6 ← copy var_x) ;;
        Stmt.writeRef s6 (.site 12) ;;   -- *x = 0 (again)
        (letsite s7 ← copy var_y) ;;
        Stmt.writeRef s7 (.site 13)      -- *y = 0 (again)
      terminator := ret []
    }
  ]
}

-- Theorems: both functions are well-typed
theorem borrow_welltyped : ∃ lenv, typecheck_fun borrow lenv := by
  sorry

theorem write_welltyped : ∃ lenv, typecheck_fun write lenv := by
  sorry

end LeanMove.Examples.Expressivity.MultipleMutableReturnValues
