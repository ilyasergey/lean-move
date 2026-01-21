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
# Simple Dangling Reference Examples

Source: https://github.com/tnowacki/sui/blob/example-tests/external-crates/move/crates/bytecode-verifier-transactional-tests/tests/reference_safety/expressivity/simple_dangling.mvir

This file contains five modules that all fail with WRITEREF_EXISTS_BORROW_ERROR.
Each demonstrates a different way to create a dangling reference:

1. field: Borrow a struct field, then reassign the struct
2. nested_field: Borrow a nested field, then reassign intermediate struct
3. vector: Borrow a vector element, then clear the vector
4. simple_call: Pass mutable ref to function, modify original after
5. field_call: Borrow field via function, modify struct after

All are REJECTED by the type checker because they would create dangling references.
-/

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Checker
open AssocMap
open Regex

namespace LeanMove.Examples.Expressivity.SimpleDangling

-- Fields for structs
def field_f : Field := ⟨"f"⟩
def field_inner : Field := ⟨"inner"⟩

-- S { f: u64 }
def s_entries : AssocMap Field BasicMoveType := insert empty field_f .tint

-- Outer { inner: S }
def outer_entries : AssocMap Field BasicMoveType :=
  insert empty field_inner (.trecord s_entries)

-- Variables
def var_s : Var := ⟨"s"⟩
def var_outer : Var := ⟨"outer"⟩
def var_f : Var := ⟨"f"⟩
def var_inner : Var := ⟨"inner"⟩

-- Sites
def s0 : Site := .site 0
def s1 : Site := .site 1
def s2 : Site := .site 2
def s3 : Site := .site 3
def s4 : Site := .site 4
def s5 : Site := .site 5

/-
  Module 1: field
  Borrows a struct field, then reassigns the struct - creates dangling ref.

  t() {
    let s: Self.S;
    let f: &mut u64;
  label l0:
    s = S { f: 0 };
    f = &mut copy(s).S::f;   // f points into s
    s = S { f: 0 };          // ERROR: s is reassigned while f is live
    return;
  }
-/
def field : FunDef := {
  params := []
  returnType := .basic .tunit
  locals := [
    { name := var_s, type := .basic (.trecord s_entries) },
    { name := var_f, type := .ref .tint (.varRef var_s) .siteBorrowMut }
  ]
  blocks := [
    { label := "l0"
      body :=
        -- Pack s = S { f: 0 }
        Stmt.letBind s0 (Expr.pack "S" [(field_f, .site 10)]) ;;
        (var_s ::= s0) ;;                -- s = packed value
        -- f = &mut s.f
        (letsite s1 ← &mut var_s) ;;     -- s1 = &mut s
        Stmt.letBind s2 (Expr.borrowMutField s1 "S" field_f) ;; -- s2 = &mut s1.f
        (var_f ::= s2) ;;                -- f = s2 (f points into s)
        -- s = S { f: 0 } -- THIS SHOULD FAIL: s is borrowed
        Stmt.letBind s3 (Expr.pack "S" [(field_f, .site 11)]) ;;
        (var_s ::= s3)                   -- ERROR: reassigning while f is live
      terminator := ret []
    }
  ]
}

/-
  Module 2: nested_field
  Borrows a deeply nested field, then reassigns intermediate struct.

  t() {
    let outer: Self.Outer;
    let f: &mut u64;
  label l0:
    outer = Outer { inner: S { f: 0 } };
    f = &mut copy(outer).Outer::inner.S::f;
    outer = Outer { inner: S { f: 0 } };  // ERROR: outer borrowed via f
    return;
  }
-/
def nested_field : FunDef := {
  params := []
  returnType := .basic .tunit
  locals := [
    { name := var_outer, type := .basic (.trecord outer_entries) },
    { name := var_f, type := .ref .tint (.varRef var_outer) .siteBorrowMut }
  ]
  blocks := [
    { label := "l0"
      body :=
        -- Pack inner S
        Stmt.letBind s0 (Expr.pack "S" [(field_f, .site 10)]) ;;
        -- Pack outer with inner
        Stmt.letBind s1 (Expr.pack "Outer" [(field_inner, s0)]) ;;
        (var_outer ::= s1) ;;            -- outer = Outer { inner: S { f: 0 } }
        -- Navigate and borrow f
        (letsite s2 ← &mut var_outer) ;; -- s2 = &mut outer
        Stmt.letBind s3 (Expr.borrowMutField s2 "Outer" field_inner) ;; -- s3 = &mut s2.inner
        Stmt.letBind s4 (Expr.borrowMutField s3 "S" field_f) ;; -- s4 = &mut s3.f
        (var_f ::= s4) ;;                -- f = s4 (f points deep into outer)
        -- Reassign outer - ERROR: borrowed through f
        Stmt.letBind (.site 20) (Expr.pack "S" [(field_f, .site 11)]) ;;
        Stmt.letBind (.site 21) (Expr.pack "Outer" [(field_inner, .site 20)]) ;;
        (var_outer ::= (.site 21))       -- ERROR: reassigning while f is live
      terminator := ret []
    }
  ]
}

/-
  Module 3: vector (simplified - vectors not directly supported in MoveLight)
  Borrows a vector element, then clears the vector.

  For MoveLight, we simulate this with a struct containing multiple u64 fields.
-/
-- Skipped: MoveLight doesn't have native vector support

/-
  Module 4: simple_call (simplified)
  Passes mutable reference to a function that returns immutable reference,
  then tries to modify the original.
-/
def simple_call : FunDef := {
  params := []
  returnType := .basic .tunit
  locals := [
    { name := var_s, type := .basic (.trecord s_entries) },
    { name := var_f, type := .ref .tint (.varRef var_s) .siteBorrowMut }
  ]
  blocks := [
    { label := "l0"
      body :=
        -- s = S { f: 0 }
        Stmt.letBind s0 (Expr.pack "S" [(field_f, .site 10)]) ;;
        (var_s ::= s0) ;;
        -- f = &mut s.f
        (letsite s1 ← &mut var_s) ;;
        Stmt.letBind s2 (Expr.borrowMutField s1 "S" field_f) ;;
        (var_f ::= s2) ;;
        -- Freeze to get immutable reference
        (letsite s3 ← copy var_f) ;;
        Stmt.letBind s4 (Expr.freeze s3) ;; -- s4 = immutable ref
        -- Now try to write through the original mutable ref - should fail
        -- because there's an immutable alias
        (letsite s5 ← copy var_f) ;;
        Stmt.writeRef s5 (.site 11)      -- ERROR: writing with imm alias
      terminator := ret []
    }
  ]
}

-- Theorems: all functions are ILL-typed (rejected by type checker)
theorem field_illtyped : ¬ (∃ lenv, typecheck_fun field lenv) := by
  sorry

theorem nested_field_illtyped : ¬ (∃ lenv, typecheck_fun nested_field lenv) := by
  sorry

theorem simple_call_illtyped : ¬ (∃ lenv, typecheck_fun simple_call lenv) := by
  sorry

end LeanMove.Examples.Expressivity.SimpleDangling
