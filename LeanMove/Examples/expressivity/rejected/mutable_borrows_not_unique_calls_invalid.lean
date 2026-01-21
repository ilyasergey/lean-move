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
# Mutable Borrows Not Unique Calls - Invalid Module

Source: https://github.com/tnowacki/sui/blob/example-tests/external-crates/move/crates/bytecode-verifier-transactional-tests/tests/reference_safety/expressivity/mutable_borrows_are_not_unique_calls.mvir

This is the INVALID module (call_and_write_invalid) from the test.
It fails with WRITEREF_EXISTS_BORROW_ERROR.

The issue: When we create mutable references through a function call, we cannot
write to either the call's return value or a field borrow "since we do not know
the relationship between them."

Comment from original: "we cannot write to either call or f since we do not know
the relationship between them"
-/

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Checker
open AssocMap
open Regex

namespace LeanMove.Examples.Expressivity.MutableBorrowsNotUniqueCallsInvalid

-- Fields for structs
def field_f : Field := ⟨"f"⟩
def field_0 : Field := ⟨"0"⟩
def field_1 : Field := ⟨"1"⟩

-- S { f: u64 }
def s_entries : AssocMap Field BasicMoveType := insert empty field_f .tint

-- Pair { 0: S, 1: S }
def pair_entries : AssocMap Field BasicMoveType :=
  insert (insert empty field_0 (.trecord s_entries)) field_1 (.trecord s_entries)

-- Variables
def var_local : Var := ⟨"local"⟩
def var_root : Var := ⟨"root"⟩
def var_call : Var := ⟨"call"⟩  -- result from function call
def var_f : Var := ⟨"f"⟩

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
  call_and_write_invalid: "we cannot write to either call or f since we do not
  know the relationship between them"

  t(p: &mut Self.Pair) {
  label l0:
    root = move(p);
    // call = Self.get(copy(root));  -- returns &mut u64
    // For encoding, we simulate get() as borrowing field 0's f
    call = &mut copy(root).Pair::0.S::f;
    f = &mut copy(root).Pair::0.S::f;
    *copy(call) = 0;    // ERROR: don't know relationship with f
    *copy(f) = 0;       // ERROR: don't know relationship with call
    return;
  }
-/
def call_and_write_invalid : FunDef := {
  params := [(var_local, .ref (.trecord pair_entries) (.varRef var_local) .siteBorrowMut)]
  returnType := .basic .tunit
  locals := [
    { name := var_root, type := .ref (.trecord pair_entries) (.varRef var_local) .siteBorrowMut },
    { name := var_call, type := .ref .tint (.varRef var_local) .siteBorrowMut },
    { name := var_f, type := .ref .tint (.varRef var_local) .siteBorrowMut }
  ]
  blocks := [
    { label := "l0"
      body :=
        -- root = move(p)
        (letsite s0 ← move var_local) ;;
        (var_root ::= s0) ;;
        -- call = &mut root.0.f (simulating function call result)
        (letsite s1 ← copy var_root) ;;
        Stmt.letBind s2 (Expr.borrowMutField s1 "Pair" field_0) ;;
        Stmt.letBind s3 (Expr.borrowMutField s2 "S" field_f) ;;
        (var_call ::= s3) ;;
        -- f = &mut root.0.f (another borrow to same location)
        (letsite s4 ← copy var_root) ;;
        Stmt.letBind s5 (Expr.borrowMutField s4 "Pair" field_0) ;;
        Stmt.letBind s6 (Expr.borrowMutField s5 "S" field_f) ;;
        (var_f ::= s6) ;;
        -- *copy(call) = 0 -- ERROR: f might alias
        (letsite s7 ← copy var_call) ;;
        Stmt.writeRef s7 (.site 10) ;;  -- ERROR: unknown relationship with f
        -- *copy(f) = 0 -- ERROR: call might alias
        (letsite (.site 8) ← copy var_f) ;;
        Stmt.writeRef (.site 8) (.site 11) -- ERROR: unknown relationship with call
      terminator := ret []
    }
  ]
}

-- Theorem: call_and_write_invalid is ILL-typed
theorem call_and_write_invalid_illtyped : ¬ (∃ lenv, typecheck_fun call_and_write_invalid lenv) := by
  sorry

end LeanMove.Examples.Expressivity.MutableBorrowsNotUniqueCallsInvalid
