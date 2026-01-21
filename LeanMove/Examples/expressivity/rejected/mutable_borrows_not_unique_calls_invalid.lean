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

This file contains the INVALID module (call_and_write_invalid) that fails because
you cannot write to mutable references when their relationship is unknown.

Original MVIR:
```
// mutable borrows are not unique

//# publish
module 0x4.call {

    struct S has copy, drop { f: u64 }

    borrow_f(s: &mut Self.S): &mut u64 {
    label b0:
        return &mut move(s).S::f;
    }

    create(s: &mut Self.S) {
        let call: &mut u64;
        let f: &mut u64;
    label b0:
        // we can create multiple mutable references, even with a call, as long as the argument
        // to the call does not have any extensions at the time of the call (and as long as it does
        // not overlap with any other arguments)

        // if we swap the call with the field borrow, this will error
        call = Self.borrow_f(copy(s));
        f = &mut copy(s).S::f;
        return;
    }

}

//# publish
module 0x5.call_and_write_invalid {

    struct S has copy, drop { f: u64 }

    borrow_f(s: &mut Self.S): &mut u64 {
    label b0:
        return &mut move(s).S::f;
    }

    write(s: &mut Self.S) {
        let call: &mut u64;
        let f: &mut u64;
    label b0:
        // While mutable references are not unique, and we can create all sorts of overlaps, that
        // does not mean that we can write to all of them.
        // We cannot write to either call or f since we do not know the relationship between them.
        // While it is "safe" in this case, we do not look at the type layout for that information.
        // It could be the case that f extends call, and that call extends f.
        call = Self.borrow_f(copy(s));
        f = &mut copy(s).S::f;
        *copy(call) = 0;
        *copy(f) = 0;
        return;
    }

}

//# publish
module 0x6.call_and_write_valid {

    struct S has copy, drop { f: u64 }

    borrow_f(s: &mut Self.S): &mut u64 {
    label b0:
        return &mut move(s).S::f;
    }

    write(s: &mut Self.S) {
        let call: &mut u64;
        let f: &mut u64;
    label b0:
        // If however we free the call's return value before borrowing f, this is valid.
        call = Self.borrow_f(copy(s));
        *move(call) = 0; // the move frees the value
        f = &mut copy(s).S::f;
        *copy(f) = 0;
        return;
    }

}
```
-/

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Checker
open AssocMap
open Regex

namespace LeanMove.Examples.Expressivity.MutableBorrowsNotUniqueCallsInvalid

-- Fields for struct
def field_f : Field := ⟨"f"⟩

-- S { f: u64 }
def s_entries : AssocMap Field BasicMoveType := insert empty field_f .u64

-- Variables
def var_s : Var := ⟨"s"⟩
def var_call : Var := ⟨"call"⟩
def var_f : Var := ⟨"f"⟩

-- Sites
def s0 : Site := .site 0   -- copy(s) for call
def s1 : Site := .site 1   -- &mut s0.S::f (result of borrow_f call)
def s2 : Site := .site 2   -- copy(s) for f
def s3 : Site := .site 3   -- &mut s2.S::f (for f)
def s4 : Site := .site 4   -- copy(call)
def s5 : Site := .site 5   -- integer literal 0 for first write
def s6 : Site := .site 6   -- copy(f)
def s7 : Site := .site 7   -- integer literal 0 for second write

/-
  call_and_write_invalid module: "we cannot write to either call or f since we
  do not know the relationship between them"

  write(s: &mut Self.S) {
      let call: &mut u64;
      let f: &mut u64;
  label b0:
      call = Self.borrow_f(copy(s));  -- inlined as: &mut copy(s).S::f
      f = &mut copy(s).S::f;
      *copy(call) = 0;                -- ERROR: relationship with f unknown
      *copy(f) = 0;                   -- ERROR: relationship with call unknown
      return;
  }
-/
def call_and_write_invalid : FunDef := {
  params := [(var_s, .ref (.trecord s_entries) (.varRef var_s) .siteBorrowMut)]
  returnType := .basic .tunit
  locals := [
    { name := var_call, type := .ref .u64 (.varRef var_s) .siteBorrowMut },
    { name := var_f, type := .ref .u64 (.varRef var_s) .siteBorrowMut }
  ]
  blocks := [
    { label := "b0"
      body :=
        -- call = Self.borrow_f(copy(s)) -- inlined as &mut copy(s).S::f
        (letsite s0 ← copy var_s) ;;
        Stmt.letBind s1 (Expr.borrowMutField s0 (.trecord s_entries) field_f) ;;
        (var_call ::= s1) ;;
        -- f = &mut copy(s).S::f
        (letsite s2 ← copy var_s) ;;
        Stmt.letBind s3 (Expr.borrowMutField s2 (.trecord s_entries) field_f) ;;
        (var_f ::= s3) ;;
        -- *copy(call) = 0 -- ERROR: relationship with f unknown
        (letsite s4 ← copy var_call) ;;
        (letsite s5 ← #0) ;;
        Stmt.writeRef s4 s5 ;;
        -- *copy(f) = 0 -- ERROR: relationship with call unknown
        (letsite s6 ← copy var_f) ;;
        (letsite s7 ← #0) ;;
        Stmt.writeRef s6 s7
      terminator := ret []
    }
  ]
}

-- Theorem: call_and_write_invalid is ILL-typed (REJECTED by type checker)
theorem call_and_write_invalid_illtyped : ¬ (∃ lenv, typecheck_fun call_and_write_invalid lenv) := by
  sorry

end LeanMove.Examples.Expressivity.MutableBorrowsNotUniqueCallsInvalid
