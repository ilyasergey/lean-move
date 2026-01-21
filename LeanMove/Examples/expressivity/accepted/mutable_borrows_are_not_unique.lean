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
# Mutable Borrows Are Not Unique

Source: https://github.com/tnowacki/sui/blob/example-tests/external-crates/move/crates/bytecode-verifier-transactional-tests/tests/reference_safety/expressivity/mutable_borrows_are_not_unique.mvir

Two modules demonstrating that mutable variables/references are not unique and
don't take ownership over their memory:

1. fields: Creates multiple mutable refs to nested fields
2. fields_write: Same but also performs writes through all refs

The key insight is that "order does not matter as long as the reference has no extensions."
-/

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Checker
open AssocMap
open Regex

namespace LeanMove.Examples.Expressivity.MutableBorrowsNotUnique

-- Fields for structs
def field_f : Field := ⟨"f"⟩
def field_0 : Field := ⟨"0"⟩  -- first element
def field_1 : Field := ⟨"1"⟩  -- second element

-- Types for nested structs
-- S { f: u64 }
def s_entries : AssocMap Field BasicMoveType := insert empty field_f .tint

-- Pair { 0: S, 1: S } (tuple-like)
def pair_entries : AssocMap Field BasicMoveType :=
  insert (insert empty field_0 (.trecord s_entries)) field_1 (.trecord s_entries)

-- Variables
def var_local : Var := ⟨"local"⟩
def var_root : Var := ⟨"root"⟩
def var_s0 : Var := ⟨"s0"⟩
def var_s1 : Var := ⟨"s1"⟩
def var_f0 : Var := ⟨"f0"⟩
def var_f1 : Var := ⟨"f1"⟩

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

/-
  Module 1: fields
  Creates multiple mutable references to nested fields without writing.

  struct S has copy, drop { f: u64 }
  struct Pair has copy, drop { 0: S, 1: S }

  create(p: &mut Self.Pair) {
  label l0:
      root = move(p);
      s0 = &mut copy(root).Pair::0;
      s1 = &mut copy(root).Pair::1;
      f0 = &mut copy(s0).S::f;
      f1 = &mut copy(s1).S::f;
      return;
  }
-/
def fields : FunDef := {
  params := [(var_local, .ref (.trecord pair_entries) (.varRef var_local) .siteBorrowMut)]
  returnType := .basic .tunit
  locals := [
    { name := var_root, type := .ref (.trecord pair_entries) (.varRef var_local) .siteBorrowMut },
    { name := var_s0, type := .ref (.trecord s_entries) (.varRef var_local) .siteBorrowMut },
    { name := var_s1, type := .ref (.trecord s_entries) (.varRef var_local) .siteBorrowMut },
    { name := var_f0, type := .ref .tint (.varRef var_local) .siteBorrowMut },
    { name := var_f1, type := .ref .tint (.varRef var_local) .siteBorrowMut }
  ]
  blocks := [
    { label := "l0"
      body :=
        (letsite s0 ← move var_local) ;; -- s0 = move(p)
        (var_root ::= s0) ;;             -- root = s0
        (letsite s1 ← copy var_root) ;;  -- s1 = copy(root)
        Stmt.letBind s2 (Expr.borrowMutField s1 "Pair" field_0) ;; -- s2 = &mut s1.0
        (var_s0 ::= s2) ;;               -- s0_ = s2
        (letsite s3 ← copy var_root) ;;  -- s3 = copy(root)
        Stmt.letBind s4 (Expr.borrowMutField s3 "Pair" field_1) ;; -- s4 = &mut s3.1
        (var_s1 ::= s4) ;;               -- s1_ = s4
        (letsite s5 ← copy var_s0) ;;    -- s5 = copy(s0_)
        Stmt.letBind s6 (Expr.borrowMutField s5 "S" field_f) ;; -- s6 = &mut s5.f
        (var_f0 ::= s6) ;;               -- f0 = s6
        (letsite s7 ← copy var_s1) ;;    -- s7 = copy(s1_)
        Stmt.letBind s8 (Expr.borrowMutField s7 "S" field_f) ;; -- s8 = &mut s7.f
        (var_f1 ::= s8) ;;               -- f1 = s8
        Stmt.ret []
    }
  ]
}

/-
  Module 2: fields_write
  Same as fields but also writes through all references.

  The writes are safe because "order does not matter as long as the reference has no extensions."
-/
def fields_write : FunDef := {
  params := [(var_local, .ref (.trecord pair_entries) (.varRef var_local) .siteBorrowMut)]
  returnType := .basic .tunit
  locals := [
    { name := var_root, type := .ref (.trecord pair_entries) (.varRef var_local) .siteBorrowMut },
    { name := var_s0, type := .ref (.trecord s_entries) (.varRef var_local) .siteBorrowMut },
    { name := var_s1, type := .ref (.trecord s_entries) (.varRef var_local) .siteBorrowMut },
    { name := var_f0, type := .ref .tint (.varRef var_local) .siteBorrowMut },
    { name := var_f1, type := .ref .tint (.varRef var_local) .siteBorrowMut }
  ]
  blocks := [
    { label := "l0"
      body :=
        (letsite s0 ← move var_local) ;; -- s0 = move(p)
        (var_root ::= s0) ;;             -- root = s0
        (letsite s1 ← copy var_root) ;;  -- s1 = copy(root)
        Stmt.letBind s2 (Expr.borrowMutField s1 "Pair" field_0) ;; -- s2 = &mut s1.0
        (var_s0 ::= s2) ;;               -- s0_ = s2
        (letsite s3 ← copy var_root) ;;  -- s3 = copy(root)
        Stmt.letBind s4 (Expr.borrowMutField s3 "Pair" field_1) ;; -- s4 = &mut s3.1
        (var_s1 ::= s4) ;;               -- s1_ = s4
        (letsite s5 ← copy var_s0) ;;    -- s5 = copy(s0_)
        Stmt.letBind s6 (Expr.borrowMutField s5 "S" field_f) ;; -- s6 = &mut s5.f
        (var_f0 ::= s6) ;;               -- f0 = s6
        (letsite s7 ← copy var_s1) ;;    -- s7 = copy(s1_)
        Stmt.letBind s8 (Expr.borrowMutField s7 "S" field_f) ;; -- s8 = &mut s7.f
        (var_f1 ::= s8) ;;               -- f1 = s8
        -- Now perform writes (consuming copies of the refs)
        (letsite (.site 10) ← copy var_f0) ;;
        Stmt.writeRef (.site 10) (.site 11) ;;  -- *f0 = 0
        (letsite (.site 12) ← copy var_f1) ;;
        Stmt.writeRef (.site 12) (.site 13) ;;  -- *f1 = 0
        Stmt.ret []
    }
  ]
}

-- Theorems: both functions are well-typed
theorem fields_welltyped : ∃ lenv, typecheck_fun fields lenv := by
  sorry

theorem fields_write_welltyped : ∃ lenv, typecheck_fun fields_write lenv := by
  sorry

end LeanMove.Examples.Expressivity.MutableBorrowsNotUnique
