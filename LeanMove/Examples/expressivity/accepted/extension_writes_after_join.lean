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
# Extension Writes After Join

Source: https://github.com/tnowacki/sui/blob/example-tests/external-crates/move/crates/bytecode-verifier-transactional-tests/tests/reference_safety/expressivity/extension_writes_after_join.mvir

This module demonstrates writing to extensions after a control flow join.

struct S has copy, drop, store { f: u64 }

t(cond: bool, a: &mut S, b: &mut S): &mut S
  Based on condition, swaps which ref goes to x.
  Then borrows x.f and writes through it.
  Returns one of the references.
-/

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Checker
open AssocMap
open Regex

namespace LeanMove.Examples.Expressivity.ExtensionWritesAfterJoin

-- Field for S struct
def field_f : Field := ⟨"f"⟩

-- S { f: u64 }
def s_entries : AssocMap Field BasicMoveType := insert empty field_f .tint

-- Variables
def var_cond : Var := ⟨"cond"⟩
def var_a : Var := ⟨"a"⟩
def var_b : Var := ⟨"b"⟩
def var_x : Var := ⟨"x"⟩
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
  t(cond: bool, a: &mut Self.S, b: &mut Self.S): &mut Self.S

  label l0:
      jump_if (copy(cond)) l2;
  label l1:
      x = copy(a);
      jump l3;
  label l2:
      x = copy(b);
      jump l3;
  label l3:
      f = &mut copy(x).S::f;
      *copy(f) = 0;
      return copy(x);
-/
def t : FunDef := {
  params := [
    (var_cond, .basic .tbool),
    (var_a, .ref (.trecord s_entries) (.varRef var_a) .siteBorrowMut),
    (var_b, .ref (.trecord s_entries) (.varRef var_b) .siteBorrowMut)
  ]
  returnType := .basic .tunit  -- Simplified
  locals := [
    { name := var_x, type := .ref (.trecord s_entries) (.varRef var_a) .siteBorrowMut },
    { name := var_f, type := .ref .tint (.varRef var_a) .siteBorrowMut }
  ]
  blocks := [
    -- l0: branch on condition
    { label := "l0"
      body :=
        (letsite s0 ← copy var_cond) ;;  -- s0 = copy(cond)
        Stmt.branch s0 "l2" "l1"         -- if s0 then l2 else l1
    },
    -- l1 (false branch): x = copy(a)
    { label := "l1"
      body :=
        (letsite s1 ← copy var_a) ;;     -- s1 = copy(a)
        (var_x ::= s1) ;;                -- x = s1
        jump "l3"
    },
    -- l2 (true branch): x = copy(b)
    { label := "l2"
      body :=
        (letsite s1 ← copy var_b) ;;     -- s1 = copy(b)
        (var_x ::= s1) ;;                -- x = s1
        jump "l3"
    },
    -- l3: borrow field and write
    { label := "l3"
      body :=
        (letsite s2 ← copy var_x) ;;     -- s2 = copy(x)
        Stmt.letBind s3 (Expr.borrowMutField s2 "S" field_f) ;; -- s3 = &mut s2.f
        (var_f ::= s3) ;;                -- f = s3
        (letsite s4 ← copy var_f) ;;     -- s4 = copy(f)
        Stmt.writeRef s4 (.site 10) ;;   -- *s4 = 0
        (letsite s5 ← copy var_x) ;;     -- s5 = copy(x)
        Stmt.ret [s5]                    -- return s5
    }
  ]
}

-- Theorem: t is well-typed
theorem t_welltyped : ∃ lenv, typecheck_fun t lenv := by
  sorry

end LeanMove.Examples.Expressivity.ExtensionWritesAfterJoin
