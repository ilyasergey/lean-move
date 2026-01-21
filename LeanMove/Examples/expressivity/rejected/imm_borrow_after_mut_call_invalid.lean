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
# Immutable Borrow After Mutable Call - Invalid Module

Source: https://github.com/tnowacki/sui/blob/example-tests/external-crates/move/crates/bytecode-verifier-transactional-tests/tests/reference_safety/expressivity/imm_borrow_after_mut_call.mvir

This is the INVALID module from the imm_borrow_after_mut_call test.
It fails with WRITEREF_EXISTS_BORROW_ERROR.

The issue: After creating a mutable reference and passing it through id_mut(),
then creating an immutable reference from it, you CANNOT write to the original
mutable reference because the immutable reference creates an alias.

Comment from original: "cannot write to mut1"
-/

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Checker
open AssocMap
open Regex

namespace LeanMove.Examples.Expressivity.ImmBorrowAfterMutCallInvalid

-- Variables
def var_a : Var := ⟨"a"⟩
def var_r : Var := ⟨"r"⟩
def var_mut1 : Var := ⟨"mut1"⟩
def var_imm1 : Var := ⟨"imm1"⟩

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
  invalid module: "cannot write to mut1"

  t() {
    let a: u64;
    let r: &mut u64;
    let mut1: &mut u64;
    let imm1: &u64;
  label l0:
    a = 0;
    r = &mut a;
    // Simulate: mut1 = Self.id_mut(copy(r));
    // In our encoding: mut1 = copy(r)
    mut1 = copy(r);
    // imm1 = freeze(copy(mut1));
    imm1 = freeze(copy(mut1));
    *copy(mut1) = 0;          // ERROR: cannot write - imm1 is an alias
    _ = *copy(imm1);
    return;
  }
-/
def invalid : FunDef := {
  params := []
  returnType := .basic .tunit
  locals := [
    { name := var_a, type := .basic .tint },
    { name := var_r, type := .ref .tint (.varRef var_a) .siteBorrowMut },
    { name := var_mut1, type := .ref .tint (.varRef var_a) .siteBorrowMut },
    { name := var_imm1, type := .ref .tint (.varRef var_a) .siteBorrowImm }
  ]
  blocks := [
    { label := "l0"
      body :=
        (var_a ::= s0) ;;               -- a = 0
        (letsite s1 ← &mut var_a) ;;    -- s1 = &mut a
        (var_r ::= s1) ;;               -- r = s1
        -- mut1 = copy(r) (simulating id_mut call)
        (letsite s2 ← copy var_r) ;;    -- s2 = copy(r)
        (var_mut1 ::= s2) ;;            -- mut1 = s2
        -- imm1 = freeze(copy(mut1))
        (letsite s3 ← copy var_mut1) ;; -- s3 = copy(mut1)
        Stmt.letBind s4 (Expr.freeze s3) ;; -- s4 = freeze(s3)
        (var_imm1 ::= s4) ;;            -- imm1 = s4
        -- *copy(mut1) = 0 -- ERROR: mut1 has immutable alias imm1
        (letsite s5 ← copy var_mut1) ;; -- s5 = copy(mut1)
        Stmt.writeRef s5 (.site 10) ;;  -- ERROR: write with imm alias
        -- _ = *copy(imm1)
        (letsite s6 ← copy var_imm1) ;; -- s6 = copy(imm1)
        Stmt.letBind s7 (Expr.readRef s6) -- s7 = *s6 (discard)
      terminator := ret []
    }
  ]
}

-- Theorem: invalid is ILL-typed
theorem invalid_illtyped : ¬ (∃ lenv, typecheck_fun invalid lenv) := by
  sorry

end LeanMove.Examples.Expressivity.ImmBorrowAfterMutCallInvalid
