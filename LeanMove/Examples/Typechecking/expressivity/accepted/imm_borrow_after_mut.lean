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
import LeanMove.Typing.TypeChecking
import LeanMove.Typing.Algorithmic.DecidableTypeEnv
import LeanMove.Lang.Macros

/-!
# Immutable Borrow After Mutable

Source: https://github.com/tnowacki/sui/blob/example-tests/external-crates/move/crates/bytecode-verifier-transactional-tests/tests/reference_safety/expressivity/imm_borrow_after_mut.mvir

Two modules demonstrating that immutable references can coexist with mutable
references when properly sequenced:

1. direct: Creates mutable ref, then immutable ref to same var; writes then reads
2. copy_and_freeze: Creates mutable ref, freezes a copy to get immutable ref

Both demonstrate safe patterns where mutable and immutable references coexist.
-/

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Typing
open AssocMap
open Regex

namespace LeanMove.Examples.Expressivity.ImmBorrowAfterMut

-- Variables
def var_a : Var := ⟨"a"⟩
def var_rmut : Var := ⟨"rmut"⟩
def var_rimm : Var := ⟨"rimm"⟩

-- Sites
def s0 : Site := .site 0   -- constant 0
def s1 : Site := .site 1   -- &mut a
def s2 : Site := .site 2   -- &a or freeze(copy(rmut))
def s3 : Site := .site 3   -- copy(rmut)
def s4 : Site := .site 4   -- constant for write
def s5 : Site := .site 5   -- copy(rimm)
def s6 : Site := .site 6   -- *copy(rimm)
def s7 : Site := .site 7   -- second constant 0 (for copy_and_freeze write)

/-
  Module 1: direct
  Creates mutable ref, then direct immutable borrow.

  t() {
    let a: u64;
    let rmut: &mut u64;
    let rimm: &u64;
  label l0:
    a = 0;
    rmut = &mut a;
    rimm = &a;
    *copy(rmut) = 0;
    _ = *copy(rimm);
    return;
  }
-/
def direct : FunDef := {
  params := []
  returnType := .basic .tunit
  locals := [
    { name := var_a, type := .basic .u64 },
    { name := var_rmut, type := .ref .u64 (.refid 1) .siteBorrowMut },
    { name := var_rimm, type := .ref .u64 (.refid 2) .siteBorrowImm }
  ]
  blocks := [
    { label := "l0"
      body :=
        (letsite s0 ← #0) ;;            -- s0 = 0 (integer literal)
        (var_a ::= s0) ;;               -- a = s0
        (letsite s1 ← &mut var_a) ;;    -- s1 = &mut a
        (var_rmut ::= s1) ;;            -- rmut = s1
        (letsite s2 ← &var_a) ;;        -- s2 = &a
        (var_rimm ::= s2) ;;            -- rimm = s2
        (letsite s3 ← copy var_rmut) ;; -- s3 = copy(rmut)
        (letsite s4 ← #0) ;;            -- s4 = 0 (integer literal for write)
        Stmt.writeRef s3 s4 ;;          -- *s3 = s4
        (letsite s5 ← copy var_rimm) ;; -- s5 = copy(rimm)
        Stmt.letBind s6 (Expr.readRef s5) ;; -- s6 = *s5 (discarded)
        Stmt.ret []
    }
  ]
}

/-
  Module 2: copy_and_freeze
  Creates mutable ref, copies and freezes it to get immutable ref.

  t() {
    let a: u64;
    let rmut: &mut u64;
    let rimm: &u64;
  label l0:
    a = 0;
    rmut = &mut a;
    rimm = freeze(copy(rmut));
    *copy(rmut) = 0;
    _ = *copy(rimm);
    return;
  }
-/
def copy_and_freeze : FunDef := {
  params := []
  returnType := .basic .tunit
  locals := [
    { name := var_a, type := .basic .u64 },
    { name := var_rmut, type := .ref .u64 (.refid 1) .siteBorrowMut },
    { name := var_rimm, type := .ref .u64 (.refid 2) .siteBorrowImm }
  ]
  blocks := [
    { label := "l0"
      body :=
        (letsite s0 ← #0) ;;            -- s0 = 0 (integer literal)
        (var_a ::= s0) ;;               -- a = s0
        (letsite s1 ← &mut var_a) ;;    -- s1 = &mut a
        (var_rmut ::= s1) ;;            -- rmut = s1
        (letsite s2 ← copy var_rmut) ;; -- s2 = copy(rmut)
        Stmt.letBind s3 (Expr.freeze s2) ;; -- s3 = freeze(s2)
        (var_rimm ::= s3) ;;            -- rimm = s3
        (letsite s4 ← copy var_rmut) ;; -- s4 = copy(rmut)
        (letsite s7 ← #0) ;;            -- s7 = 0 (integer literal for write)
        Stmt.writeRef s4 s7 ;;          -- *s4 = s7
        (letsite s5 ← copy var_rimm) ;; -- s5 = copy(rimm)
        Stmt.letBind s6 (Expr.readRef s5) ;; -- s6 = *s5 (discarded)
        Stmt.ret []
    }
  ]
}

-- -----------------------------------------------------
-- -           Algorithmic Type Checking Tests        --
-- -----------------------------------------------------

-- Initial environments (decidable)
def direct_initEnvDec : TypeEnvDec := {
  siteEnv := AssocMap.empty
  varEnv := init_fun_varEnv direct
  pathEnv := .init
  funEnv := AssocMap.empty
}

def direct_lenvDec : LabelEnvDec :=
  AssocMap.insert AssocMap.empty "l0" direct_initEnvDec

def copy_and_freeze_initEnvDec : TypeEnvDec := {
  siteEnv := AssocMap.empty
  varEnv := init_fun_varEnv copy_and_freeze
  pathEnv := .init
  funEnv := AssocMap.empty
}

def copy_and_freeze_lenvDec : LabelEnvDec :=
  AssocMap.insert AssocMap.empty "l0" copy_and_freeze_initEnvDec

-- Theorems: both functions type check algorithmically
theorem direct_check : check_fun_dec direct direct_lenvDec = true := by rfl
theorem copy_and_freeze_check : check_fun_dec copy_and_freeze copy_and_freeze_lenvDec = true := by rfl

-- -----------------------------------------------------
-- -           Relational Type Checking Theorems      --
-- -----------------------------------------------------

theorem direct_welltyped : ∃ lenv, typecheck_fun direct lenv :=
  ⟨_, check_fun_dec_sound _ _ direct_check⟩

theorem copy_and_freeze_welltyped : ∃ lenv, typecheck_fun copy_and_freeze lenv :=
  ⟨_, check_fun_dec_sound _ _ copy_and_freeze_check⟩

end LeanMove.Examples.Expressivity.ImmBorrowAfterMut
