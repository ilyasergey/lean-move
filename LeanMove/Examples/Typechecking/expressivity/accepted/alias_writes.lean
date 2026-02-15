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


import LeanMove.Lang.MoveLight
import LeanMove.Typing.TypeChecking
import LeanMove.Typing.Algorithmic.DecidableTypeEnv
import LeanMove.Lang.Macros

/-!
# Alias Writes

Source: https://github.com/tnowacki/sui/blob/example-tests/external-crates/move/crates/bytecode-verifier-transactional-tests/tests/reference_safety/expressivity/alias_writes.mvir

This file contains four modules demonstrating that writing to aliased mutable
references is safe and consistent regardless of write order:

1. borrow_local_twice: Creates two mutable refs to same var, writes through both
2. borrow_local_twice_reverse: Same as above but reversed write order
3. borrow_local_and_copy_ref: Creates ref, copies it, writes through both
4. borrow_local_and_copy_ref_reverse: Same as above but reversed write order

The key insight is that "writing to alias writes should be consistent" -
the order doesn't matter as long as references are properly released.
-/

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Typing
open AssocMap
open Regex

namespace LeanMove.Examples.Expressivity.AliasWrites

-- Variables
def var_a : Var := ⟨"a"⟩
def var_x : Var := ⟨"x"⟩
def var_y : Var := ⟨"y"⟩

-- Sites (temporaries in A-normal form)
def s0 : Site := .site 0   -- integer literal 0 (for a = 0)
def s1 : Site := .site 1   -- &mut a
def s2 : Site := .site 2   -- &mut a or copy(x)
def s3 : Site := .site 3   -- move(x) for write
def s4 : Site := .site 4   -- integer literal 0 (for first write)
def s5 : Site := .site 5   -- move(y) for write
def s6 : Site := .site 6   -- integer literal 0 (for second write)

/-
  Module 1: borrow_local_twice
  Creates two mutable references to the same local, writes through both.

  t() {
    let a: u64;
    let x: &mut u64;
    let y: &mut u64;
  label l0:
    a = 0;
    x = &mut a;
    y = &mut a;
    *move(x) = 0;
    *move(y) = 0;
    return;
  }
-/
def borrow_local_twice : FunDef := {
  params := []
  returnType := .basic .tunit
  locals := [
    { name := var_a, type := .basic .u64 },
    { name := var_x, type := .ref .u64 (.refid 1) .siteBorrowMut },
    { name := var_y, type := .ref .u64 (.refid 2) .siteBorrowMut }
  ]
  blocks := [
    { label := "l0"
      body :=
        (letsite s0 ← #0) ;;            -- s0 = 0
        (var_a ::= s0) ;;               -- a = 0
        (letsite s1 ← &mut var_a) ;;    -- s1 = &mut a
        (var_x ::= s1) ;;               -- x = s1
        (letsite s2 ← &mut var_a) ;;    -- s2 = &mut a
        (var_y ::= s2) ;;               -- y = s2
        (letsite s3 ← move var_x) ;;    -- s3 = move(x)
        (letsite s4 ← #0) ;;            -- s4 = 0
        Stmt.writeRef s3 s4 ;;          -- *s3 = 0
        (letsite s5 ← move var_y) ;;    -- s5 = move(y)
        (letsite s6 ← #0) ;;            -- s6 = 0
        Stmt.writeRef s5 s6 ;;          -- *s5 = 0
        Stmt.ret []
    }
  ]
}

/-
  Module 2: borrow_local_twice_reverse
  Same as above but writes in reverse order (y first, then x).
  *move(y) = 0; *move(x) = 0;
-/
def borrow_local_twice_reverse : FunDef := {
  params := []
  returnType := .basic .tunit
  locals := [
    { name := var_a, type := .basic .u64 },
    { name := var_x, type := .ref .u64 (.refid 1) .siteBorrowMut },
    { name := var_y, type := .ref .u64 (.refid 2) .siteBorrowMut }
  ]
  blocks := [
    { label := "l0"
      body :=
        (letsite s0 ← #0) ;;            -- s0 = 0
        (var_a ::= s0) ;;               -- a = 0
        (letsite s1 ← &mut var_a) ;;    -- s1 = &mut a
        (var_x ::= s1) ;;               -- x = s1
        (letsite s2 ← &mut var_a) ;;    -- s2 = &mut a
        (var_y ::= s2) ;;               -- y = s2
        (letsite s3 ← move var_y) ;;    -- s3 = move(y) -- reversed
        (letsite s4 ← #0) ;;            -- s4 = 0
        Stmt.writeRef s3 s4 ;;          -- *s3 = 0
        (letsite s5 ← move var_x) ;;    -- s5 = move(x) -- reversed
        (letsite s6 ← #0) ;;            -- s6 = 0
        Stmt.writeRef s5 s6 ;;          -- *s5 = 0
        Stmt.ret []
    }
  ]
}

/-
  Module 3: borrow_local_and_copy_ref
  Creates a ref, copies it to another variable, writes through both.

  t() {
    let a: u64;
    let x: &mut u64;
    let y: &mut u64;
  label l0:
    a = 0;
    x = &mut a;
    y = copy(x);
    *move(x) = 0;
    *move(y) = 0;
    return;
  }
-/
def borrow_local_and_copy_ref : FunDef := {
  params := []
  returnType := .basic .tunit
  locals := [
    { name := var_a, type := .basic .u64 },
    { name := var_x, type := .ref .u64 (.refid 1) .siteBorrowMut },
    { name := var_y, type := .ref .u64 (.refid 2) .siteBorrowMut }
  ]
  blocks := [
    { label := "l0"
      body :=
        (letsite s0 ← #0) ;;            -- s0 = 0
        (var_a ::= s0) ;;               -- a = 0
        (letsite s1 ← &mut var_a) ;;    -- s1 = &mut a
        (var_x ::= s1) ;;               -- x = s1
        (letsite s2 ← copy var_x) ;;    -- s2 = copy(x)
        (var_y ::= s2) ;;               -- y = s2
        (letsite s3 ← move var_x) ;;    -- s3 = move(x)
        (letsite s4 ← #0) ;;            -- s4 = 0
        Stmt.writeRef s3 s4 ;;          -- *s3 = 0
        (letsite s5 ← move var_y) ;;    -- s5 = move(y)
        (letsite s6 ← #0) ;;            -- s6 = 0
        Stmt.writeRef s5 s6 ;;          -- *s5 = 0
        Stmt.ret []
    }
  ]
}

/-
  Module 4: borrow_local_and_copy_ref_reverse
  Same as above but writes in reverse order.
  *move(y) = 0; *move(x) = 0;
-/
def borrow_local_and_copy_ref_reverse : FunDef := {
  params := []
  returnType := .basic .tunit
  locals := [
    { name := var_a, type := .basic .u64 },
    { name := var_x, type := .ref .u64 (.refid 1) .siteBorrowMut },
    { name := var_y, type := .ref .u64 (.refid 52) .siteBorrowMut }
  ]
  blocks := [
    { label := "l0"
      body :=
        (letsite s0 ← #0) ;;            -- s0 = 0
        (var_a ::= s0) ;;               -- a = 0
        (letsite s1 ← &mut var_a) ;;    -- s1 = &mut a
        (var_x ::= s1) ;;               -- x = s1
        (letsite s2 ← copy var_x) ;;    -- s2 = copy(x)
        (var_y ::= s2) ;;               -- y = s2
        (letsite s3 ← move var_y) ;;    -- s3 = move(y) -- reversed
        (letsite s4 ← #0) ;;            -- s4 = 0
        Stmt.writeRef s3 s4 ;;          -- *s3 = 0
        (letsite s5 ← move var_x) ;;    -- s5 = move(x) -- reversed
        (letsite s6 ← #0) ;;            -- s6 = 0
        Stmt.writeRef s5 s6 ;;          -- *s5 = 0
        Stmt.ret []
    }
  ]
}

-- -----------------------------------------------------
-- -           Algorithmic Type Checking Tests        --
-- -----------------------------------------------------

-- Initial environments (decidable)
def borrow_local_twice_lenvDec : LabelEnvDec :=
  AssocMap.insert AssocMap.empty "l0" {
    siteEnv := AssocMap.empty
    varEnv := init_fun_varEnv borrow_local_twice
    pathEnv := .init
    funEnv := AssocMap.empty
  }

def borrow_local_twice_reverse_lenvDec : LabelEnvDec :=
  AssocMap.insert AssocMap.empty "l0" {
    siteEnv := AssocMap.empty
    varEnv := init_fun_varEnv borrow_local_twice_reverse
    pathEnv := .init
    funEnv := AssocMap.empty
  }

def borrow_local_and_copy_ref_lenvDec : LabelEnvDec :=
  AssocMap.insert AssocMap.empty "l0" {
    siteEnv := AssocMap.empty
    varEnv := init_fun_varEnv borrow_local_and_copy_ref
    pathEnv := .init
    funEnv := AssocMap.empty
  }

def borrow_local_and_copy_ref_reverse_lenvDec : LabelEnvDec :=
  AssocMap.insert AssocMap.empty "l0" {
    siteEnv := AssocMap.empty
    varEnv := init_fun_varEnv borrow_local_and_copy_ref_reverse
    pathEnv := .init
    funEnv := AssocMap.empty
  }

-- Theorems: all functions type check algorithmically
theorem borrow_local_twice_check :
  check_fun_dec borrow_local_twice borrow_local_twice_lenvDec = true := by rfl

theorem borrow_local_twice_reverse_check :
  check_fun_dec borrow_local_twice_reverse borrow_local_twice_reverse_lenvDec = true := by rfl

theorem borrow_local_and_copy_ref_check :
  check_fun_dec borrow_local_and_copy_ref borrow_local_and_copy_ref_lenvDec = true := by rfl

theorem borrow_local_and_copy_ref_reverse_check :
  check_fun_dec borrow_local_and_copy_ref_reverse borrow_local_and_copy_ref_reverse_lenvDec = true := by rfl

-- -----------------------------------------------------
-- -           Relational Type Checking Theorems      --
-- -----------------------------------------------------

theorem borrow_local_twice_welltyped : ∃ lenv, typecheck_fun borrow_local_twice lenv :=
  ⟨_, check_fun_dec_sound _ _ borrow_local_twice_check⟩

theorem borrow_local_twice_reverse_welltyped : ∃ lenv, typecheck_fun borrow_local_twice_reverse lenv :=
  ⟨_, check_fun_dec_sound _ _ borrow_local_twice_reverse_check⟩

theorem borrow_local_and_copy_ref_welltyped : ∃ lenv, typecheck_fun borrow_local_and_copy_ref lenv :=
  ⟨_, check_fun_dec_sound _ _ borrow_local_and_copy_ref_check⟩

theorem borrow_local_and_copy_ref_reverse_welltyped : ∃ lenv, typecheck_fun borrow_local_and_copy_ref_reverse lenv :=
  ⟨_, check_fun_dec_sound _ _ borrow_local_and_copy_ref_reverse_check⟩

end LeanMove.Examples.Expressivity.AliasWrites
