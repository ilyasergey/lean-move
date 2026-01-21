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
open LeanMove.Checker
open AssocMap
open Regex

namespace LeanMove.Examples.Expressivity.AliasWrites

-- Variables
def var_a : Var := ⟨"a"⟩
def var_x : Var := ⟨"x"⟩
def var_y : Var := ⟨"y"⟩

-- Sites
def s0 : Site := .site 0   -- constant 0
def s1 : Site := .site 1   -- &mut a
def s2 : Site := .site 2   -- &mut a or copy(x)
def s3 : Site := .site 3   -- copy for write
def s4 : Site := .site 4   -- constant for write
def s5 : Site := .site 5   -- copy for write
def s6 : Site := .site 6   -- constant for write

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
    *copy(x) = 0;
    *copy(y) = 0;
    return;
  }
-/
def borrow_local_twice : FunDef := {
  params := []
  returnType := .basic .tunit
  locals := [
    { name := var_a, type := .basic .tint },
    { name := var_x, type := .ref .tint (.varRef var_a) .siteBorrowMut },
    { name := var_y, type := .ref .tint (.varRef var_a) .siteBorrowMut }
  ]
  blocks := [
    { label := "l0"
      body :=
        (var_a ::= s0) ;;               -- a = 0
        (letsite s1 ← &mut var_a) ;;    -- s1 = &mut a
        (var_x ::= s1) ;;               -- x = s1
        (letsite s2 ← &mut var_a) ;;    -- s2 = &mut a
        (var_y ::= s2) ;;               -- y = s2
        (letsite s3 ← copy var_x) ;;    -- s3 = copy(x)
        Stmt.writeRef s3 s4 ;;          -- *s3 = 0
        (letsite s5 ← copy var_y) ;;    -- s5 = copy(y)
        Stmt.writeRef s5 s6 ;;          -- *s5 = 0
        Stmt.ret []
    }
  ]
}

/-
  Module 2: borrow_local_twice_reverse
  Same as above but writes in reverse order (y first, then x).
-/
def borrow_local_twice_reverse : FunDef := {
  params := []
  returnType := .basic .tunit
  locals := [
    { name := var_a, type := .basic .tint },
    { name := var_x, type := .ref .tint (.varRef var_a) .siteBorrowMut },
    { name := var_y, type := .ref .tint (.varRef var_a) .siteBorrowMut }
  ]
  blocks := [
    { label := "l0"
      body :=
        (var_a ::= s0) ;;               -- a = 0
        (letsite s1 ← &mut var_a) ;;    -- s1 = &mut a
        (var_x ::= s1) ;;               -- x = s1
        (letsite s2 ← &mut var_a) ;;    -- s2 = &mut a
        (var_y ::= s2) ;;               -- y = s2
        (letsite s3 ← copy var_y) ;;    -- s3 = copy(y) -- reversed
        Stmt.writeRef s3 s4 ;;          -- *s3 = 0
        (letsite s5 ← copy var_x) ;;    -- s5 = copy(x) -- reversed
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
    *copy(x) = 0;
    *copy(y) = 0;
    return;
  }
-/
def borrow_local_and_copy_ref : FunDef := {
  params := []
  returnType := .basic .tunit
  locals := [
    { name := var_a, type := .basic .tint },
    { name := var_x, type := .ref .tint (.varRef var_a) .siteBorrowMut },
    { name := var_y, type := .ref .tint (.varRef var_a) .siteBorrowMut }
  ]
  blocks := [
    { label := "l0"
      body :=
        (var_a ::= s0) ;;               -- a = 0
        (letsite s1 ← &mut var_a) ;;    -- s1 = &mut a
        (var_x ::= s1) ;;               -- x = s1
        (letsite s2 ← copy var_x) ;;    -- s2 = copy(x)
        (var_y ::= s2) ;;               -- y = s2
        (letsite s3 ← copy var_x) ;;    -- s3 = copy(x)
        Stmt.writeRef s3 s4 ;;          -- *s3 = 0
        (letsite s5 ← copy var_y) ;;    -- s5 = copy(y)
        Stmt.writeRef s5 s6 ;;          -- *s5 = 0
        Stmt.ret []
    }
  ]
}

/-
  Module 4: borrow_local_and_copy_ref_reverse
  Same as above but writes in reverse order.
-/
def borrow_local_and_copy_ref_reverse : FunDef := {
  params := []
  returnType := .basic .tunit
  locals := [
    { name := var_a, type := .basic .tint },
    { name := var_x, type := .ref .tint (.varRef var_a) .siteBorrowMut },
    { name := var_y, type := .ref .tint (.varRef var_a) .siteBorrowMut }
  ]
  blocks := [
    { label := "l0"
      body :=
        (var_a ::= s0) ;;               -- a = 0
        (letsite s1 ← &mut var_a) ;;    -- s1 = &mut a
        (var_x ::= s1) ;;               -- x = s1
        (letsite s2 ← copy var_x) ;;    -- s2 = copy(x)
        (var_y ::= s2) ;;               -- y = s2
        (letsite s3 ← copy var_y) ;;    -- s3 = copy(y) -- reversed
        Stmt.writeRef s3 s4 ;;          -- *s3 = 0
        (letsite s5 ← copy var_x) ;;    -- s5 = copy(x) -- reversed
        Stmt.writeRef s5 s6 ;;          -- *s5 = 0
        Stmt.ret []
    }
  ]
}

-- Theorems: all functions are well-typed
theorem borrow_local_twice_welltyped : ∃ lenv, typecheck_fun borrow_local_twice lenv := by
  sorry

theorem borrow_local_twice_reverse_welltyped : ∃ lenv, typecheck_fun borrow_local_twice_reverse lenv := by
  sorry

theorem borrow_local_and_copy_ref_welltyped : ∃ lenv, typecheck_fun borrow_local_and_copy_ref lenv := by
  sorry

theorem borrow_local_and_copy_ref_reverse_welltyped : ∃ lenv, typecheck_fun borrow_local_and_copy_ref_reverse lenv := by
  sorry

end LeanMove.Examples.Expressivity.AliasWrites
