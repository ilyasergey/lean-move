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
import LeanMove.Checker.Algorithmic.TypeCheckingAlgorithmic
import LeanMove.Checker.Algorithmic.AlgorithmicTypingSoundness
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
open LeanMove.Checker
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

-- Initial environment for borrow_local_twice
def borrow_local_twice_initEnv : TypeEnv := {
  siteEnv := AssocMap.empty
  varEnv := init_fun_varEnv borrow_local_twice
  pathEnv := PathEnv.init
  funEnv := AssocMap.empty
}

-- LabelEnv for borrow_local_twice: maps "l0" to initial environment
def borrow_local_twice_lenv : LabelEnv :=
  AssocMap.insert AssocMap.empty "l0" borrow_local_twice_initEnv

-- Debug: test algorithmic type checking
#eval check_fun borrow_local_twice borrow_local_twice_lenv

-- Debug: step-by-step type checking of l0 body
-- Step 1: intLit 0
#eval (check_stmt borrow_local_twice_lenv borrow_local_twice_initEnv
  ((letsite s0 ← #0) ;; Stmt.skip)
  (.basic .tunit)).isSome
-- Step 2: + assign a
#eval (check_stmt borrow_local_twice_lenv borrow_local_twice_initEnv
  ((letsite s0 ← #0) ;; (var_a ::= s0) ;; Stmt.skip)
  (.basic .tunit)).isSome
-- Step 3: + borrow mut a
#eval (check_stmt borrow_local_twice_lenv borrow_local_twice_initEnv
  ((letsite s0 ← #0) ;; (var_a ::= s0) ;;
   (letsite s1 ← &mut var_a) ;; Stmt.skip)
  (.basic .tunit)).isSome
-- Step 4: + assign x
#eval (check_stmt borrow_local_twice_lenv borrow_local_twice_initEnv
  ((letsite s0 ← #0) ;; (var_a ::= s0) ;;
   (letsite s1 ← &mut var_a) ;; (var_x ::= s1) ;; Stmt.skip)
  (.basic .tunit)).isSome
-- Step 5: + second borrow mut a
#eval (check_stmt borrow_local_twice_lenv borrow_local_twice_initEnv
  ((letsite s0 ← #0) ;; (var_a ::= s0) ;;
   (letsite s1 ← &mut var_a) ;; (var_x ::= s1) ;;
   (letsite s2 ← &mut var_a) ;; Stmt.skip)
  (.basic .tunit)).isSome
-- Step 6: + assign y
#eval (check_stmt borrow_local_twice_lenv borrow_local_twice_initEnv
  ((letsite s0 ← #0) ;; (var_a ::= s0) ;;
   (letsite s1 ← &mut var_a) ;; (var_x ::= s1) ;;
   (letsite s2 ← &mut var_a) ;; (var_y ::= s2) ;; Stmt.skip)
  (.basic .tunit)).isSome
-- Step 7: + move x
#eval (check_stmt borrow_local_twice_lenv borrow_local_twice_initEnv
  ((letsite s0 ← #0) ;; (var_a ::= s0) ;;
   (letsite s1 ← &mut var_a) ;; (var_x ::= s1) ;;
   (letsite s2 ← &mut var_a) ;; (var_y ::= s2) ;;
   (letsite s3 ← move var_x) ;; Stmt.skip)
  (.basic .tunit)).isSome
-- Step 8: + intLit for first write
#eval (check_stmt borrow_local_twice_lenv borrow_local_twice_initEnv
  ((letsite s0 ← #0) ;; (var_a ::= s0) ;;
   (letsite s1 ← &mut var_a) ;; (var_x ::= s1) ;;
   (letsite s2 ← &mut var_a) ;; (var_y ::= s2) ;;
   (letsite s3 ← move var_x) ;; (letsite s4 ← #0) ;; Stmt.skip)
  (.basic .tunit)).isSome
-- Step 9: + writeRef *s3 = s4
#eval (check_stmt borrow_local_twice_lenv borrow_local_twice_initEnv
  ((letsite s0 ← #0) ;; (var_a ::= s0) ;;
   (letsite s1 ← &mut var_a) ;; (var_x ::= s1) ;;
   (letsite s2 ← &mut var_a) ;; (var_y ::= s2) ;;
   (letsite s3 ← move var_x) ;; (letsite s4 ← #0) ;;
   Stmt.writeRef s3 s4 ;; Stmt.skip)
  (.basic .tunit)).isSome

-- Debug: remaining steps - move y, intLit, second writeRef, return
-- Step 10: + move y + intLit + second writeRef
#eval (check_stmt borrow_local_twice_lenv borrow_local_twice_initEnv
  ((letsite s0 ← #0) ;; (var_a ::= s0) ;;
   (letsite s1 ← &mut var_a) ;; (var_x ::= s1) ;;
   (letsite s2 ← &mut var_a) ;; (var_y ::= s2) ;;
   (letsite s3 ← move var_x) ;; (letsite s4 ← #0) ;;
   Stmt.writeRef s3 s4 ;;
   (letsite s5 ← move var_y) ;; (letsite s6 ← #0) ;;
   Stmt.writeRef s5 s6 ;; Stmt.skip)
  (.basic .tunit)).isSome
-- Step 11: full body with ret
#eval (check_stmt borrow_local_twice_lenv borrow_local_twice_initEnv
  ((letsite s0 ← #0) ;; (var_a ::= s0) ;;
   (letsite s1 ← &mut var_a) ;; (var_x ::= s1) ;;
   (letsite s2 ← &mut var_a) ;; (var_y ::= s2) ;;
   (letsite s3 ← move var_x) ;; (letsite s4 ← #0) ;;
   Stmt.writeRef s3 s4 ;;
   (letsite s5 ← move var_y) ;; (letsite s6 ← #0) ;;
   Stmt.writeRef s5 s6 ;; Stmt.ret [])
  (.basic .tunit)).isSome

-- Debug: equiv_bool check (what check_fun does internally)
#eval TypeEnv.equiv_bool borrow_local_twice_initEnv
  { varEnv := init_fun_varEnv borrow_local_twice, siteEnv := AssocMap.empty,
    pathEnv := PathEnv.init, funEnv := AssocMap.empty }

-- Test theorem: borrow_local_twice type checks algorithmically
theorem borrow_local_twice_check :
  check_fun borrow_local_twice
  borrow_local_twice_lenv := by rfl

-- Initial environment for borrow_local_twice_reverse
def borrow_local_twice_reverse_initEnv : TypeEnv := {
  siteEnv := AssocMap.empty
  varEnv := init_fun_varEnv borrow_local_twice_reverse
  pathEnv := PathEnv.init
  funEnv := AssocMap.empty
}

-- LabelEnv for borrow_local_twice_reverse: maps "l0" to initial environment
def borrow_local_twice_reverse_lenv : LabelEnv :=
  AssocMap.insert AssocMap.empty "l0" borrow_local_twice_reverse_initEnv

-- Debug: test algorithmic type checking
#eval check_fun borrow_local_twice_reverse borrow_local_twice_reverse_lenv

-- Test theorem: borrow_local_twice_reverse type checks algorithmically
theorem borrow_local_twice_reverse_check :
  check_fun borrow_local_twice_reverse
  borrow_local_twice_reverse_lenv := by rfl

-- Initial environment for borrow_local_and_copy_ref
def borrow_local_and_copy_ref_initEnv : TypeEnv := {
  siteEnv := AssocMap.empty
  varEnv := init_fun_varEnv borrow_local_and_copy_ref
  pathEnv := PathEnv.init
  funEnv := AssocMap.empty
}

-- LabelEnv for borrow_local_and_copy_ref: maps "l0" to initial environment
def borrow_local_and_copy_ref_lenv : LabelEnv :=
  AssocMap.insert AssocMap.empty "l0" borrow_local_and_copy_ref_initEnv

-- Debug: test algorithmic type checking
#eval check_fun borrow_local_and_copy_ref borrow_local_and_copy_ref_lenv

-- Test theorem: borrow_local_and_copy_ref type checks algorithmically
theorem borrow_local_and_copy_ref_check :
  check_fun borrow_local_and_copy_ref
  borrow_local_and_copy_ref_lenv := by rfl

-- Initial environment for borrow_local_and_copy_ref_reverse
def borrow_local_and_copy_ref_reverse_initEnv : TypeEnv := {
  siteEnv := AssocMap.empty
  varEnv := init_fun_varEnv borrow_local_and_copy_ref_reverse
  pathEnv := PathEnv.init
  funEnv := AssocMap.empty
}

-- LabelEnv for borrow_local_and_copy_ref_reverse: maps "l0" to initial environment
def borrow_local_and_copy_ref_reverse_lenv : LabelEnv :=
  AssocMap.insert AssocMap.empty "l0" borrow_local_and_copy_ref_reverse_initEnv

-- Debug: test algorithmic type checking
#eval check_fun borrow_local_and_copy_ref_reverse borrow_local_and_copy_ref_reverse_lenv

-- Test theorem: borrow_local_and_copy_ref_reverse type checks algorithmically
theorem borrow_local_and_copy_ref_reverse_check :
 check_fun borrow_local_and_copy_ref_reverse
 borrow_local_and_copy_ref_reverse_lenv := by rfl

-- -----------------------------------------------------
-- -           Relational Type Checking Theorems      --
-- -----------------------------------------------------

-- Helper: init_fun_varEnv for these functions has fresh refs
private lemma borrow_local_twice_varEnv_fresh :
    VarEnv.RefsAreFresh (init_fun_varEnv borrow_local_twice) := by
  unfold init_fun_varEnv add_locals_to_varEnv init_varEnv_from_params
  simp only [borrow_local_twice, List.foldl]
  apply VarEnv.insert_refs_are_fresh
  · apply VarEnv.insert_refs_are_fresh
    · apply VarEnv.insert_refs_are_fresh
      · exact VarEnv.empty_refs_are_fresh
      · trivial
    · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩

-- Helper: all envs in the single-entry lenv are well-formed
private lemma borrow_local_twice_lenv_wf :
    ∀ l env, lookup borrow_local_twice_lenv l = some env → TypeEnv.WellFormed env := by
  intro l env hlookup
  simp only [borrow_local_twice_lenv, borrow_local_twice_initEnv,
             AssocMap.insert, AssocMap.empty, AssocMap.lookup,
             List.filter, List.lookup] at hlookup
  split at hlookup
  · injection hlookup with heq; subst heq
    exact TypeEnv.init_wellformed _ _ borrow_local_twice_varEnv_fresh
  · exact absurd hlookup (by simp)

-- Theorems: all functions are well-typed (via soundness of algorithmic checker)
theorem borrow_local_twice_welltyped : ∃ lenv, typecheck_fun borrow_local_twice lenv :=
  ⟨_, check_fun_sound _ _ borrow_local_twice_lenv_wf borrow_local_twice_check⟩

theorem borrow_local_twice_reverse_welltyped : ∃ lenv, typecheck_fun borrow_local_twice_reverse lenv :=
  ⟨_, check_fun_sound _ _ (fun l env hlookup => by
    simp only [borrow_local_twice_reverse_lenv, borrow_local_twice_reverse_initEnv,
               AssocMap.insert, AssocMap.empty, AssocMap.lookup,
               List.filter, List.lookup] at hlookup
    split at hlookup
    · injection hlookup with heq; subst heq
      exact TypeEnv.init_wellformed _ _ (by
        unfold init_fun_varEnv add_locals_to_varEnv init_varEnv_from_params
        simp only [borrow_local_twice_reverse, List.foldl]
        apply VarEnv.insert_refs_are_fresh
        · apply VarEnv.insert_refs_are_fresh
          · apply VarEnv.insert_refs_are_fresh
            · exact VarEnv.empty_refs_are_fresh
            · trivial
          · exact ⟨1, rfl⟩
        · exact ⟨2, rfl⟩)
    · exact absurd hlookup (by simp)) borrow_local_twice_reverse_check⟩

theorem borrow_local_and_copy_ref_welltyped : ∃ lenv, typecheck_fun borrow_local_and_copy_ref lenv :=
  ⟨_, check_fun_sound _ _ (fun l env hlookup => by
    simp only [borrow_local_and_copy_ref_lenv, borrow_local_and_copy_ref_initEnv,
               AssocMap.insert, AssocMap.empty, AssocMap.lookup,
               List.filter, List.lookup] at hlookup
    split at hlookup
    · injection hlookup with heq; subst heq
      exact TypeEnv.init_wellformed _ _ (by
        unfold init_fun_varEnv add_locals_to_varEnv init_varEnv_from_params
        simp only [borrow_local_and_copy_ref, List.foldl]
        apply VarEnv.insert_refs_are_fresh
        · apply VarEnv.insert_refs_are_fresh
          · apply VarEnv.insert_refs_are_fresh
            · exact VarEnv.empty_refs_are_fresh
            · trivial
          · exact ⟨1, rfl⟩
        · exact ⟨2, rfl⟩)
    · exact absurd hlookup (by simp)) borrow_local_and_copy_ref_check⟩

theorem borrow_local_and_copy_ref_reverse_welltyped : ∃ lenv, typecheck_fun borrow_local_and_copy_ref_reverse lenv :=
  ⟨_, check_fun_sound _ _ (fun l env hlookup => by
    simp only [borrow_local_and_copy_ref_reverse_lenv, borrow_local_and_copy_ref_reverse_initEnv,
               AssocMap.insert, AssocMap.empty, AssocMap.lookup,
               List.filter, List.lookup] at hlookup
    split at hlookup
    · injection hlookup with heq; subst heq
      exact TypeEnv.init_wellformed _ _ (by
        unfold init_fun_varEnv add_locals_to_varEnv init_varEnv_from_params
        simp only [borrow_local_and_copy_ref_reverse, List.foldl]
        apply VarEnv.insert_refs_are_fresh
        · apply VarEnv.insert_refs_are_fresh
          · apply VarEnv.insert_refs_are_fresh
            · exact VarEnv.empty_refs_are_fresh
            · trivial
          · exact ⟨1, rfl⟩
        · exact ⟨_, rfl⟩)
    · exact absurd hlookup (by simp)) borrow_local_and_copy_ref_reverse_check⟩

end LeanMove.Examples.Expressivity.AliasWrites
