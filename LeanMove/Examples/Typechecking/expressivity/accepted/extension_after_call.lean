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
import LeanMove.Typing.Algorithmic.TypeCheckingAlgorithmic
import LeanMove.Typing.Algorithmic.AlgorithmicTypingSoundness
import LeanMove.Lang.Macros

/-!
# Extension After Call

Source: https://github.com/tnowacki/sui/blob/example-tests/external-crates/move/crates/bytecode-verifier-transactional-tests/tests/reference_safety/expressivity/extension_after_call.mvir

This module demonstrates borrowing and writing to nested struct fields.

Structs:
- Point { x: u64, y: u64 } - a point with copy, drop, store
- Box { tl: Point, br: Point } - a box with top-left and bottom-right points

Functions:
- borrow(b: &mut Box): &mut Point - returns a mutable ref to the top-left point
- write(b: &mut Box): &mut Point - borrows tl, writes zeros to both coords, returns ref
-/

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Typing
open AssocMap
open Regex

namespace LeanMove.Examples.Expressivity.ExtensionAfterCall

-- Fields
def field_x : Field := ⟨"x"⟩
def field_y : Field := ⟨"y"⟩
def field_tl : Field := ⟨"tl"⟩
def field_br : Field := ⟨"br"⟩

-- Point { x: u64, y: u64 }
def point_entries : AssocMap Field BasicMoveType :=
  insert (insert empty field_x .u64) field_y .u64

-- Box { tl: Point, br: Point }
def box_entries : AssocMap Field BasicMoveType :=
  insert (insert empty field_tl (.trecord point_entries)) field_br (.trecord point_entries)

-- Variables
def var_b : Var := ⟨"b"⟩
def var_tl : Var := ⟨"tl"⟩
def var_x : Var := ⟨"x"⟩
def var_y : Var := ⟨"y"⟩

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
def s9 : Site := .site 9
def s10 : Site := .site 10 -- integer literal 0 for *x write
def s11 : Site := .site 11 -- integer literal 0 for *y write

/-
  borrow(b: &mut Self.Box): &mut Self.Point
  Returns a mutable reference to the top-left point.

  label l0:
      tl = &mut copy(b).Box::tl;
      return copy(tl);
-/
def fn_borrow : FunDef := {
  params := [(var_b, .ref (.trecord box_entries) (.refid 0) .siteBorrowMut)]
  returnType := .ref (.trecord point_entries) (.refid 4) .siteBorrowMut
  locals := [
    { name := var_tl, type := .ref (.trecord point_entries) (.refid 1) .siteBorrowMut }
  ]
  blocks := [
    { label := "l0"
      body :=
        (letsite s0 ← copy var_b) ;;     -- s0 = copy(b)
        Stmt.letBind s1 (Expr.borrowMutField s0 (.trecord box_entries) field_tl) ;; -- s1 = &mut s0.tl
        (var_tl ::= s1) ;;               -- tl = s1
        (letsite s2 ← copy var_tl) ;;    -- s2 = copy(tl)
        Stmt.ret [s2]                    -- return s2
    }
  ]
}

/-
  write(b: &mut Self.Box): &mut Self.Point
  Borrows the top-left point, writes zeros to both coordinates.

  Original MVIR:
  p = Self.borrow(copy(b));
  x = &mut copy(p).Point::x;
  *move(x) = 0;
  y = &mut copy(p).Point::y;
  *move(y) = 0;
  return move(p);

  We inline the borrow call.
-/
def fn_write : FunDef := {
  params := [(var_b, .ref (.trecord box_entries) (.refid 0) .siteBorrowMut)]
  returnType := .ref (.trecord point_entries) (.refid 4) .siteBorrowMut
  locals := [
    { name := var_tl, type := .ref (.trecord point_entries) (.refid 1) .siteBorrowMut },
    { name := var_x, type := .ref .u64 (.refid 2) .siteBorrowMut },
    { name := var_y, type := .ref .u64 (.refid 2) .siteBorrowMut }
  ]
  blocks := [
    { label := "l0"
      body :=
        -- p = Self.borrow(copy(b)) - inlined as: p = &mut copy(b).Box::tl
        (letsite s0 ← copy var_b) ;;     -- s0 = copy(b)
        Stmt.letBind s1 (Expr.borrowMutField s0 (.trecord box_entries) field_tl) ;; -- s1 = &mut s0.tl
        (var_tl ::= s1) ;;               -- tl (p) = s1
        -- x = &mut copy(p).Point::x
        (letsite s2 ← copy var_tl) ;;    -- s2 = copy(p)
        Stmt.letBind s3 (Expr.borrowMutField s2 (.trecord point_entries) field_x) ;; -- s3 = &mut s2.x
        (var_x ::= s3) ;;                -- x = s3
        -- *move(x) = 0
        (letsite s6 ← move var_x) ;;     -- s6 = move(x)
        (letsite s10 ← #0) ;;            -- s10 = 0 (integer literal)
        Stmt.writeRef s6 s10 ;;          -- *s6 = s10
        -- y = &mut copy(p).Point::y
        (letsite s4 ← copy var_tl) ;;    -- s4 = copy(p)
        Stmt.letBind s5 (Expr.borrowMutField s4 (.trecord point_entries) field_y) ;; -- s5 = &mut s4.y
        (var_y ::= s5) ;;                -- y = s5
        -- *move(y) = 0
        (letsite s7 ← move var_y) ;;     -- s7 = move(y)
        (letsite s11 ← #0) ;;            -- s11 = 0 (integer literal)
        Stmt.writeRef s7 s11 ;;          -- *s7 = s11
        -- return move(p)
        (letsite s8 ← move var_tl) ;;    -- s8 = move(tl/p)
        Stmt.ret [s8]                    -- return s8
    }
  ]
}

-- -----------------------------------------------------
-- -           Algorithmic Type Checking Tests        --
-- -----------------------------------------------------

-- Initial environments
def fn_borrow_initEnv : TypeEnv := {
  siteEnv := AssocMap.empty
  varEnv := init_fun_varEnv fn_borrow
  pathEnv := PathEnv.init
  funEnv := AssocMap.empty
}

def fn_borrow_lenv : LabelEnv :=
  AssocMap.insert AssocMap.empty "l0" fn_borrow_initEnv

def fn_write_initEnv : TypeEnv := {
  siteEnv := AssocMap.empty
  varEnv := init_fun_varEnv fn_write
  pathEnv := PathEnv.init
  funEnv := AssocMap.empty
}

def fn_write_lenv : LabelEnv :=
  AssocMap.insert AssocMap.empty "l0" fn_write_initEnv

-- Debug: test algorithmic type checking
#eval check_fun fn_borrow fn_borrow_lenv
#eval check_fun fn_write fn_write_lenv

-- Test theorems: both functions type check algorithmically
theorem fn_borrow_check : check_fun fn_borrow fn_borrow_lenv = true := by rfl
theorem fn_write_check : check_fun fn_write fn_write_lenv = true := by rfl

-- -----------------------------------------------------
-- -           Relational Type Checking Theorems      --
-- -----------------------------------------------------

-- Helper: init_fun_varEnv for fn_borrow has fresh refs
private lemma fn_borrow_varEnv_fresh :
    VarEnv.RefsAreFresh (init_fun_varEnv fn_borrow) := by
  unfold init_fun_varEnv add_locals_to_varEnv init_varEnv_from_params
  simp only [fn_borrow, List.foldl]
  apply VarEnv.insert_refs_are_fresh
  · apply VarEnv.insert_refs_are_fresh
    · exact VarEnv.empty_refs_are_fresh
    · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩

private lemma fn_borrow_lenv_wf :
    ∀ l env, lookup fn_borrow_lenv l = some env → TypeEnv.WellFormed env := by
  intro l env hlookup
  simp only [fn_borrow_lenv, fn_borrow_initEnv,
             AssocMap.insert, AssocMap.empty, AssocMap.lookup,
             List.filter, List.lookup] at hlookup
  split at hlookup
  · injection hlookup with heq; subst heq
    exact TypeEnv.init_wellformed _ _ fn_borrow_varEnv_fresh
  · exact absurd hlookup (by simp)

theorem borrow_welltyped : ∃ lenv, typecheck_fun fn_borrow lenv :=
  ⟨_, check_fun_sound _ _ fn_borrow_lenv_wf fn_borrow_check⟩

-- Helper: init_fun_varEnv for fn_write has fresh refs
private lemma fn_write_varEnv_fresh :
    VarEnv.RefsAreFresh (init_fun_varEnv fn_write) := by
  unfold init_fun_varEnv add_locals_to_varEnv init_varEnv_from_params
  simp only [fn_write, List.foldl]
  apply VarEnv.insert_refs_are_fresh
  · apply VarEnv.insert_refs_are_fresh
    · apply VarEnv.insert_refs_are_fresh
      · apply VarEnv.insert_refs_are_fresh
        · exact VarEnv.empty_refs_are_fresh
        · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
  · exact ⟨2, rfl⟩

private lemma fn_write_lenv_wf :
    ∀ l env, lookup fn_write_lenv l = some env → TypeEnv.WellFormed env := by
  intro l env hlookup
  simp only [fn_write_lenv, fn_write_initEnv,
             AssocMap.insert, AssocMap.empty, AssocMap.lookup,
             List.filter, List.lookup] at hlookup
  split at hlookup
  · injection hlookup with heq; subst heq
    exact TypeEnv.init_wellformed _ _ fn_write_varEnv_fresh
  · exact absurd hlookup (by simp)

theorem write_welltyped : ∃ lenv, typecheck_fun fn_write lenv :=
  ⟨_, check_fun_sound _ _ fn_write_lenv_wf fn_write_check⟩

end LeanMove.Examples.Expressivity.ExtensionAfterCall
