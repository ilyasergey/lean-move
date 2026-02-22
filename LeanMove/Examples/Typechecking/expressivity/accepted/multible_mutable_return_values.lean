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
# Multiple Mutable Return Values

Source: https://github.com/tnowacki/sui/blob/example-tests/external-crates/move/crates/bytecode-verifier-transactional-tests/tests/reference_safety/expressivity/multible_mutable_return_values.mvir

(Note: the original filename has a typo "multible" instead of "multiple")

This module demonstrates that all mutable return values from a function call
should be writable. A function can return multiple mutable references, and
the caller should be able to write through all of them.

struct Point has copy, drop, store { x: u64, y: u64 }

borrow(p: &mut Self.Point): &mut u64 * &mut u64
  Returns mutable refs to both x and y fields.

write(p: &mut Self.Point)
  Calls borrow to get both field refs, then writes 0 to each twice.
-/

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Typing
open AssocMap
open Regex

namespace LeanMove.Examples.Expressivity.MultipleMutableReturnValues

-- Fields for Point struct
def field_x : Field := ⟨"x"⟩
def field_y : Field := ⟨"y"⟩

-- Point { x: u64, y: u64 }
def point_entries : AssocMap Field BasicMoveType :=
  insert (insert empty field_x .u64) field_y .u64

-- Abstract reference for the parameter
def r0 : Aref := .varRef ⟨"p"⟩

-- Variables
def var_p : Var := ⟨"p"⟩
def var_x : Var := ⟨"x"⟩
def var_y : Var := ⟨"y"⟩

-- Sites for borrow function
def s0 : Site := .site 0   -- copy(p) for field x borrow
def s1 : Site := .site 1   -- &mut s0.Point::x
def s2 : Site := .site 2   -- copy(p) for field y borrow
def s3 : Site := .site 3   -- &mut s2.Point::y

/-
  borrow(p: &mut Self.Point): &mut u64 * &mut u64
  Returns mutable references to both x and y fields.

  Original MVIR:
  label b0:
      return &mut copy(p).Point::x, &mut copy(p).Point::y;
-/
def borrow : FunDef := {
  params := [(var_p, .ref (.trecord point_entries) r0 .siteBorrowMut)]
  returnType := [⟨.u64, some true⟩, ⟨.u64, some true⟩]
  locals := []
  blocks := [
    { label := "b0"
      body :=
        (letsite s0 ← copy var_p) ;;
        (letsite s1 ← borrowMutField(s0, .trecord point_entries, field_x)) ;;
        (letsite s2 ← copy var_p) ;;
        (letsite s3 ← borrowMutField(s2, .trecord point_entries, field_y)) ;;
        ret [s1, s3]
    }
  ]
}

-- Sites for write function
-- s0 = copy(p) for call argument
-- s1, s2 = result sites from call (assigned to x, y)
-- s3..s10 = writeRef flattening (4 writes, each needs copy + intLit)
def ws0 : Site := .site 0   -- copy(p)
def ws1 : Site := .site 1   -- call result for x
def ws2 : Site := .site 2   -- call result for y
def ws3 : Site := .site 3   -- copy(x)
def ws4 : Site := .site 4   -- #0
def ws5 : Site := .site 5   -- copy(y)
def ws6 : Site := .site 6   -- #0
def ws7 : Site := .site 7   -- copy(x)
def ws8 : Site := .site 8   -- #0
def ws9 : Site := .site 9   -- copy(y)
def ws10 : Site := .site 10  -- #0

/-
  write(p: &mut Self.Point)
  Calls borrow to get both field refs, then writes 0 to each twice.

  Original MVIR:
  label b0:
      x, y = Self.borrow(copy(p));
      *copy(x) = 0;
      *copy(y) = 0;
      *copy(x) = 0;
      *copy(y) = 0;
      return;
-/
def write : FunDef := {
  params := [(var_p, .ref (.trecord point_entries) r0 .siteBorrowMut)]
  returnType := []
  locals := [
    { name := var_x, type := .ref .u64 (.refid 1) .siteBorrowMut },
    { name := var_y, type := .ref .u64 (.refid 2) .siteBorrowMut }
  ]
  blocks := [
    { label := "b0"
      body :=
        -- x, y = Self.borrow(copy(p))
        (letsite ws0 ← copy var_p) ;;
        (call([ws1, ws2], "borrow", [ws0])) ;;
        (var_x ::= ws1) ;;
        (var_y ::= ws2) ;;
        -- *copy(x) = 0
        (letsite ws3 ← copy var_x) ;;
        (letsite ws4 ← #0) ;;
        (*ws3 ::= ws4) ;;
        -- *copy(y) = 0
        (letsite ws5 ← copy var_y) ;;
        (letsite ws6 ← #0) ;;
        (*ws5 ::= ws6) ;;
        -- *copy(x) = 0 (again)
        (letsite ws7 ← copy var_x) ;;
        (letsite ws8 ← #0) ;;
        (*ws7 ::= ws8) ;;
        -- *copy(y) = 0 (again)
        (letsite ws9 ← copy var_y) ;;
        (letsite ws10 ← #0) ;;
        (*ws9 ::= ws10) ;;
        ret []
    }
  ]
}

-- -----------------------------------------------------
-- -           Algorithmic Type Checking Tests        --
-- -----------------------------------------------------

-- Function signature for borrow: takes &mut Point, returns (&mut u64, &mut u64)
def borrow_sig : FunSig := ⟨[⟨.trecord point_entries, some true⟩], [⟨.u64, some true⟩, ⟨.u64, some true⟩]⟩

-- Initial environments (decidable)
def borrow_initEnvDec : TypeEnvDec := {
  siteEnv := AssocMap.empty
  varEnv := init_fun_varEnv borrow
  pathEnv := init_fun_pathEnvDec borrow.params
  funEnv := AssocMap.empty
}

def borrow_lenvDec : LabelEnvDec :=
  AssocMap.insert AssocMap.empty "b0" borrow_initEnvDec

-- Function environment for write (contains borrow's signature)
def write_funEnv : FunEnv :=
  AssocMap.insert AssocMap.empty "borrow" borrow_sig

def write_initEnvDec : TypeEnvDec := {
  siteEnv := AssocMap.empty
  varEnv := init_fun_varEnv write
  pathEnv := init_fun_pathEnvDec write.params
  funEnv := write_funEnv
}

def write_lenvDec : LabelEnvDec :=
  AssocMap.insert AssocMap.empty "b0" write_initEnvDec

-- Theorems: both functions type check algorithmically
theorem borrow_check : check_fun_dec borrow borrow_lenvDec = true := by rfl
set_option maxRecDepth 4096 in
theorem write_check : check_fun_dec write write_lenvDec = true := by rfl

-- -----------------------------------------------------
-- -           Relational Type Checking Theorems      --
-- -----------------------------------------------------

theorem borrow_welltyped : ∃ lenv, typecheck_fun borrow lenv :=
  ⟨_, check_fun_dec_sound _ _ borrow_check⟩

theorem write_welltyped : ∃ lenv, typecheck_fun write lenv :=
  ⟨_, check_fun_dec_sound _ _ write_check⟩

end LeanMove.Examples.Expressivity.MultipleMutableReturnValues
