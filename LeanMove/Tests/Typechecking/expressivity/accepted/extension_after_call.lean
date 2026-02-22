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
import LeanMove.Tests.Parsing.TestUtils

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

namespace LeanMove.Tests.Expressivity.ExtensionAfterCall

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
  params := [(var_b, .ref (.trecord box_entries) (.paramRef var_b) .siteBorrowMut)]
  returnType := [⟨.trecord point_entries, some true⟩]
  locals := [
    { name := var_tl, type := .ref (.trecord point_entries) (.refid 1) .siteBorrowMut }
  ]
  blocks := [
    { label := "l0"
      body :=
        (letsite s0 ← copy var_b) ;;     -- s0 = copy(b)
        (letsite s1 ← borrowMutField(s0, .trecord box_entries, field_tl)) ;; -- s1 = &mut s0.tl
        (var_tl ::= s1) ;;               -- tl = s1
        (letsite s2 ← copy var_tl) ;;    -- s2 = copy(tl)
        ret [s2]                         -- return s2
    }
  ]
}

-- Function signature for borrow
def borrow_sig : FunSig := ⟨[⟨.trecord box_entries, some true⟩], [⟨.trecord point_entries, some true⟩]⟩

/-
  write(b: &mut Self.Box): &mut Self.Point
  Borrows the top-left point, writes zeros to both coordinates.

  label l0:
      p = Self.borrow(copy(b));
      x = &mut copy(p).Point::x;
      *move(x) = 0;
      y = &mut copy(p).Point::y;
      *move(y) = 0;
      return move(p);
-/
def fn_write : FunDef := {
  params := [(var_b, .ref (.trecord box_entries) (.paramRef var_b) .siteBorrowMut)]
  returnType := [⟨.trecord point_entries, some true⟩]
  locals := [
    { name := var_tl, type := .ref (.trecord point_entries) (.refid 1) .siteBorrowMut },
    { name := var_x, type := .ref .u64 (.refid 2) .siteBorrowMut },
    { name := var_y, type := .ref .u64 (.refid 2) .siteBorrowMut }
  ]
  blocks := [
    { label := "l0"
      body :=
        -- p = Self.borrow(copy(b))
        (letsite s0 ← copy var_b) ;;     -- s0 = copy(b)
        (call([s1], "borrow", [s0])) ;;   -- s1 = borrow(s0)
        (var_tl ::= s1) ;;               -- p = s1
        -- x = &mut copy(p).Point::x
        (letsite s2 ← copy var_tl) ;;    -- s2 = copy(p)
        (letsite s3 ← borrowMutField(s2, .trecord point_entries, field_x)) ;; -- s3 = &mut s2.x
        (var_x ::= s3) ;;                -- x = s3
        -- *move(x) = 0
        (letsite s6 ← move var_x) ;;     -- s6 = move(x)
        (letsite s10 ← #0) ;;            -- s10 = 0 (integer literal)
        (*s6 ::= s10) ;;                 -- *s6 = s10
        -- y = &mut copy(p).Point::y
        (letsite s4 ← copy var_tl) ;;    -- s4 = copy(p)
        (letsite s5 ← borrowMutField(s4, .trecord point_entries, field_y)) ;; -- s5 = &mut s4.y
        (var_y ::= s5) ;;                -- y = s5
        -- *move(y) = 0
        (letsite s7 ← move var_y) ;;     -- s7 = move(y)
        (letsite s11 ← #0) ;;            -- s11 = 0 (integer literal)
        (*s7 ::= s11) ;;                 -- *s7 = s11
        -- return move(p)
        (letsite s8 ← move var_tl) ;;    -- s8 = move(p)
        ret [s8]                         -- return s8
    }
  ]
}

-- -----------------------------------------------------
-- -           Algorithmic Type Checking Tests        --
-- -----------------------------------------------------

-- Initial environments (decidable)
def fn_borrow_lenvDec := mkLabelEnvDec fn_borrow

def borrow_funEnv : FunEnv := AssocMap.insert AssocMap.empty "borrow" borrow_sig

def fn_write_lenvDec := mkLabelEnvDec fn_write borrow_funEnv

-- Test theorems: both functions type check algorithmically
theorem fn_borrow_check : check_fun_dec fn_borrow fn_borrow_lenvDec = true := by rfl

theorem fn_write_check : check_fun_dec fn_write fn_write_lenvDec = true := by rfl

-- -----------------------------------------------------
-- -           Relational Type Checking Theorems      --
-- -----------------------------------------------------

theorem borrow_welltyped : ∃ lenv, typecheck_fun fn_borrow lenv :=
  ⟨_, check_fun_dec_sound _ _ fn_borrow_check⟩

theorem write_welltyped : ∃ lenv, typecheck_fun fn_write lenv :=
  ⟨_, check_fun_dec_sound _ _ fn_write_check⟩

-- -----------------------------------------------------
-- -    Type Checking Parsed MVIR Programs             --
-- -----------------------------------------------------

open LeanMove.Tests.Parsing.TestUtils

private def extensionAfterCallMvir := "
// can write to an extension after a call

//# publish

module 0x2.Tester {

struct Point has copy, drop, store { x: u64, y: u64 }
struct Box has copy, drop, store { tl: Self.Point, br: Self.Point }

borrow(p: &mut Self.Box): &mut Self.Point {
label b0:
    return &mut copy(p).Box::tl;
}

write(b: &mut Self.Box): &mut Self.Point {
    let p: &mut Self.Point;
    let x: &mut u64;
    let y: &mut u64;
label b0:
    p = Self.borrow(copy(b));
    x = &mut copy(p).Point::x;
    *move(x) = 0;
    y = &mut copy(p).Point::y;
    *move(y) = 0;
    return move(p);
}

}
"

private def parsedFuns := (parseAndTranslate extensionAfterCallMvir).toOption.get!

private def parsed_fn_borrow :=
  (findFun parsedFuns "borrow").get!

private def parsed_fn_write :=
  (findFun parsedFuns "write").get!

#guard check_fun_dec parsed_fn_borrow (mkLabelEnvDec parsed_fn_borrow)
#guard check_fun_dec parsed_fn_write (mkLabelEnvDec parsed_fn_write borrow_funEnv)

end LeanMove.Tests.Expressivity.ExtensionAfterCall
