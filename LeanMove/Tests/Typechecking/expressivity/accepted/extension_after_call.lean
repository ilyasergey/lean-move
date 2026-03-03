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
import LeanMove.Lang.MoveIR.PrettyPrint
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

-- Hand-written FunDefs moved to Tests/Parsing/Test_extension_after_call.lean

-- Function signature for borrow
def borrow_sig : FunSig := ⟨[⟨.trecord box_entries, some true⟩], [⟨.trecord point_entries, some true⟩]⟩

-- -----------------------------------------------------
-- -    Parsed MVIR Programs                           --
-- -----------------------------------------------------

open LeanMove.Tests.Parsing.TestUtils

private def extensionAfterCallMvir :=
  include_str "extension_after_call.mvir"

private def parsedFuns := (parseAndTranslate extensionAfterCallMvir).toOption.get!

def parsed_fn_borrow :=
  (findFun parsedFuns "borrow").get!

def parsed_fn_write :=
  (findFun parsedFuns "write").get!

-- Uncomment to pretty-print the parsed FunDefs:
-- #eval IO.println (ppFunDef "borrow" parsed_fn_borrow)
-- #eval IO.println (ppFunDef "write" parsed_fn_write)

-- -----------------------------------------------------
-- -           Algorithmic Type Checking Tests        --
-- -----------------------------------------------------

-- Initial environments (decidable)
def fn_borrow_lenvDec := mkLabelEnvDec parsed_fn_borrow

def borrow_funEnv : FunEnv := AssocMap.insert AssocMap.empty "Tester.borrow" borrow_sig

def fn_write_lenvDec := mkLabelEnvDec parsed_fn_write borrow_funEnv

-- Test theorems: both functions type check algorithmically
theorem fn_borrow_check : check_fun_dec parsed_fn_borrow fn_borrow_lenvDec = true := by native_decide

theorem fn_write_check : check_fun_dec parsed_fn_write fn_write_lenvDec = true := by native_decide

-- -----------------------------------------------------
-- -           Relational Type Checking Theorems      --
-- -----------------------------------------------------

theorem borrow_welltyped : ∃ lenv, typecheck_fun parsed_fn_borrow lenv :=
  ⟨_, check_fun_dec_sound _ _ fn_borrow_check⟩

theorem write_welltyped : ∃ lenv, typecheck_fun parsed_fn_write lenv :=
  ⟨_, check_fun_dec_sound _ _ fn_write_check⟩

end LeanMove.Tests.Expressivity.ExtensionAfterCall
