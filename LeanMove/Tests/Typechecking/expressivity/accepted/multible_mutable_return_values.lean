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

namespace LeanMove.Tests.Expressivity.MultipleMutableReturnValues

-- Fields for Point struct
def field_x : Field := ⟨"x"⟩
def field_y : Field := ⟨"y"⟩

-- Point { x: u64, y: u64 }
def point_entries : AssocMap Field BasicMoveType :=
  insert (insert empty field_x .u64) field_y .u64

-- Abstract reference for the parameter
def r0 : Aref := .paramRef ⟨"p"⟩

-- Variables
def var_p : Var := ⟨"p"⟩
def var_x : Var := ⟨"x"⟩
def var_y : Var := ⟨"y"⟩

-- -----------------------------------------------------
-- -    Parsed MVIR Programs                           --
-- -----------------------------------------------------

open LeanMove.Tests.Parsing.TestUtils

private def multibleMutableReturnValuesMvir :=
  include_str "multible_mutable_return_values.mvir"

private def parsedFuns := (parseAndTranslate multibleMutableReturnValuesMvir).toOption.get!

def parsed_borrow :=
  (findFunInModule parsedFuns "Tester" "borrow").get!

def parsed_write :=
  (findFunInModule parsedFuns "Tester" "write").get!

-- Uncomment to pretty-print the parsed FunDefs:
-- #eval IO.println (ppFunDef "borrow" parsed_borrow)
-- #eval IO.println (ppFunDef "write" parsed_write)

-- -----------------------------------------------------
-- -           Algorithmic Type Checking Tests        --
-- -----------------------------------------------------

-- Function signature for borrow: takes &mut Point, returns (&mut u64, &mut u64)
def borrow_sig : FunSig := ⟨[⟨.trecord point_entries, some true⟩], [⟨.u64, some true⟩, ⟨.u64, some true⟩]⟩

-- Initial environments (decidable)
def borrow_lenvDec := mkLabelEnvDec parsed_borrow

-- Function environment for write (contains borrow's signature)
def write_funEnv : FunEnv :=
  AssocMap.insert AssocMap.empty "Tester.borrow" borrow_sig

def write_lenvDec := mkLabelEnvDec parsed_write write_funEnv

-- Theorems: both functions type check algorithmically
theorem borrow_check : check_fun_dec parsed_borrow borrow_lenvDec = true := by native_decide
set_option maxRecDepth 4096 in
theorem write_check : check_fun_dec parsed_write write_lenvDec = true := by native_decide

-- -----------------------------------------------------
-- -           Relational Type Checking Theorems      --
-- -----------------------------------------------------

theorem borrow_welltyped : ∃ lenv, typecheck_fun parsed_borrow lenv AssocMap.empty :=
  ⟨_, check_fun_dec_sound _ _ _ borrow_check⟩

theorem write_welltyped : ∃ lenv, typecheck_fun parsed_write lenv AssocMap.empty :=
  ⟨_, check_fun_dec_sound _ _ _ write_check⟩

end LeanMove.Tests.Expressivity.MultipleMutableReturnValues
