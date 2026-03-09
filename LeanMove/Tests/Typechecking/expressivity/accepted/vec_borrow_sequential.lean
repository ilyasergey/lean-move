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
# Vector Element Borrow Tests

Tests for vector element borrowing operations:
1. vec_imm_borrow_read: borrow element immutably, read through it
2. vec_multi_imm_borrow: multiple simultaneous immutable element borrows (safe)
3. vec_mut_borrow_write: mutable element borrow, write through it

All functions are ACCEPTED by the type checker.
-/

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Typing
open AssocMap
open Regex

namespace LeanMove.Tests.Expressivity.VecBorrowSequential

open LeanMove.Tests.Parsing.TestUtils

private def vecBorrowSeqMvir :=
  include_str "../../../MVIR/vec_borrow_sequential.mvir"

#guard (parseAndTranslate vecBorrowSeqMvir).isOk

private def parsedFuns := (parseAndTranslate vecBorrowSeqMvir).toOption.get!

def parsed_vec_imm_borrow_read :=
  (findFunInModule parsedFuns "vec_imm_borrow_read" "t").get!

def parsed_vec_multi_imm_borrow :=
  (findFunInModule parsedFuns "vec_multi_imm_borrow" "t").get!

def parsed_vec_mut_borrow_write :=
  (findFunInModule parsedFuns "vec_mut_borrow_write" "t").get!

-- Algorithmic Type Checking (Decidable)
def vec_imm_borrow_read_lenvDec := mkLabelEnvDec parsed_vec_imm_borrow_read
def vec_multi_imm_borrow_lenvDec := mkLabelEnvDec parsed_vec_multi_imm_borrow
def vec_mut_borrow_write_lenvDec := mkLabelEnvDec parsed_vec_mut_borrow_write

theorem vec_imm_borrow_read_check :
  check_fun_dec parsed_vec_imm_borrow_read vec_imm_borrow_read_lenvDec = true := by native_decide

theorem vec_multi_imm_borrow_check :
  check_fun_dec parsed_vec_multi_imm_borrow vec_multi_imm_borrow_lenvDec = true := by native_decide

theorem vec_mut_borrow_write_check :
  check_fun_dec parsed_vec_mut_borrow_write vec_mut_borrow_write_lenvDec = true := by native_decide

-- Relational Type Checking (via Algorithmic Soundness)
theorem vec_imm_borrow_read_welltyped : ∃ lenv, typecheck_fun parsed_vec_imm_borrow_read lenv AssocMap.empty :=
  ⟨_, check_fun_dec_sound _ _ _ vec_imm_borrow_read_check⟩

theorem vec_multi_imm_borrow_welltyped : ∃ lenv, typecheck_fun parsed_vec_multi_imm_borrow lenv AssocMap.empty :=
  ⟨_, check_fun_dec_sound _ _ _ vec_multi_imm_borrow_check⟩

theorem vec_mut_borrow_write_welltyped : ∃ lenv, typecheck_fun parsed_vec_mut_borrow_write lenv AssocMap.empty :=
  ⟨_, check_fun_dec_sound _ _ _ vec_mut_borrow_write_check⟩

end LeanMove.Tests.Expressivity.VecBorrowSequential
