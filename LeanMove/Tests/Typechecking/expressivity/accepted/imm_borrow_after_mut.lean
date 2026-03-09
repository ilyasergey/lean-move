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

namespace LeanMove.Tests.Expressivity.ImmBorrowAfterMut

-- Variables
def var_a : Var := ⟨"a"⟩
def var_rmut : Var := ⟨"rmut"⟩
def var_rimm : Var := ⟨"rimm"⟩

-- Hand-written FunDefs moved to Tests/Parsing/Test_imm_borrow_after_mut.lean

-- -----------------------------------------------------
-- -    Parsed MVIR Programs                           --
-- -----------------------------------------------------

open LeanMove.Tests.Parsing.TestUtils

private def immBorrowAfterMutMvir :=
  include_str "../../../MVIR/imm_borrow_after_mut.mvir"

private def parsedFuns := (parseAndTranslate immBorrowAfterMutMvir).toOption.get!

def parsed_direct :=
  (findFunInModule parsedFuns "direct" "t").get!

def parsed_copy_and_freeze :=
  (findFunInModule parsedFuns "copy_and_freeze" "t").get!

-- Uncomment to pretty-print the parsed FunDefs:
-- #eval IO.println (ppFunDef "direct" parsed_direct)
-- #eval IO.println (ppFunDef "copy_and_freeze" parsed_copy_and_freeze)

-- -----------------------------------------------------
-- -           Algorithmic Type Checking Tests        --
-- -----------------------------------------------------

-- Initial environments (decidable)
def direct_lenvDec := mkLabelEnvDec parsed_direct

def copy_and_freeze_lenvDec := mkLabelEnvDec parsed_copy_and_freeze

-- Theorems: both functions type check algorithmically
theorem direct_check : check_fun_dec parsed_direct direct_lenvDec = true := by native_decide
theorem copy_and_freeze_check : check_fun_dec parsed_copy_and_freeze copy_and_freeze_lenvDec = true := by native_decide

-- -----------------------------------------------------
-- -           Relational Type Checking Theorems      --
-- -----------------------------------------------------

theorem direct_welltyped : ∃ lenv, typecheck_fun parsed_direct lenv AssocMap.empty :=
  ⟨_, check_fun_dec_sound _ _ _ direct_check⟩

theorem copy_and_freeze_welltyped : ∃ lenv, typecheck_fun parsed_copy_and_freeze lenv AssocMap.empty :=
  ⟨_, check_fun_dec_sound _ _ _ copy_and_freeze_check⟩

end LeanMove.Tests.Expressivity.ImmBorrowAfterMut
