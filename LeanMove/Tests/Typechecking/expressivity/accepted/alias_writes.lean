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

namespace LeanMove.Tests.Expressivity.AliasWrites

-- Variables
def var_a : Var := ⟨"a"⟩
def var_x : Var := ⟨"x"⟩
def var_y : Var := ⟨"y"⟩

-- Hand-written FunDefs moved to Tests/Parsing/Test_alias_writes.lean

-- -----------------------------------------------------
-- -    Parsed MVIR Programs                           --
-- -----------------------------------------------------

open LeanMove.Tests.Parsing.TestUtils

private def aliasWritesMvir :=
  include_str "alias_writes.mvir"

private def parsedFuns := (parseAndTranslate aliasWritesMvir).toOption.get!

def parsed_borrow_local_twice :=
  (findFunInModule parsedFuns "borrow_local_twice" "t").get!

def parsed_borrow_local_twice_reverse :=
  (findFunInModule parsedFuns "borrow_local_twice_reverse" "t").get!

def parsed_borrow_local_and_copy_ref :=
  (findFunInModule parsedFuns "borrow_local_and_copy_ref" "t").get!

def parsed_borrow_local_and_copy_ref_reverse :=
  (findFunInModule parsedFuns "borrow_local_and_copy_ref_reverse" "t").get!

-- Uncomment to pretty-print the parsed FunDefs:
-- #eval IO.println (ppFunDef "borrow_local_twice" parsed_borrow_local_twice)
-- #eval IO.println (ppFunDef "borrow_local_twice_reverse" parsed_borrow_local_twice_reverse)
-- #eval IO.println (ppFunDef "borrow_local_and_copy_ref" parsed_borrow_local_and_copy_ref)
-- #eval IO.println (ppFunDef "borrow_local_and_copy_ref_reverse" parsed_borrow_local_and_copy_ref_reverse)

-- -----------------------------------------------------
-- -           Algorithmic Type Checking Tests        --
-- -----------------------------------------------------

-- Initial environments (decidable)
def borrow_local_twice_lenvDec := mkLabelEnvDec parsed_borrow_local_twice

def borrow_local_twice_reverse_lenvDec := mkLabelEnvDec parsed_borrow_local_twice_reverse

def borrow_local_and_copy_ref_lenvDec := mkLabelEnvDec parsed_borrow_local_and_copy_ref

def borrow_local_and_copy_ref_reverse_lenvDec := mkLabelEnvDec parsed_borrow_local_and_copy_ref_reverse

-- Theorems: all functions type check algorithmically
theorem borrow_local_twice_check :
  check_fun_dec parsed_borrow_local_twice borrow_local_twice_lenvDec = true := by native_decide

theorem borrow_local_twice_reverse_check :
  check_fun_dec parsed_borrow_local_twice_reverse borrow_local_twice_reverse_lenvDec = true := by native_decide

theorem borrow_local_and_copy_ref_check :
  check_fun_dec parsed_borrow_local_and_copy_ref borrow_local_and_copy_ref_lenvDec = true := by native_decide

theorem borrow_local_and_copy_ref_reverse_check :
  check_fun_dec parsed_borrow_local_and_copy_ref_reverse borrow_local_and_copy_ref_reverse_lenvDec = true := by native_decide

-- -----------------------------------------------------
-- -           Relational Type Checking Theorems      --
-- -----------------------------------------------------

theorem borrow_local_twice_welltyped : ∃ lenv, typecheck_fun parsed_borrow_local_twice lenv AssocMap.empty :=
  ⟨_, check_fun_dec_sound _ _ _ borrow_local_twice_check⟩

theorem borrow_local_twice_reverse_welltyped : ∃ lenv, typecheck_fun parsed_borrow_local_twice_reverse lenv AssocMap.empty :=
  ⟨_, check_fun_dec_sound _ _ _ borrow_local_twice_reverse_check⟩

theorem borrow_local_and_copy_ref_welltyped : ∃ lenv, typecheck_fun parsed_borrow_local_and_copy_ref lenv AssocMap.empty :=
  ⟨_, check_fun_dec_sound _ _ _ borrow_local_and_copy_ref_check⟩

theorem borrow_local_and_copy_ref_reverse_welltyped : ∃ lenv, typecheck_fun parsed_borrow_local_and_copy_ref_reverse lenv AssocMap.empty :=
  ⟨_, check_fun_dec_sound _ _ _ borrow_local_and_copy_ref_reverse_check⟩

end LeanMove.Tests.Expressivity.AliasWrites
