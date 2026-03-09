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
# Basic Vector Operations

Tests for basic vector lifecycle operations: pack, len, push_back, pop_back.
All functions are ACCEPTED by the type checker.
-/

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Typing
open AssocMap
open Regex

namespace LeanMove.Tests.Expressivity.VecBasicOps

open LeanMove.Tests.Parsing.TestUtils

private def vecBasicOpsMvir :=
  include_str "vec_basic_ops.mvir"

#guard (parseAndTranslate vecBasicOpsMvir).isOk

private def parsedFuns := (parseAndTranslate vecBasicOpsMvir).toOption.get!

def parsed_vec_pack_empty :=
  (findFunInModule parsedFuns "vec_pack_empty" "t").get!

def parsed_vec_pack_elems :=
  (findFunInModule parsedFuns "vec_pack_elems" "t").get!

def parsed_vec_len :=
  (findFunInModule parsedFuns "vec_len" "t").get!

def parsed_vec_push :=
  (findFunInModule parsedFuns "vec_push" "t").get!

def parsed_vec_pop :=
  (findFunInModule parsedFuns "vec_pop" "t").get!

def parsed_vec_swap :=
  (findFunInModule parsedFuns "vec_swap" "t").get!

def parsed_vec_unpack :=
  (findFunInModule parsedFuns "vec_unpack" "t").get!

-- Algorithmic Type Checking (Decidable)
def vec_pack_empty_lenvDec := mkLabelEnvDec parsed_vec_pack_empty
def vec_pack_elems_lenvDec := mkLabelEnvDec parsed_vec_pack_elems
def vec_len_lenvDec := mkLabelEnvDec parsed_vec_len
def vec_push_lenvDec := mkLabelEnvDec parsed_vec_push
def vec_pop_lenvDec := mkLabelEnvDec parsed_vec_pop
def vec_swap_lenvDec := mkLabelEnvDec parsed_vec_swap
def vec_unpack_lenvDec := mkLabelEnvDec parsed_vec_unpack

theorem vec_pack_empty_check :
  check_fun_dec parsed_vec_pack_empty vec_pack_empty_lenvDec = true := by native_decide

theorem vec_pack_elems_check :
  check_fun_dec parsed_vec_pack_elems vec_pack_elems_lenvDec = true := by native_decide

theorem vec_len_check :
  check_fun_dec parsed_vec_len vec_len_lenvDec = true := by native_decide

theorem vec_push_check :
  check_fun_dec parsed_vec_push vec_push_lenvDec = true := by native_decide

theorem vec_pop_check :
  check_fun_dec parsed_vec_pop vec_pop_lenvDec = true := by native_decide

theorem vec_swap_check :
  check_fun_dec parsed_vec_swap vec_swap_lenvDec = true := by native_decide

theorem vec_unpack_check :
  check_fun_dec parsed_vec_unpack vec_unpack_lenvDec = true := by native_decide

-- Relational Type Checking (via Algorithmic Soundness)
theorem vec_pack_empty_welltyped : ∃ lenv, typecheck_fun parsed_vec_pack_empty lenv AssocMap.empty :=
  ⟨_, check_fun_dec_sound _ _ _ vec_pack_empty_check⟩

theorem vec_pack_elems_welltyped : ∃ lenv, typecheck_fun parsed_vec_pack_elems lenv AssocMap.empty :=
  ⟨_, check_fun_dec_sound _ _ _ vec_pack_elems_check⟩

theorem vec_len_welltyped : ∃ lenv, typecheck_fun parsed_vec_len lenv AssocMap.empty :=
  ⟨_, check_fun_dec_sound _ _ _ vec_len_check⟩

theorem vec_push_welltyped : ∃ lenv, typecheck_fun parsed_vec_push lenv AssocMap.empty :=
  ⟨_, check_fun_dec_sound _ _ _ vec_push_check⟩

theorem vec_pop_welltyped : ∃ lenv, typecheck_fun parsed_vec_pop lenv AssocMap.empty :=
  ⟨_, check_fun_dec_sound _ _ _ vec_pop_check⟩

theorem vec_swap_welltyped : ∃ lenv, typecheck_fun parsed_vec_swap lenv AssocMap.empty :=
  ⟨_, check_fun_dec_sound _ _ _ vec_swap_check⟩

theorem vec_unpack_welltyped : ∃ lenv, typecheck_fun parsed_vec_unpack lenv AssocMap.empty :=
  ⟨_, check_fun_dec_sound _ _ _ vec_unpack_check⟩

end LeanMove.Tests.Expressivity.VecBasicOps
