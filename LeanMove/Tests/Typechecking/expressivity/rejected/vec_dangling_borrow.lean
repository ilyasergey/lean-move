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
import LeanMove.Typing.Algorithmic.AlgorithmicTypeChecking
import LeanMove.Typing.Algorithmic.AlgorithmicTypingSoundness
import LeanMove.Lang.Macros
import LeanMove.Lang.MoveIR.PrettyPrint
import LeanMove.Tests.Parsing.TestUtils

/-!
# Vector Dangling Borrow Tests

Adapted from tnowacki/sui bytecode-verifier-transactional-tests:
- vector_ops_pop_after_borrow.mvir
- vector_ops_double_borrow.mvir

All functions are REJECTED by the type checker because they attempt to
mutate a vector (push_back, pop_back, writeRef) while an element borrow
is still live. The `check_outbound` guard detects the outstanding borrow.
-/

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Typing
open AssocMap
open Regex

namespace LeanMove.Tests.Expressivity.VecDanglingBorrow

open LeanMove.Tests.Parsing.TestUtils

private def vecDanglingBorrowMvir :=
  include_str "../../../MVIR/vec_dangling_borrow.mvir"

#guard (parseAndTranslate vecDanglingBorrowMvir).isOk

private def parsedFuns := (parseAndTranslate vecDanglingBorrowMvir).toOption.get!

-- Module: vec_push_while_borrow (rejected)
def parsed_push_while_borrow :=
  (findFunInModule parsedFuns "vec_push_while_borrow" "t").get!

-- Module: vec_pop_while_borrow (rejected)
def parsed_pop_while_borrow :=
  (findFunInModule parsedFuns "vec_pop_while_borrow" "t").get!

-- Module: vec_write_while_borrow (rejected)
def parsed_write_while_borrow :=
  (findFunInModule parsedFuns "vec_write_while_borrow" "t").get!

def push_while_borrow_lenv := mkLabelEnv parsed_push_while_borrow
def pop_while_borrow_lenv := mkLabelEnv parsed_pop_while_borrow
def write_while_borrow_lenv := mkLabelEnv parsed_write_while_borrow

#eval check_fun parsed_push_while_borrow push_while_borrow_lenv AssocMap.empty

#guard !check_fun parsed_push_while_borrow push_while_borrow_lenv AssocMap.empty

#eval check_fun parsed_pop_while_borrow pop_while_borrow_lenv AssocMap.empty

#guard !check_fun parsed_pop_while_borrow pop_while_borrow_lenv AssocMap.empty

#eval check_fun parsed_write_while_borrow write_while_borrow_lenv AssocMap.empty

#guard !check_fun parsed_write_while_borrow write_while_borrow_lenv AssocMap.empty

end LeanMove.Tests.Expressivity.VecDanglingBorrow
