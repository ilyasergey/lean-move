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
import LeanMove.Tests.Parsing.TestUtils

/-!
# Vector Pop After Borrow Tests

Adapted from tnowacki/sui bytecode-verifier-transactional-tests:
- vector_ops_pop_after_borrow.mvir

REJECTED: popping from a vector while an element borrow is live
invalidates the borrow (the popped element might be the borrowed one).
-/

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Typing

namespace LeanMove.Tests.Expressivity.VecPopAfterBorrow

open LeanMove.Tests.Parsing.TestUtils

private def vecPopAfterBorrowMvir :=
  include_str "vec_pop_after_borrow.mvir"

#guard (parseAndTranslate vecPopAfterBorrowMvir).isOk

private def parsedFuns := (parseAndTranslate vecPopAfterBorrowMvir).toOption.get!

-- All modules are 0x42.m with entry foo(), use indexed access
def parsed_pop_after_imm :=
  (findFunAt parsedFuns 0).get!

def parsed_pop_after_mut :=
  (findFunAt parsedFuns 1).get!

def pop_after_imm_lenv := mkLabelEnv parsed_pop_after_imm
def pop_after_mut_lenv := mkLabelEnv parsed_pop_after_mut

#guard !check_fun parsed_pop_after_imm pop_after_imm_lenv AssocMap.empty
#guard !check_fun parsed_pop_after_mut pop_after_mut_lenv AssocMap.empty

end LeanMove.Tests.Expressivity.VecPopAfterBorrow
