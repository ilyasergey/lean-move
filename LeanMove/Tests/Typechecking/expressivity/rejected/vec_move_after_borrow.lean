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
# Vector Move After Borrow Tests

Adapted from tnowacki/sui bytecode-verifier-transactional-tests:
- vector_ops_move_after_borrow.mvir

REJECTED: borrowing a vector element then moving the vector invalidates the borrow.
-/

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Typing

namespace LeanMove.Tests.Expressivity.VecMoveAfterBorrow

open LeanMove.Tests.Parsing.TestUtils

private def vecMoveAfterBorrowMvir :=
  include_str "vec_move_after_borrow.mvir"

#guard (parseAndTranslate vecMoveAfterBorrowMvir).isOk

private def parsedFuns := (parseAndTranslate vecMoveAfterBorrowMvir).toOption.get!

-- All modules are 0x42.m with entry foo(), use indexed access
def parsed_move_after_imm :=
  (findFunAt parsedFuns 0).get!

def parsed_move_after_mut :=
  (findFunAt parsedFuns 1).get!

def move_after_imm_lenv := mkLabelEnv parsed_move_after_imm
def move_after_mut_lenv := mkLabelEnv parsed_move_after_mut

#guard !check_fun parsed_move_after_imm move_after_imm_lenv AssocMap.empty
#guard !check_fun parsed_move_after_mut move_after_mut_lenv AssocMap.empty

end LeanMove.Tests.Expressivity.VecMoveAfterBorrow
