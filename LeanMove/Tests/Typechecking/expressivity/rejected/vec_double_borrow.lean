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
# Vector Double Borrow Tests

Adapted from tnowacki/sui bytecode-verifier-transactional-tests:
- vector_ops_double_borrow.mvir

REJECTED: two simultaneous borrows on a vector create overlapping
references that the type checker rejects.
(The mut-then-imm case is accepted — see accepted/vec_mut_then_imm_borrow.lean)
-/

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Typing

namespace LeanMove.Tests.Expressivity.VecDoubleBorrow

open LeanMove.Tests.Parsing.TestUtils

private def vecDoubleBorrowMvir :=
  include_str "vec_double_borrow.mvir"

#guard (parseAndTranslate vecDoubleBorrowMvir).isOk

private def parsedFuns := (parseAndTranslate vecDoubleBorrowMvir).toOption.get!

-- All modules are 0x42.m with entry foo(), use indexed access
-- Module 0 = imm_then_mut, Module 1 = mut_then_imm (accepted), Module 2 = mut_then_mut
def parsed_imm_then_mut :=
  (findFunAt parsedFuns 0).get!

def parsed_mut_then_mut :=
  (findFunAt parsedFuns 2).get!

def imm_then_mut_lenv := mkLabelEnv parsed_imm_then_mut
def mut_then_mut_lenv := mkLabelEnv parsed_mut_then_mut

#guard !check_fun parsed_imm_then_mut imm_then_mut_lenv AssocMap.empty
#guard !check_fun parsed_mut_then_mut mut_then_mut_lenv AssocMap.empty

end LeanMove.Tests.Expressivity.VecDoubleBorrow
