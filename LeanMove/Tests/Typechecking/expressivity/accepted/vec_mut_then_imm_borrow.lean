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
import LeanMove.Tests.Parsing.TestUtils

/-!
# Vector Mut Then Imm Borrow Test

Adapted from tnowacki/sui bytecode-verifier-transactional-tests:
- vector_ops_double_borrow.mvir (second module)

ACCEPTED: mut borrow on element 0, then imm borrow on element 1.
The imm borrow does not conflict with the existing mut borrow
because they target different elements.
-/

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Typing

namespace LeanMove.Tests.Expressivity.VecMutThenImmBorrow

open LeanMove.Tests.Parsing.TestUtils

private def vecMutThenImmBorrowMvir :=
  include_str "../../../MVIR/vec_mut_then_imm_borrow.mvir"

#guard (parseAndTranslate vecMutThenImmBorrowMvir).isOk

private def parsedFuns := (parseAndTranslate vecMutThenImmBorrowMvir).toOption.get!

def parsed_mut_then_imm :=
  (findFunAt parsedFuns 0).get!

-- Algorithmic Type Checking (Decidable)
def mut_then_imm_lenvDec := mkLabelEnvDec parsed_mut_then_imm

theorem mut_then_imm_check :
  check_fun_dec parsed_mut_then_imm mut_then_imm_lenvDec = true := by native_decide

-- Relational Type Checking (via Algorithmic Soundness)
theorem mut_then_imm_welltyped : ∃ lenv, typecheck_fun parsed_mut_then_imm lenv AssocMap.empty :=
  ⟨_, check_fun_dec_sound _ _ _ mut_then_imm_check⟩

end LeanMove.Tests.Expressivity.VecMutThenImmBorrow
