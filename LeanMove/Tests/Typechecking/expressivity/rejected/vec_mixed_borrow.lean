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
# Vector Mixed Borrow Tests

Adapted from tnowacki/sui bytecode-verifier-transactional-tests:
- vector_ops_mixed_borrow.mvir

REJECTED: mut borrow + imm borrow on vector, then Self.foo() call.
The double borrow creates overlapping references.
-/

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Typing

namespace LeanMove.Tests.Expressivity.VecMixedBorrow

open LeanMove.Tests.Parsing.TestUtils

private def vecMixedBorrowMvir :=
  include_str "../../../MVIR/vec_mixed_borrow.mvir"

#guard (parseAndTranslate vecMixedBorrowMvir).isOk

private def parsedFuns := (parseAndTranslate vecMixedBorrowMvir).toOption.get!

def parsed_test :=
  (findFunInModule parsedFuns "vector_ops_mixed_borrow" "test").get!

def test_lenv := mkLabelEnv parsed_test

#guard !check_fun parsed_test test_lenv AssocMap.empty

end LeanMove.Tests.Expressivity.VecMixedBorrow
