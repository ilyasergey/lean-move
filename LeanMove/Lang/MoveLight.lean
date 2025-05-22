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

import Batteries.Data.HashMap
import Ssreflect.Lang

/- -----------------------------------------------------/
/- -       Definition of the Move Light language      --/
/- -----------------------------------------------------/

namespace LeanMove.Lang

abbrev Id := String

-- Abstract locations aka Sites
structure Site where
  id: Id
deriving Repr, DecidableEq, Inhabited, Hashable

namespace MoveLight

-- Types
inductive MoveType where
  | TInt
  | TUnit
deriving Repr, DecidableEq, Inhabited, Hashable

end MoveLight

end LeanMove.Lang
