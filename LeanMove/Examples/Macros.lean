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

/-! ## Macros for MoveLight AST -/

open LeanMove.Lang.MoveLight

-- Statement sequencing: s1 ;; s2
infixr:20 " ;; " => Stmt.seq

-- Variable assignment: x ::= a
infixl:50 " ::= " => Stmt.assign

-- Let binding with borrow: letsite a ← &x
macro "letsite" a:term " ← " "&" x:term : term =>
  `(Stmt.letBind $a (Expr.usage (Usage.borrowImm $x)))

-- Let binding with mutable borrow: letsite a ← &mut x
macro "letsite" a:term " ← " "&mut" x:term : term =>
  `(Stmt.letBind $a (Expr.usage (Usage.borrowMut $x)))

-- Let binding with copy: letsite a ← copy x
macro "letsite" a:term " ← " "copy" x:term : term =>
  `(Stmt.letBind $a (Expr.usage (Usage.copy $x)))

-- Let binding with move: letsite a ← move x
macro "letsite" a:term " ← " "move" x:term : term =>
  `(Stmt.letBind $a (Expr.usage (Usage.move $x)))

-- Jump: jump "label"
macro "jump" l:term : term => `(Stmt.jump $l)

/-!
## Notes on macros

The following macros work reliably:
- `;;` for statement sequencing
- `::=` for variable assignment
- `letsite s ← &x` for immutable borrow
- `letsite s ← &mut x` for mutable borrow
- `letsite s ← copy x` for copy
- `letsite s ← move x` for move
- `jump "label"` for jumps

For other statement forms, use dot notation directly:
- `.ret [s1, s2]` for return
- `.call [results] "fname" [args]` for function calls
- `.release s` for releasing references
- `.letBind s (.pack "T" [(f, a)])` for packing structs
- `.letBind s (.readRef src)` for reading references
- `.letBind s (.borrowField src bt f)` for borrowing fields
-/
