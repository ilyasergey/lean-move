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

-- Jump: jump "label" (Terminator)
macro "jump" l:term : term => `(Terminator.jump $l)

-- Branch: branch cond "l1" "l2" (Terminator)
macro "branch" cond:term l1:term l2:term : term => `(Terminator.branch $cond $l1 $l2)

-- Write reference: *a ::= b (write to reference)
-- Using *::= to avoid conflict with variable assignment
macro "*" a:term " ::= " b:term : term => `(Stmt.writeRef $a $b)

-- Return: ret [sites] (Terminator)
macro "ret" sites:term : term => `(Terminator.ret $sites)

-- Abort: abort s (Terminator)
macro "abort" s:term : term => `(Terminator.abort $s)

-- Release: release s
macro "release" s:term : term => `(Stmt.release $s)

-- Let binding with read reference: letsite a ← *b
macro "letsite" a:term " ← " "*" b:term : term =>
  `(Stmt.letBind $a (Expr.readRef $b))

-- Let binding with freeze: letsite a ← freeze b
macro "letsite" a:term " ← " "freeze" b:term : term =>
  `(Stmt.letBind $a (Expr.freeze $b))

-- Let binding with integer literal: letsite a ← #n
macro "letsite" a:term " ← " "#" n:term : term =>
  `(Stmt.letBind $a (Expr.intLit $n))

/-!
## Notes on macros

### Statement macros (Stmt)
- `;;` for statement sequencing
- `::=` for variable assignment
- `letsite s ← &x` for immutable borrow
- `letsite s ← &mut x` for mutable borrow
- `letsite s ← copy x` for copy
- `letsite s ← move x` for move
- `letsite s ← *x` for reading reference (dereference)
- `letsite s ← freeze x` for freezing a reference
- `letsite s ← #n` for integer literal (u64 value n)
- `* a ::= b` for write through reference
- `release s` for releasing references

### Terminator macros (Terminator)
- `jump "label"` for unconditional jump
- `branch cond "l1" "l2"` for conditional branch
- `ret [s1, s2]` for return
- `abort s` for abort

### Direct notation for other forms
- `Stmt.call [results] "fname" [args]` for function calls
- `Stmt.letBind s (Expr.pack "T" [(f, a)])` for packing structs
- `Stmt.letBind s (Expr.borrowField src bt f)` for borrowing fields
- `Stmt.letBind s (Expr.borrowMutField src name f)` for mutable field borrow
-/
