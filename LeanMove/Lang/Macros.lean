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

/-! ## Macros for MoveLight AST

With continuation-passing style, statements are composed by nesting.
The `;;` operator threads the continuation: `s1 ;; s2` means "s1 with s2 as its continuation".

Terminal statements (skip, jump, branch, ret, abort) have no continuation and end the chain.
Non-terminal statements (letBind, assign, writeRef, release, etc.) take their continuation.
-/

open LeanMove.Lang.MoveLight

/-!
## Statement Builder Type

In CPS-style, we use "statement builders" - functions that take a continuation and produce a statement.
The `;;` operator composes these builders, and terminal statements end the chain.
-/

/-- A statement builder takes a continuation and produces a complete statement -/
abbrev StmtBuilder := Stmt → Stmt

-- Statement sequencing: s1 ;; s2
-- s1 is a StmtBuilder, s2 is either a StmtBuilder or a terminal Stmt
-- This threads s2 as the continuation of s1
infixr:20 " ;; " => fun (f : StmtBuilder) (s : Stmt) => f s

-- Variable assignment builder: x ::= a (produces StmtBuilder)
macro x:term " ::= " a:term : term =>
  `((fun cont => Stmt.assign $x $a cont : StmtBuilder))

-- Let binding with borrow: letsite a ← &x (produces StmtBuilder)
macro "letsite" a:term " ← " "&" x:term : term =>
  `((fun cont => Stmt.letBind $a (Expr.usage (Usage.borrowImm $x)) cont : StmtBuilder))

-- Let binding with mutable borrow: letsite a ← &mut x (produces StmtBuilder)
macro "letsite" a:term " ← " "&mut" x:term : term =>
  `((fun cont => Stmt.letBind $a (Expr.usage (Usage.borrowMut $x)) cont : StmtBuilder))

-- Let binding with copy: letsite a ← copy x (produces StmtBuilder)
macro "letsite" a:term " ← " "copy" x:term : term =>
  `((fun cont => Stmt.letBind $a (Expr.usage (Usage.copy $x)) cont : StmtBuilder))

-- Let binding with move: letsite a ← move x (produces StmtBuilder)
macro "letsite" a:term " ← " "move" x:term : term =>
  `((fun cont => Stmt.letBind $a (Expr.usage (Usage.move $x)) cont : StmtBuilder))

-- Let binding with read reference: letsite a ← *b (produces StmtBuilder)
macro "letsite" a:term " ← " "*" b:term : term =>
  `((fun cont => Stmt.letBind $a (Expr.readRef $b) cont : StmtBuilder))

-- Let binding with freeze: letsite a ← freeze b (produces StmtBuilder)
macro "letsite" a:term " ← " "freeze" b:term : term =>
  `((fun cont => Stmt.letBind $a (Expr.freeze $b) cont : StmtBuilder))

-- Let binding with integer literal: letsite a ← #n (produces StmtBuilder)
macro "letsite" a:term " ← " "#" n:term : term =>
  `((fun cont => Stmt.letBind $a (Expr.intLit $n) cont : StmtBuilder))

-- Write reference builder: *a ::= b (produces StmtBuilder)
macro "*" a:term " ::= " b:term : term =>
  `((fun cont => Stmt.writeRef $a $b cont : StmtBuilder))

-- Release builder: release s (produces StmtBuilder)
macro "release" s:term : term =>
  `((fun cont => Stmt.release $s cont : StmtBuilder))

-- Pack struct builder: letsite s ← pack("T", [(f, a)]) (produces StmtBuilder)
macro "letsite" a:term " ← " "pack" "(" name:term "," fields:term ")" : term =>
  `((fun cont => Stmt.letBind $a (Expr.pack $name $fields) cont : StmtBuilder))

-- Borrow field builder: letsite s ← borrowField(src, bt, f) (produces StmtBuilder)
macro "letsite" af:term " ← " "borrowField" "(" a:term "," bt:term "," f:term ")" : term =>
  `((fun cont => Stmt.letBind $af (Expr.borrowField $a $bt $f) cont : StmtBuilder))

-- Call builder: call(results, fname, args) (produces StmtBuilder)
macro "call" "(" results:term "," fnName:term "," args:term ")" : term =>
  `((fun cont => Stmt.call $results $fnName $args cont : StmtBuilder))

-- Terminal statements (no continuation needed)

-- Jump: jump "label" (terminal Stmt)
macro "jump" l:term : term => `(Stmt.jump $l)

-- Branch: branch cond "l1" "l2" (terminal Stmt)
macro "branch" cond:term l1:term l2:term : term => `(Stmt.branch $cond $l1 $l2)

-- Return: ret [sites] (terminal Stmt)
macro "ret" sites:term : term => `(Stmt.ret $sites)

-- Abort: abort s (terminal Stmt)
macro "abort" s:term : term => `(Stmt.abort $s)

/-!
## Notes on macros

### Statement builder macros (produce StmtBuilder = Stmt → Stmt)
- `x ::= a` for variable assignment
- `letsite s ← &x` for immutable borrow
- `letsite s ← &mut x` for mutable borrow
- `letsite s ← copy x` for copy
- `letsite s ← move x` for move
- `letsite s ← *x` for reading reference (dereference)
- `letsite s ← freeze x` for freezing a reference
- `letsite s ← #n` for integer literal (u64 value n)
- `* a ::= b` for write through reference
- `release s` for releasing references
- `letsite s ← pack("T", [(f, a)])` for packing structs
- `letsite s ← borrowField(src, bt, f)` for borrowing fields
- `call(results, "fname", args)` for function calls

### Terminal statement macros (produce Stmt directly)
- `jump "label"` for unconditional jump
- `branch cond "l1" "l2"` for conditional branch
- `ret [s1, s2]` for return
- `abort s` for abort
- `Stmt.skip` for no-op

### Composition
- `;;` sequences statements: `s1 ;; s2` threads s2 as the continuation of s1
- Example: `(letsite s ← move x) ;; ret [s]`
  expands to: `Stmt.letBind s (Expr.usage (Usage.move x)) (Stmt.ret [s])`

### Direct notation for other forms
- `Stmt.letBind s (Expr.borrowMutField src name f) cont` for mutable field borrow
- `Stmt.unpack [(f, s)] src cont` for unpacking structs
-/
