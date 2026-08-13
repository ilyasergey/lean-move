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

-- Let binding with integer literal: letsite a ← #n (produces StmtBuilder).
-- An unannotated literal is `u64`, matching the MVIR convention for an
-- unsuffixed literal; use `letsite a ← #n w` to pick another width.
macro "letsite" a:term " ← " "#" n:term : term =>
  `((fun cont => Stmt.letBind $a (Expr.intLit $n .u64) cont : StmtBuilder))

-- Let binding with a width-annotated integer literal: letsite a ← #n w
macro "letsite" a:term " ← " "#" n:term w:term : term =>
  `((fun cont => Stmt.letBind $a (Expr.intLit $n $w) cont : StmtBuilder))

-- Write reference builder: *a ::= b (produces StmtBuilder)
macro "*" a:term:max " ::= " b:term:21 : term =>
  `((fun cont => Stmt.writeRef $a $b cont : StmtBuilder))

-- Release builder: release s (produces StmtBuilder)
macro "release" s:term:max : term =>
  `((fun cont => Stmt.release $s cont : StmtBuilder))

-- Pack struct builder: letsite s ← pack("T", [(f, a)]) (produces StmtBuilder)
macro "letsite" a:term " ← " "pack" "(" name:term "," fields:term ")" : term =>
  `((fun cont => Stmt.letBind $a (Expr.pack $name $fields) cont : StmtBuilder))

-- Borrow field builder: letsite s ← borrowField(src, bt, f) (produces StmtBuilder)
macro "letsite" af:term " ← " "borrowField" "(" a:term "," bt:term "," f:term ")" : term =>
  `((fun cont => Stmt.letBind $af (Expr.borrowField $a $bt $f) cont : StmtBuilder))

-- Borrow mutable field builder: letsite s ← borrowMutField(src, bt, f) (produces StmtBuilder)
macro "letsite" af:term " ← " "borrowMutField" "(" a:term "," bt:term "," f:term ")" : term =>
  `((fun cont => Stmt.letBind $af (Expr.borrowMutField $a $bt $f) cont : StmtBuilder))

-- Unpack builder: unpack(fields, src) (produces StmtBuilder)
macro "unpack" "(" fields:term "," src:term ")" : term =>
  `((fun cont => Stmt.unpack $fields $src cont : StmtBuilder))

-- Call builder: call(results, fname, args) (produces StmtBuilder)
macro "call" "(" results:term "," fnName:term "," args:term ")" : term =>
  `((fun cont => Stmt.call $results $fnName $args cont : StmtBuilder))

-- Vector operations

-- Let binding with vec_pack: letsite a ← vecPack(T, elems) (produces StmtBuilder)
macro "letsite" a:term " ← " "vecPack" "(" t:term "," elems:term ")" : term =>
  `((fun cont => Stmt.letBind $a (Expr.vecPack $t $elems) cont : StmtBuilder))

-- Let binding with vec_len: letsite a ← vecLen(src) (produces StmtBuilder)
macro "letsite" a:term " ← " "vecLen" "(" src:term ")" : term =>
  `((fun cont => Stmt.letBind $a (Expr.vecLen $src) cont : StmtBuilder))

-- Let binding with vec_imm_borrow: letsite a ← vecImmBorrow(src, idx) (produces StmtBuilder)
macro "letsite" a:term " ← " "vecImmBorrow" "(" src:term "," idx:term ")" : term =>
  `((fun cont => Stmt.letBind $a (Expr.vecImmBorrow $src $idx) cont : StmtBuilder))

-- Let binding with vec_mut_borrow: letsite a ← vecMutBorrow(src, idx) (produces StmtBuilder)
macro "letsite" a:term " ← " "vecMutBorrow" "(" src:term "," idx:term ")" : term =>
  `((fun cont => Stmt.letBind $a (Expr.vecMutBorrow $src $idx) cont : StmtBuilder))

-- Let binding with vec_pop_back: letsite a ← vecPopBack(src) (produces StmtBuilder)
macro "letsite" a:term " ← " "vecPopBack" "(" src:term ")" : term =>
  `((fun cont => Stmt.letBind $a (Expr.vecPopBack $src) cont : StmtBuilder))

-- Vec unpack builder: vecUnpack(T, results, src) (produces StmtBuilder)
macro "vecUnpack" "(" t:term "," results:term "," src:term ")" : term =>
  `((fun cont => Stmt.vecUnpack $t $results $src cont : StmtBuilder))

-- Vec push_back builder: vecPushBack(ref, val) (produces StmtBuilder)
macro "vecPushBack" "(" ref:term "," val:term ")" : term =>
  `((fun cont => Stmt.vecPushBack $ref $val cont : StmtBuilder))

-- Vec swap builder: vecSwap(ref, idx1, idx2) (produces StmtBuilder)
macro "vecSwap" "(" ref:term "," idx1:term "," idx2:term ")" : term =>
  `((fun cont => Stmt.vecSwap $ref $idx1 $idx2 cont : StmtBuilder))

-- Binop: letsite a ← binop(op, b, c) (produces StmtBuilder)
macro "letsite" a:term " ← " "binop" "(" op:term "," b:term "," c:term ")" : term =>
  `((fun cont => Stmt.letBind $a (Expr.binop $op $b $c) cont : StmtBuilder))

-- Unop: letsite a ← unop(op, b) (produces StmtBuilder)
macro "letsite" a:term " ← " "unop" "(" op:term "," b:term ")" : term =>
  `((fun cont => Stmt.letBind $a (Expr.unop $op $b) cont : StmtBuilder))

-- Enum operations

-- Let binding with packVariant: letsite a ← packVariant(ename, vname, fields) (produces StmtBuilder)
macro "letsite" a:term " ← " "packVariant" "(" ename:term "," vname:term "," fields:term ")" : term =>
  `((fun cont => Stmt.letBind $a (Expr.packVariant $ename $vname $fields) cont : StmtBuilder))

-- Unpack variant builder: unpackVariant(vname, fields, src) (produces StmtBuilder)
macro "unpackVariant" "(" vname:term "," fields:term "," src:term ")" : term =>
  `((fun cont => Stmt.unpackVariant $vname $fields $src cont : StmtBuilder))

-- Terminal statements (no continuation needed)

-- Jump: jump "label" (terminal Stmt)
macro "jump" l:term : term => `(Stmt.jump $l)

-- Branch: branch cond "l1" "l2" (terminal Stmt)
macro "branch" cond:term:max l1:term:max l2:term : term => `(Stmt.branch $cond $l1 $l2)

-- Return: ret [sites] (terminal Stmt)
macro "ret" sites:term : term => `(Stmt.ret $sites)

-- Abort: abort s (terminal Stmt)
macro "abort" s:term : term => `(Stmt.abort $s)

-- Variant switch: variantSwitch src cases (terminal Stmt)
macro "variantSwitch" src:term cases:term : term => `(Stmt.variantSwitch $src $cases)

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
- `letsite s ← borrowField(src, bt, f)` for borrowing immutable fields
- `letsite s ← borrowMutField(src, bt, f)` for borrowing mutable fields
- `unpack(fields, src)` for unpacking structs
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

### Note on partial application
The following raw `Stmt` constructors also work as `StmtBuilder` via partial application:
- `Stmt.writeRef a b` (equivalent to `*a ::= b`)
- `Stmt.call results fname args` (equivalent to `call(results, fname, args)`)
- `Stmt.unpack fields src` (equivalent to `unpack(fields, src)`)
The macro forms are preferred for readability and closeness to Move IR syntax.
-/
