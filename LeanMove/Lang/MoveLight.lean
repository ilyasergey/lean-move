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
import LeanMove.Structures.AssocMap

/- -----------------------------------------------------
 -       Definition of the Move Light language      --
 -----------------------------------------------------/

namespace LeanMove.Lang

open AssocMap

abbrev Id := String
abbrev Label := String

-- Sites: model linear stack slots in A-Normal form
inductive Site where
  | site : Nat → Site -- Temp site
  | root : Site -- Root site
deriving Repr, DecidableEq, Inhabited, Hashable

namespace MoveLight

-- Field names for structs
structure Field where
  id: Id
deriving Repr, DecidableEq, Inhabited, Hashable

inductive BasicMoveType where
  | u64   -- Unsigned 64-bit integer
  | tbool
  | tunit
  | trecord : AssocMap Field BasicMoveType → BasicMoveType
deriving Repr, Inhabited, Hashable

-- Variables are just identifiers
structure Var where
  id: Id
deriving Repr, DecidableEq, Inhabited, Hashable

-- Abstract references
inductive Aref where
  | root : Aref
  | refid : Nat → Aref
  | varRef : Var → Aref
deriving Repr, DecidableEq, Inhabited, Hashable


-- Borrowing kind: tracks only mutability, NOT provenance
-- Provenance (which variable was borrowed) is tracked via PathEnv edges
inductive BorrowingKind where
  | siteBorrowImm : BorrowingKind
  | siteBorrowMut : BorrowingKind
deriving Repr, DecidableEq, Inhabited, Hashable

-- Types
inductive MoveType where
  | basic: BasicMoveType → MoveType
  -- The reference type stores: basic type, abstract reference, and mutability
  -- Note: Provenance (which variable was borrowed from) is tracked separately
  -- via PathEnv with root_to_var edges, not in this type
  | ref : BasicMoveType → Aref → BorrowingKind → MoveType
deriving Repr, Inhabited, Hashable

-- Variable Usage
inductive Usage where
  | copy : Var → Usage
  | move : Var → Usage
  | borrowImm : Var → Usage
  | borrowMut : Var → Usage
deriving Repr, DecidableEq, Inhabited, Hashable

-- Abstract locations (single-assign variables)
abbrev ALoc := Site

inductive Binop where
  | add
  | sub
  | mul
  | div
  | mod
  | eq
  | lt
  | nand
deriving Repr, DecidableEq, Inhabited, Hashable

-- Expressions
inductive Expr where
  | usage : Usage → Expr
  | intLit : Nat → Expr  -- Integer literal (u64 value)
  | borrowField : Site → BasicMoveType → Field → Expr  -- &a.T::f
  | borrowMutField : Site → Id → Field → Expr  -- &mut a.T::f
  | binop : Binop → Site → Site → Expr  -- a + b
  | readRef : Site → Expr  -- *a
  | pack : Id → List (Field × Site) → Expr  -- T { f: a1, ..., f: an }
  | freeze : Site → Expr
deriving Repr, Inhabited, Hashable

-- Statements in a-normal form (no control flow - that's in Terminator)
inductive Stmt where
  | skip : Stmt
  | letBind : Site → Expr → Stmt  -- let a = e
  | unpack : List (Field × Site) → Site → Stmt  -- T { fi: ai, ...} = b
  | call : List Site → Id → List Site → Stmt  -- let (a1, ..., an) = f(b1, ..., bm)
  | assign : Var → Site → Stmt  -- x = a
  | writeRef : Site → Site → Stmt  -- *a = b
  | release : Site → Stmt  -- release(a)
  | seq : Stmt → Stmt → Stmt  -- s1; s2 (sequential composition)
deriving Repr, Inhabited

-- Block terminators (control flow) - every block must end with exactly one
inductive Terminator where
  | jump : Label → Terminator  -- goto L
  | branch : Site → Label → Label → Terminator  -- if (a) goto L1 else goto L2
  | ret : List Site → Terminator  -- return (a1, ..., an)
  | abort : Site → Terminator  -- abort a
deriving Repr, Inhabited

-- Local variable declaration
structure LocalVar where
  name : Var
  type : MoveType
deriving Repr, Inhabited, Hashable

-- A labeled block: label, body statements, and terminator
structure Block where
  label : Label
  body : Stmt
  terminator : Terminator
deriving Repr, Inhabited

-- Function definition
structure FunDef where
  params : List (Var × MoveType)  -- (x : T)*
  returnType : MoveType  -- Tr
  locals : List LocalVar  -- (let v : T)*
  blocks : List Block  -- List of labeled blocks; first block is entry point
deriving Repr, Inhabited

end MoveLight

end LeanMove.Lang
