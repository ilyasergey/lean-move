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

/- -----------------------------------------------------/
/- -       Definition of the Move Light language      --/
/- -----------------------------------------------------/

namespace LeanMove.Lang

open AssocMap

abbrev Id := String

-- Abstract locations: model linear stack slots in A-Normal form
inductive Aloc where
  | aloc : Nat → Aloc -- Temp site
  | root : Aloc -- Root site
deriving Repr, DecidableEq, Inhabited, Hashable

namespace MoveLight

-- Field names for structs
structure Field where
  id: Id
deriving Repr, DecidableEq, Inhabited, Hashable

inductive BasicMoveType where
  | tint
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
  | refid : Nat -> Aref
  | varRef : Var → Aref
deriving Repr, DecidableEq, Inhabited, Hashable


inductive SiteIsBorrowing where
  | siteBorrowImm : Var -> SiteIsBorrowing
  | siteBorrowMut : Var -> SiteIsBorrowing
  | siteNotBorrowed : SiteIsBorrowing
deriving Repr, DecidableEq, Inhabited, Hashable

-- Types
inductive MoveType where
  | basic: BasicMoveType → MoveType
  -- The reference type also stores abstract location and borrowing provenance
  | ref : BasicMoveType → Aref → SiteIsBorrowing → MoveType
deriving Repr, Inhabited, Hashable


-- Variable Usage
inductive Usage where
  | copy : Var → Usage
  | move : Var → Usage
  | borrowImm : Var → Usage
  | borrowMut : Var → Usage
deriving Repr, DecidableEq, Inhabited, Hashable

-- Abstract locations (single-assign variables)
abbrev ALoc := Aloc

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
  | borrowField : Aloc → BasicMoveType → Field → Expr  -- &a.T::f
  | borrowMutField : Aloc → Id → Field → Expr  -- &mut a.T::f
  | binop : Binop → Aloc → Aloc → Expr  -- a + b
  | readRef : Aloc → Expr  -- *a
  | pack : Id → List (Field × Aloc) → Expr  -- T { f: a1, ..., f: an }
deriving Repr, Inhabited, Hashable

-- Statements in a-normal form
inductive Stmt where
  | skip : Stmt
  | letBind : Aloc → Expr → Stmt  -- let a = e
  | unpack : List (Field × Aloc) → Aloc → Stmt  -- T { fi: ai, ...} = b
  | call : List Aloc → Id → List Aloc → Stmt  -- let (a1, ..., an) = f(b1, ..., bm)
  | assign : Var → Aloc → Stmt  -- x = a
  | writeRef : Aloc → Aloc → Stmt  -- *a = b
  | abort : Aloc → Stmt  -- abort a
  | release : Aloc → Stmt  -- release(a)
  | block : List Stmt → Stmt  -- { s;+ }
  | ifThenElse : Aloc → Stmt → Stmt → Stmt  -- if (a) s else s
  | while : Var → Stmt → Stmt  -- while (x) s
  | return : List Aloc → Stmt  -- return (a1, ..., an)
deriving Repr, Inhabited

-- Local variable declaration
structure LocalVar where
  name : Var
  type : MoveType
deriving Repr, Inhabited, Hashable

-- Function definition
structure FunDef where
  params : List (Var × MoveType)  -- (x : T)*
  returnType : MoveType  -- Tr
  locals : List LocalVar  -- (let v : T)*
  body : List Stmt  -- s+
deriving Repr, Inhabited

end MoveLight

end LeanMove.Lang
