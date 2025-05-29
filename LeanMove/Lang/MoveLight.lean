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

-- Kinds of abstract locations: for variables, parameters, and temporaries
inductive SiteKind where
  | svar : Id → SiteKind
  | stmp: SiteKind
deriving Repr, DecidableEq, Inhabited, Hashable

-- Abstract locations aka Sites
structure Site where
  kind: SiteKind
  num : Nat -- Is variable site if some i
deriving Repr, DecidableEq, Inhabited, Hashable

namespace MoveLight

inductive BasicMoveType where
  | tint
  | tbool
  | tunit
  | trecord : AssocMap Id BasicMoveType → BasicMoveType
deriving Repr, Inhabited, Hashable


-- Types
inductive MoveType where
  | basic: BasicMoveType → MoveType
  | ref : MoveType → MoveType
deriving Repr, Inhabited, Hashable

-- Variables are just identifiers
structure Var where
  id: Id
deriving Repr, DecidableEq, Inhabited, Hashable

-- Field names for structs
structure Field where
  id: Id
deriving Repr, DecidableEq, Inhabited, Hashable

-- Variable Usage
inductive Usage where
  | copy : Var → Usage
  | move : Var → Usage
  | borrow : Var → Usage
  | borrowMut : Var → Usage
deriving Repr, DecidableEq, Inhabited, Hashable

-- Abstract locations (single-assign variables)
abbrev ALoc := Site

-- Expressions
inductive Expr where
  | usage : Usage → Expr
  | borrowField : Site → Id → Field → Expr  -- &a.T::f
  | borrowMutField : Site → Id → Field → Expr  -- &mut a.T::f
  | binop : Site → Site → Expr  -- a + b
  | readRef : Site → Expr  -- *a
  | pack : Id → List (Field × Site) → Expr  -- T { f: a1, ..., f: an }
deriving Repr, DecidableEq, Inhabited, Hashable

-- Statements
inductive Stmt where
  | skip : Stmt
  | letBind : Site → Expr → Stmt  -- let a = e
  | unpack : Id → List (Field × Site) → Site → Stmt  -- T { fi: ai, ...} = b
  | call : List Site → Id → List Site → Stmt  -- let (a1, ..., an) = f(b1, ..., bm)
  | assign : Var → Site → Stmt  -- x = a
  | writeRef : Site → Site → Stmt  -- *a = b
  | abort : Site → Stmt  -- abort a
  | release : Site → Stmt  -- release(a)
  | block : List Stmt → Stmt  -- { s;+ }
  | ifThenElse : Site → Stmt → Stmt → Stmt  -- if (a) s else s
  | while : Var → Stmt → Stmt  -- while (x) s
  | return : List Site → Stmt  -- return (a1, ..., an)
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
