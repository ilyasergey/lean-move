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
import LeanMove.Structures.DecidableEquality

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

-- Types Field, BasicMoveType, Var, Aref, BorrowingKind, MoveType are imported
-- from LeanMove.Structures.DecidableEquality (same namespace)

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
  | borrowMutField : Site → BasicMoveType → Field → Expr  -- &mut a.T::f
  | binop : Binop → Site → Site → Expr  -- a + b
  | readRef : Site → Expr  -- *a
  | pack : Id → List (Field × Site) → Expr  -- T { f: a1, ..., f: an }
  | freeze : Site → Expr
deriving Repr, Inhabited, Hashable

-- Statements in a-normal form with continuation-passing style
-- Terminal statements (skip, jump, branch, ret, abort) have no continuation
-- Non-terminal statements take their continuation as the last argument
inductive Stmt where
  -- Terminal statements (no continuation)
  | skip : Stmt                                    -- no-op (terminal)
  | jump : Label → Stmt                            -- goto L
  | branch : Site → Label → Label → Stmt           -- if (a) goto L1 else goto L2
  | ret : List Site → Stmt                         -- return (a1, ..., an)
  | abort : Site → Stmt                            -- abort a
  -- Non-terminal statements (take continuation)
  | letBind : Site → Expr → Stmt → Stmt            -- let a = e; cont
  | unpack : List (Field × Site) → Site → Stmt → Stmt  -- T { fi: ai, ...} = b; cont
  | call : List Site → Id → List Site → Stmt → Stmt    -- let (a1, ..., an) = f(b1, ..., bm); cont
  | assign : Var → Site → Stmt → Stmt              -- x = a; cont
  | writeRef : Site → Site → Stmt → Stmt           -- *a = b; cont
  | release : Site → Stmt → Stmt                   -- release(a); cont
deriving Repr, Inhabited

-- Local variable declaration
structure LocalVar where
  name : Var
  type : MoveType
deriving Repr, Inhabited, Hashable

-- A labeled block: label and body (which ends with a terminal statement)
structure Block where
  label : Label
  body : Stmt
deriving Repr, Inhabited

-- Parameter type: basic type + optional reference mutability
structure ParamType where
  -- inner type
  basicType : BasicMoveType
  -- mutable    = some true
  -- immmutable = some false
  -- not a reference = none
  isRefMut : Option Bool
deriving Repr, Inhabited, Hashable, DecidableEq

-- Function definition
structure FunDef where
  params : List (Var × MoveType)  -- (x : T)*
  returnType : List ParamType  -- Return type specifications
  locals : List LocalVar  -- (let v : T)*
  blocks : List Block  -- List of labeled blocks; first block is entry point
deriving Repr, Inhabited

end MoveLight

end LeanMove.Lang
