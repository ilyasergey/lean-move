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

-- Defining DecidableEq instance
/-
def decEqBasicMoveType (x y : BasicMoveType) : Decidable (x = y) :=

  let decPair (a b: Id × BasicMoveType):  Decidable (a = b) := match a, b with
    | (i, x), (j, y) =>  match decEq i j with
      | isFalse h => isFalse (by sby scase)
      | isTrue h => by
        subst j
        exact (match decEqBasicMoveType x y with
        | isTrue h' => by sby apply isTrue
        | isFalse h' => by sby apply isFalse)

  let rec listDec (l₁ l₂ : List (Id × BasicMoveType)) : Decidable (l₁ = l₂) := match l₁, l₂ with
     | .nil, .nil => isTrue rfl
     | .cons _ _, .nil => isFalse (fun h => List.noConfusion h)
     | .nil, .cons _ _ => isFalse (fun h => List.noConfusion h)
     | .cons x xs, .cons y ys =>
      match decPair x y with
      | isTrue hab  =>
        match listDec xs ys with
        | isTrue habs  => isTrue (hab ▸ habs ▸ rfl)
        | isFalse nabs => isFalse (fun h => List.noConfusion h (fun _ habs => absurd habs nabs))
      | isFalse nab => isFalse (fun h => List.noConfusion h (fun hab _ => absurd hab nab))

  match x, y with
  | .tint, .tint => isTrue rfl
  | .tbool, .tbool => isTrue rfl
  | .tunit, .tunit => isTrue rfl
  | .trecord m1, .trecord m2 => by simp only [BasicMoveType.trecord.injEq]; exact (
      match (listDec m1.entries m2.entries) with
      | isTrue h => isTrue (by sby move: m1 m2 h=>[e1][e2])
      | isFalse h => isFalse (fun h' => h (by cases h'; rfl))
   )
   | .tint, .tbool => isFalse (fun h => BasicMoveType.noConfusion h)
   | .tint, .tunit => isFalse (fun h => BasicMoveType.noConfusion h)
   | .tint, .trecord _ => isFalse (fun h => BasicMoveType.noConfusion h)
   | .tbool, .tint => isFalse (fun h => BasicMoveType.noConfusion h)
   | .tbool, .tunit => isFalse (fun h => BasicMoveType.noConfusion h)
   | .tbool, .trecord _ => isFalse (fun h => BasicMoveType.noConfusion h)
   | .tunit, .tint => isFalse (fun h => BasicMoveType.noConfusion h)
   | .tunit, .tbool => isFalse (fun h => BasicMoveType.noConfusion h)
   | .tunit, .trecord _ => isFalse (fun h => BasicMoveType.noConfusion h)
   | .trecord _, .tint => isFalse (fun h => BasicMoveType.noConfusion h)
   | .trecord _, .tbool => isFalse (fun h => BasicMoveType.noConfusion h)
   | .trecord _, .tunit => isFalse (fun h => BasicMoveType.noConfusion h)

instance : DecidableEq BasicMoveType := fun x y => decEqBasicMoveType x y
-/


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

-- Types
inductive MoveType where
  | basic: BasicMoveType → MoveType
  -- TODO: can simplify: no need to nest refs
  | ref : MoveType → Aref → MoveType
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
