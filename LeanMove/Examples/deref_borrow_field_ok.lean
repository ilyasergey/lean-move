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
import LeanMove.Checker.TypeChecking

/- -----------------------------------------------------/
/- -       Example: Basic Move IR Translation        --/
/- -----------------------------------------------------/

namespace LeanMove.Examples

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Checker
open AssocMap

/-
Original Move IR Program:

module 0x42.M {
  struct T { f: u64 }

  new(x: u64): Self.T {
    return T { f: move(x) };
  }

  t(r: &Self.T) {
    return;
  }

  entry foo() {
    let x: Self.T;
    x = Self.new(2);
    Self.t(&x);
    return;
  }
}
-/

-- Define the struct type T with field f: u64
def typeT : BasicMoveType :=
  .trecord (insert AssocMap.empty ⟨"f"⟩ .tint)

-- Function foo() translated to MoveLight A-Normal Form
def exampleFoo : Stmt :=
  .seq
    -- let s1 = copy(literal_2)
    (.letBind (Site.site 1) (Expr.usage (Usage.copy ⟨"literal_2"⟩)))
    (.seq
      -- let s2 = M.new(s1)  [consumes s1, produces s2: T]
      (.call [Site.site 2] "M.new" [Site.site 1])
      (.seq
        -- x = s2  [moves s2 into variable x]
        (.assign ⟨"x"⟩ (Site.site 2))
        (.seq
          -- let s3 = &x  [creates immutable borrow of x]
          (.letBind (Site.site 3) (Expr.usage (Usage.borrowImm ⟨"x"⟩)))
          (.seq
            -- M.t(s3)  [consumes the borrow s3]
            (.call [] "M.t" [Site.site 3])
            -- return ()
            (.return [])))))

-- Function M.new(x: u64): T
def funDefNew : FunDef :=
  { params := [(⟨"x"⟩, .basic .tint)]
  , returnType := .basic typeT
  , locals := []
  , body :=
      .seq
        -- let s1 = copy(literal_2) [for field value]
        (.letBind (Site.site 1) (Expr.usage (Usage.copy ⟨"x"⟩)))
        (.seq
          -- let s2 = T { f: s1 }
          (.letBind (Site.site 2) (Expr.pack "T" [(⟨"f"⟩, Site.site 1)]))
          -- return s2
          (.return [Site.site 2]))
  }

-- Function M.t(r: &T): ()
def funDefT : FunDef :=
  { params := [(⟨"r"⟩, .ref typeT (.varRef ⟨"r"⟩) .siteBorrowImm)]
  , returnType := .basic .tunit
  , locals := []
  , body := .return []
  }

-- Entry function foo(): ()
def funDefFoo : FunDef :=
  { params := []
  , returnType := .basic .tunit
  , locals := [LocalVar.mk ⟨"x"⟩ (.basic typeT)]
  , body := exampleFoo
  }

end LeanMove.Examples
