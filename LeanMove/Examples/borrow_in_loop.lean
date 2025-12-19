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

import Ssreflect.Lang

import LeanMove.Lang.MoveLight
import LeanMove.Checker.TypeChecking

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Checker
open AssocMap


/-
Original Move IR Program:

foo() {
    let x: u64;
    let r: &u64;
    label l0:
    x = 0;
    r = &x;
    jump l0;
}
-/

namespace LeanMove.Examples.BorrowInLoop

-- Variables
def var_x : Var := ⟨"x"⟩
def var_r : Var := ⟨"r"⟩

-- Sites (temporaries in A-normal form)
def s0 : Site := .site 0  -- constant 0
def s1 : Site := .site 1  -- &x

/-
  Function foo() translated to MoveLight AST:

  foo() {
      let x: u64;
      let r: &u64;
  label l0:
      x = 0;       // let s0 = 0; x = s0
      r = &x;      // let s1 = &x; r = s1
      jump l0;
  }
-/
def foo : FunDef := {
  params := []
  returnType := .basic .tunit
  locals := [
    { name := var_x, type := .basic .tint },
    { name := var_r, type := .ref .tint (.varRef var_x) .siteBorrowImm }
  ]
  blocks := [
    { label := "l0"
      body :=
        -- x = 0 (in A-normal form: assign from a site holding constant)
        .seq (.assign var_x s0)
        -- r = &x
        (.seq (.letBind s1 (.usage (.borrowImm var_x)))
        (.seq (.assign var_r s1)
        -- jump l0
        (.jump "l0")))
    }
  ]
}

/- -----------------------------------------------------/
/- -           Type Checking Verification             --/
/- -----------------------------------------------------/

-- Initial environment for foo: no params, locals x and r are invalid
def foo_initEnv : TypeEnv := {
  siteEnv := AssocMap.empty
  varEnv := add_locals_to_varEnv AssocMap.empty foo.locals
  pathEnv := PathEnv.init
  funEnv := AssocMap.empty
}

-- LabelEnv for foo: maps "l0" to the initial environment
def foo_lenv : LabelEnv :=
  AssocMap.insert AssocMap.empty "l0" foo_initEnv

open Stmt

--[TODO] Check with Todd what would be interesting/characteristic tiny programs to type-check
-- Theorem: foo is well-typed
theorem foo_welltyped : ∃ lenv, typecheck_fun foo lenv := by
  exists foo_lenv
  apply typecheck_fun.fun_ok (initEnv := foo_initEnv)
  all_goals try aesop
  { unfold foo at a; aesop }
  {
    move: a=>//=
    scase: (foo.blocks.head?) =>//=[] l b
    scase
    srw foo_lenv at a_1
    move: (lookup_some _ _ _ a_1)=>//=
    srw foo_initEnv=>//=
    simp [AssocMap.insert]; scase=>//
    scase
    sby simp [empty]
  }
  {
    -- The actual type-checking
    scase: idx a a_1=>//=
    dsimp [foo] at * =>//==<- {block}=>//=
    srw foo_lenv foo_initEnv=>//= /lookup_some=>//=
    simp [AssocMap.insert]=>->
    -- now the fun begins: need to come up with the outEnv manually
    -- [TODO: write a symbolic execution to infer these environments]

    sorry
  }
  { sdone }

end LeanMove.Examples.BorrowInLoop
