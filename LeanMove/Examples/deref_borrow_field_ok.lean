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

module 0x1.M {
    struct T has drop {f: u64}

    public new(g: u64): Self.T {
    label b0:
        return T{f: move(g)};
    }

    public t(this: &Self.T) {
        let y: u64;
    label b0:
        y = *&move(this).T::f; // valid deref/read
        return;
    }
}

//# run
module 0x42.m {
import 0x1.M;

entry foo() {
    let x: M.T;
    let x_ref: &M.T;
    x = M.new(2);
    x_ref = &x;
    M.t(move(x_ref));
    return;
}
}
-/

-- Abbreviation for the struct type M.T = { f: u64 }
def M_T_basic : BasicMoveType := .trecord (AssocMap.insert AssocMap.empty ⟨"f"⟩ .tint)
def M_T : MoveType := .basic M_T_basic

-- Field "f"
def field_f : Field := ⟨"f"⟩

-- Variables used across functions
def var_g : Var := ⟨"g"⟩
def var_this : Var := ⟨"this"⟩
def var_y : Var := ⟨"y"⟩
def var_x : Var := ⟨"x"⟩
def var_x_ref : Var := ⟨"x_ref"⟩

-- Sites (temporaries in A-normal form)
def s0 : Site := .site 0
def s1 : Site := .site 1
def s2 : Site := .site 2
def s3 : Site := .site 3

/-
  Function M.new(g: u64): Self.T

  public new(g: u64): Self.T {
  label b0:
      return T{f: move(g)};
  }

  Translation:
  - move(g) into s0
  - pack T{f: s0} into s1
  - return s1
-/
def M_new : FunDef := {
  params := [(var_g, .basic .tint)]
  returnType := M_T
  locals := []
  blocks := [
    { label := "b0"
      body :=
        -- let s0 = move(g)
        .seq (.letBind s0 (.usage (.move var_g)))
        -- let s1 = T{f: s0}
        (.seq (.letBind s1 (.pack "T" [(field_f, s0)]))
        -- return s1
        (.ret [s1]))
    }
  ]
}

/-
  Function M.t(this: &Self.T)

  public t(this: &Self.T) {
      let y: u64;
  label b0:
      y = *&move(this).T::f; // valid deref/read
      return;
  }

  Translation:
  - move(this) into s0
  - borrow field f from s0: &s0.T::f into s1
  - read reference *s1 into s2
  - assign y = s2
  - return
-/
def M_t : FunDef := {
  params := [(var_this, .ref M_T_basic (.varRef var_this) .siteBorrowImm)]
  returnType := .basic .tunit
  locals := [{ name := var_y, type := .basic .tint }]
  blocks := [
    { label := "b0"
      body :=
        -- let s0 = move(this)
        .seq (.letBind s0 (.usage (.move var_this)))
        -- let s1 = &s0.T::f (borrow field)
        (.seq (.letBind s1 (.borrowField s0 M_T_basic field_f))
        -- let s2 = *s1 (read reference)
        (.seq (.letBind s2 (.readRef s1))
        -- y = s2
        (.seq (.assign var_y s2)
        -- return
        (.ret []))))
    }
  ]
}

/-
  Function foo() translated to MoveLight AST:

  entry foo() {
      let x: M.T;
      let x_ref: &M.T;
  label b0:
      x = M.new(2);        // call with result in s0, then assign to x
      x_ref = &x;          // borrow x into s1, then assign to x_ref
      M.t(move(x_ref));    // move x_ref into s2, call M.t
      return;
  }
-/
def foo : FunDef := {
  params := []
  returnType := .basic .tunit
  locals := [
    { name := var_x, type := M_T },
    { name := var_x_ref, type := .ref M_T_basic (.varRef var_x) .siteBorrowImm }
  ]
  blocks := [
    { label := "b0"
      body :=
        -- x = M.new(2)
        -- In A-normal form: let s0 = M.new(2); x = s0
        .seq (.call [s0] "M.new" [])
        (.seq (.assign var_x s0)
        -- x_ref = &x
        -- In A-normal form: let s1 = &x; x_ref = s1
        (.seq (.letBind s1 (.usage (.borrowImm var_x)))
        (.seq (.assign var_x_ref s1)
        -- M.t(move(x_ref))
        -- In A-normal form: let s2 = move(x_ref); M.t(s2)
        (.seq (.letBind s2 (.usage (.move var_x_ref)))
        (.seq (.call [] "M.t" [s2])
        -- return
        (.ret []))))))
    }
  ]
}

/- -----------------------------------------------------/
/- -           Type Checking Verification             --/
/- -----------------------------------------------------/

/-
  To prove a function is well-typed, we need to:
  1. Construct the initial TypeEnv from the function's parameters and locals
  2. Construct a suitable LabelEnv mapping each block label to its expected entry environment
  3. Show that typecheck_fun holds for the function and LabelEnv
-/

-- Initial environment for M.new: parameter g is a valid mutable int variable
def M_new_initEnv : TypeEnv := {
  siteEnv := AssocMap.empty
  varEnv := init_varEnv_from_params [(var_g, .basic .tint)]
  pathEnv := PathEnv.init
  funEnv := AssocMap.empty
}

-- LabelEnv for M.new: maps "b0" to the initial environment
def M_new_lenv : LabelEnv :=
  AssocMap.insert AssocMap.empty "b0" M_new_initEnv

-- Theorem: M.new is well-typed
theorem M_new_welltyped : ∃ lenv, typecheck_fun M_new lenv := by
  exists M_new_lenv
  apply typecheck_fun.fun_ok (initEnv := M_new_initEnv)
  all_goals try aesop
  {sorry}
  {sorry}
  {sorry}
  {sorry}

end LeanMove.Examples
