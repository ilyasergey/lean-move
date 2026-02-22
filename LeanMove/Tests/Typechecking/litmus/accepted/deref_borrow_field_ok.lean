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
import LeanMove.Typing.TypeChecking
import LeanMove.Typing.Algorithmic.DecidableTypeEnv
import LeanMove.Lang.Macros

-- -----------------------------------------------------
-- -       Example: Basic Move IR Translation        --
-- -----------------------------------------------------

/-
Source:

https://github.com/MystenLabs/sui/blob/main/external-crates/move/crates/bytecode-verifier-transactional-tests/tests/reference_safety/deref_borrow_field_ok.mvir

 -/

namespace LeanMove.Tests

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Typing
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

-- -----------------------------------------------------
-- -              Shared Definitions                  --
-- -----------------------------------------------------

-- Abbreviation for the struct type M.T = { f: u64 }
def M_T_basic : BasicMoveType := .trecord (AssocMap.insert AssocMap.empty ⟨"f"⟩ .u64)
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

-- Function environment: maps function names to their signatures
def module_funEnv : AssocMap Id FunSig :=
  AssocMap.insert
    (AssocMap.insert AssocMap.empty
      "M.new" ⟨[⟨.u64, none⟩], [⟨M_T_basic, none⟩]⟩)
    "M.t" ⟨[⟨M_T_basic, some false⟩], []⟩

-- -----------------------------------------------------
-- -                    M.new                         --
-- -----------------------------------------------------

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
  params := [(var_g, .basic .u64)]
  returnType := [⟨M_T_basic, none⟩]
  locals := []
  blocks := [
    { label := "b0"
      body :=
        (letsite s0 ← move var_g) ;;                             -- let s0 = move(g)
        (letsite s1 ← pack("T", [(field_f, s0)])) ;;            -- let s1 = T{f: s0}
        ret [s1]                                                 -- return s1
    }
  ]
}

-- Decidable label environment for M.new
def M_new_lenvDec := mkLabelEnvDec M_new module_funEnv

-- Test theorem: M.new type checks algorithmically
theorem M_new_check : check_fun_dec M_new M_new_lenvDec = true := by rfl

-- Theorem: M.new is well-typed (via algorithmic soundness)
theorem M_new_welltyped : ∃ lenv, typecheck_fun M_new lenv :=
  ⟨_, check_fun_dec_sound _ _ M_new_check⟩

-- -----------------------------------------------------
-- -                     M.t                          --
-- -----------------------------------------------------

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
  params := [(var_this, .ref M_T_basic (.paramRef var_this) .siteBorrowImm)]
  returnType := []
  locals := [{ name := var_y, type := .basic .u64 }]
  blocks := [
    { label := "b0"
      body :=
        (letsite s0 ← move var_this) ;;                              -- let s0 = move(this)
        (letsite s1 ← borrowField(s0, M_T_basic, field_f)) ;;       -- let s1 = &s0.T::f
        (letsite s2 ← *s1) ;;                                       -- let s2 = *s1
        (var_y ::= s2) ;;                                            -- y = s2
        ret []                                                       -- return
    }
  ]
}

-- Decidable label environment for M.t
def M_t_lenvDec := mkLabelEnvDec M_t module_funEnv

-- Test theorem: M.t type checks algorithmically
theorem M_t_check : check_fun_dec M_t M_t_lenvDec = true := by rfl

-- Theorem: M_t is well-typed (via algorithmic soundness)
theorem M_t_welltyped : ∃ lenv, typecheck_fun M_t lenv :=
  ⟨_, check_fun_dec_sound _ _ M_t_check⟩

-- -----------------------------------------------------
-- -                     foo                          --
-- -----------------------------------------------------

/-
  Function foo() translated to MoveLight AST:

  entry foo() {
      let x: M.T;
      let x_ref: &M.T;
  label b0:
      x = T{f: 2};         // M.new(2) inlined as pack
      x_ref = &x;          // borrow x into s1, then assign to x_ref
      M.t(move(x_ref));    // move x_ref into s2, call M.t (call consumes s2)
      return;
  }
-/
def foo : FunDef := {
  params := []
  returnType := []
  locals := [
    { name := var_x, type := M_T },
    { name := var_x_ref, type := .ref M_T_basic (.refid 1) .siteBorrowImm }
  ]
  blocks := [
    { label := "b0"
      body :=
        -- x = T{f: 2} (M.new inlined: literal, pack, assign)
        (letsite s3 ← #2) ;;                                    -- let s3 = 2
        (letsite s0 ← pack("T", [(field_f, s3)])) ;;            -- let s0 = T{f: s3}
        (var_x ::= s0) ;;                                       -- x = s0
        -- x_ref = &x (in A-normal form: borrow then assign)
        (letsite s1 ← &var_x) ;;                                -- let s1 = &x
        (var_x_ref ::= s1) ;;                                   -- x_ref = s1
        -- M.t(move(x_ref)) (in A-normal form: move then call)
        (letsite s2 ← move var_x_ref) ;;                        -- let s2 = move(x_ref)
        (call([], "M.t", [s2])) ;;                              -- M.t(s2) — consumes s2
        ret []                                                  -- return
    }
  ]
}

-- Decidable label environment for foo
def foo_lenvDec := mkLabelEnvDec foo module_funEnv

-- Test theorem: foo type checks algorithmically
theorem foo_check : check_fun_dec foo foo_lenvDec = true := by rfl

-- Theorem: foo is well-typed (via algorithmic soundness)
theorem foo_welltyped : ∃ lenv, typecheck_fun foo lenv :=
  ⟨_, check_fun_dec_sound _ _ foo_check⟩

end LeanMove.Tests
