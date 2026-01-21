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
import LeanMove.Lang.Macros

-- -----------------------------------------------------
-- -       Example: Basic Move IR Translation        --
-- -----------------------------------------------------

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
        (letsite s0 ← move var_g) ;;                -- let s0 = move(g)
        Stmt.letBind s1 (Expr.pack "T" [(field_f, s0)])  -- let s1 = T{f: s0}
      terminator := ret [s1]                        -- return s1
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
        (letsite s0 ← move var_this) ;;                   -- let s0 = move(this)
        Stmt.letBind s1 (Expr.borrowField s0 M_T_basic field_f) ;; -- let s1 = &s0.T::f
        Stmt.letBind s2 (Expr.readRef s1) ;;              -- let s2 = *s1
        (var_y ::= s2)                                    -- y = s2
      terminator := ret []                                -- return
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
        -- x = M.new(2) (in A-normal form: call then assign)
        Stmt.call [s0] "M.new" [] ;;
        (var_x ::= s0) ;;
        -- x_ref = &x (in A-normal form: borrow then assign)
        (letsite s1 ← &var_x) ;;
        (var_x_ref ::= s1) ;;
        -- M.t(move(x_ref)) (in A-normal form: move then call)
        (letsite s2 ← move var_x_ref) ;;
        Stmt.call [] "M.t" [s2]
      terminator := ret []   -- return
    }
  ]
}

-- -----------------------------------------------------
-- -           Type Checking Verification             --
-- -----------------------------------------------------

/-
  To prove a function is well-typed, we need to:
  1. Construct the initial TypeEnv from the function's parameters and locals
  2. Construct a suitable LabelEnv mapping each block label to its expected entry environment
  3. Show that typecheck_fun holds for the function and LabelEnv
-/

-- Function environment: maps function names to their signatures
def module_funEnv : AssocMap Id FunSig :=
  AssocMap.insert
    (AssocMap.insert AssocMap.empty
      "M.new" ⟨[⟨.tint, none⟩], [⟨M_T_basic, none⟩]⟩)
    "M.t" ⟨[⟨M_T_basic, some false⟩], []⟩

-- Initial environment for M.new: parameter g is a valid mutable int variable
def M_new_initEnv : TypeEnv := {
  siteEnv := AssocMap.empty
  varEnv := init_varEnv_from_params [(var_g, .basic .tint)]
  pathEnv := PathEnv.init
  funEnv := module_funEnv
}

-- LabelEnv for M.new: maps "b0" to the initial environment
def M_new_lenv : LabelEnv :=
  AssocMap.insert AssocMap.empty "b0" M_new_initEnv

-- Theorem: M.new is well-typed
theorem M_new_welltyped : ∃ lenv, typecheck_fun M_new lenv := by
  exists M_new_lenv
  apply typecheck_fun.fun_ok (initEnv := M_new_initEnv)
  · rfl  -- initEnv.varEnv
  · rfl  -- initEnv.siteEnv
  · rfl  -- initEnv.pathEnv
  · simp only [M_new]; intro h; exact List.noConfusion h  -- blocks ≠ []
  · -- Entry block environment equivalence
    intro entryLabel entryBody entryTerm entryEnv hhead hlookup
    simp only [M_new, List.head?] at hhead
    injection hhead with hblock
    have h1 : entryLabel = "b0" := (congrArg Block.label hblock).symm
    subst h1
    simp only [M_new_lenv, AssocMap.insert, AssocMap.lookup] at hlookup
    injection hlookup with heq
    rw [← heq]
    unfold TypeEnv.equiv
    refine ⟨rfl, rfl, rfl, ?_⟩
    intros; rfl
  · -- Every block must type check
    intro block hmem blockEnv hlookup
    simp only [M_new, List.mem_singleton] at hmem
    subst hmem
    simp only [M_new_lenv, AssocMap.insert, AssocMap.lookup] at hlookup
    injection hlookup with heq
    subst heq
    unfold typecheck_block

    -- Define intermediate environments
    -- After let s0 = move(g): s0 has type .basic .tint, g is invalidated
    let env1 : TypeEnv := {
      siteEnv := AssocMap.insert M_new_initEnv.siteEnv s0 (.basic .tint)
      varEnv := AssocMap.update M_new_initEnv.varEnv var_g (.invalidVar, .basic .tint, .mutable)
      pathEnv := M_new_initEnv.pathEnv
      funEnv := M_new_initEnv.funEnv
    }

    -- After let s1 = pack T{f: s0}: s0 is consumed, s1 has the record type
    let midEnv : TypeEnv := {
      siteEnv := AssocMap.insert (AssocMap.deleteAll env1.siteEnv [s0]) s1 M_T
      varEnv := env1.varEnv
      pathEnv := env1.pathEnv
      funEnv := env1.funEnv
    }

    exists midEnv
    constructor
    · -- typecheck_stmt for body
      apply typecheck_stmt.seq (env' := env1)
      · -- let s0 = move(g)
        apply typecheck_stmt.let_bind
        apply typecheck_expr.usage
        apply typecheck_usage.t_umove (τ := .basic .tint) (ms := .mutable)
        · rfl  -- lookup varEnv var_g
        · -- not_borrowed var_g
          unfold not_borrowed
          intro r
          simp only [M_new_initEnv, PathEnv.init]
          split
          · simp only [Regex.interpret_regex]; intro h; cases h
          · simp only [Regex.interpret_regex]; exact id
        · rfl  -- notIn siteEnv s0
        · rfl  -- env' = env1
      · -- let s1 = pack T{f: s0}
        apply typecheck_stmt.let_bind
        apply typecheck_expr.pack (fentries := AssocMap.insert AssocMap.empty field_f .tint)
        · rfl  -- s1 not in env1.siteEnv
        · -- All field sites exist with correct types
          intro f a hmem
          simp at hmem
          obtain ⟨hf, ha⟩ := hmem
          subst hf ha
          exists .tint
        · -- All field sites distinct
          intro a1 a2 hexists
          obtain ⟨f1, f2, h1, h2, hne⟩ := hexists
          simp at h1 h2
          have hf1 : f1 = field_f := h1.1
          have hf2 : f2 = field_f := h2.1
          rw [hf1, hf2] at hne
          exact absurd rfl hne
        · rfl  -- env' = midEnv
    · -- typecheck_terminator for ret [s1]
      apply typecheck_terminator.t_ret
      · -- All return sites have correct type
        intro a ha
        simp only [List.mem_singleton] at ha
        subst ha
        rfl
      · -- no_locals_borrowed
        unfold no_locals_borrowed not_borrowed
        intro x v hmem r
        simp only [midEnv, env1, M_new_initEnv, PathEnv.init]
        split
        · simp only [Regex.interpret_regex]; intro h; cases h
        · simp only [Regex.interpret_regex]; exact id

end LeanMove.Examples
