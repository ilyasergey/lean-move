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
import LeanMove.Examples.Macros

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
        .letBind s1 (.pack "T" [(field_f, s0)]) ;; -- let s1 = T{f: s0}
        .ret [s1]                                  -- return s1
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
        (letsite s0 ← move var_this) ;;              -- let s0 = move(this)
        .letBind s1 (.borrowField s0 M_T_basic field_f) ;; -- let s1 = &s0.T::f
        .letBind s2 (.readRef s1) ;;                 -- let s2 = *s1
        (var_y ::= s2) ;;                            -- y = s2
        .ret []                                      -- return
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
        .call [s0] "M.new" [] ;;
        (var_x ::= s0) ;;
        -- x_ref = &x (in A-normal form: borrow then assign)
        (letsite s1 ← &var_x) ;;
        (var_x_ref ::= s1) ;;
        -- M.t(move(x_ref)) (in A-normal form: move then call)
        (letsite s2 ← move var_x_ref) ;;
        .call [] "M.t" [s2] ;;
        -- return
        .ret []
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
  all_goals try aesop
  -- Goal: M_new.blocks ≠ []
  { unfold M_new at a; aesop }
  -- Goal: Entry block environment equivalence
  {
    move: a=>//=
    scase: (M_new.blocks.head?) =>//=[] l b
    scase
    srw M_new_lenv at a_1
    move: (lookup_some _ _ _ a_1)=>//=
    srw M_new_initEnv=>//=
    simp [AssocMap.insert]; scase=>//
    scase
    sby simp [empty]
  }
  -- Goal: Each block type-checks
  {
    scase: idx a a_1=>//=
    dsimp [M_new] at * =>//==<- {block}=>//=
    srw M_new_lenv M_new_initEnv=>//= /lookup_some=>//=
    simp [AssocMap.insert]=>->

    -- Build the output environment step by step, following the typing rules exactly

    -- After let s0 = move(g): s0 has type .basic .tint, g is invalidated
    let env1 : TypeEnv := {
      siteEnv := AssocMap.insert M_new_initEnv.siteEnv s0 (.basic .tint)
      varEnv := AssocMap.update M_new_initEnv.varEnv var_g (.invalidVar, .basic .tint, .mutable)
      pathEnv := M_new_initEnv.pathEnv
      funEnv := M_new_initEnv.funEnv
    }

    -- After let s1 = pack T{f: s0}: s0 is consumed, s1 has the record type
    let env2 : TypeEnv := {
      siteEnv := AssocMap.insert (AssocMap.deleteAll env1.siteEnv [s0]) s1 M_T
      varEnv := env1.varEnv
      pathEnv := env1.pathEnv
      funEnv := env1.funEnv
    }

    -- After ret [s1]: only s1 remains in siteEnv
    let env_final : TypeEnv := {
      siteEnv := AssocMap.insert AssocMap.empty s1 M_T
      varEnv := env2.varEnv
      pathEnv := env2.pathEnv
      funEnv := env2.funEnv
    }

    exists env_final
    constructor
    · -- typecheck_block: prove the body type-checks
      apply typecheck_stmt.seq (env' := env1)
      · -- First statement: let s0 = move(g)
        apply typecheck_stmt.let_bind
        apply typecheck_expr.usage
        apply typecheck_usage.t_umove (τ := .basic .tint) (ms := .mutable)
        · -- lookup M_new_initEnv.varEnv var_g = some (validVar, .basic .tint, mutable)
          rfl
        · -- not_borrowed var_g M_new_initEnv
          -- PathEnv.init has paths (.root, r) = if .root = r then ε else empty
          -- ε only matches [], empty matches nothing
          unfold not_borrowed
          intro r
          simp only [PathEnv.init]
          -- Goal: ¬ interpret_regex (if .root = r then ε else empty) [.root_to_var var_g]
          split
          · -- r = root: regex is ε, only accepts []
            simp only [Regex.interpret_regex]
            -- Goal: ¬ ([.root_to_var var_g] = [])
            intro h; cases h
          · -- r ≠ root: regex is empty, accepts nothing
            simp only [Regex.interpret_regex]
            -- Goal: ¬ False
            exact id
        · -- s0 not in siteEnv
          rfl
        · -- env' = env1
          rfl
      · -- Remaining: seq (let s1 = pack) (ret [s1])
        apply typecheck_stmt.seq (env' := env2)
        · -- let s1 = pack T{f: s0}
          apply typecheck_stmt.let_bind
          apply typecheck_expr.pack (fentries := AssocMap.insert AssocMap.empty field_f .tint)
          · -- s1 not in env1.siteEnv
            rfl
          · -- All field sites exist with correct types
            intro f a hmem
            -- fields = [(field_f, s0)]
            simp at hmem
            obtain ⟨hf, ha⟩ := hmem
            subst hf ha
            -- Prove: ∃ bt, lookup env1.siteEnv s0 = some (.basic bt) ∧ lookup fentries field_f = some bt
            exists .tint
          · -- All field sites distinct (vacuously true: only one field)
            intro a1 a2 hexists
            -- hexists: ∃ f1 f2, (f1, a1) ∈ fields ∧ (f2, a2) ∈ fields ∧ f1 ≠ f2
            -- But fields = [(field_f, s0)], so both f1 and f2 must equal field_f
            obtain ⟨f1, f2, h1, h2, hne⟩ := hexists
            simp at h1 h2
            -- h1: f1 = field_f ∧ a1 = s0
            -- h2: f2 = field_f ∧ a2 = s0
            have : f1 = field_f := h1.1
            have : f2 = field_f := h2.1
            -- This contradicts hne: f1 ≠ f2
            subst_vars
            contradiction
          · -- env' = env2
            rfl
        · -- ret [s1]
          apply typecheck_stmt.return (fnName := "M.new") (params := [⟨.tint, none⟩]) (rets := [⟨M_T_basic, none⟩])
          · -- lookup env2.funEnv "M.new" = some ⟨params, rets⟩
            rfl
          · -- types_confrom env2.siteEnv [s1] [⟨M_T_basic, none⟩]
            -- types_confrom checks that each site has the matching type
            -- s1 has type M_T = .basic M_T_basic, and the param type is ⟨M_T_basic, none⟩
            unfold types_confrom
            constructor
            · rfl  -- M_T_basic = M_T_basic
            · trivial  -- types_confrom [] [] = True
          · -- check_mutable_inputs_isolated env2 [s1]
            -- s1 has basic type M_T, not a ref type, so vacuously true
            -- The hypothesis requires mi_site to have a ref type with siteBorrowMut
            -- but env2.siteEnv only maps s1 → M_T (basic type)
            unfold check_mutable_inputs_isolated
            intro mi_site hmi mi_bt mi_ref hlookup other_site hother other_bt other_ref bk hlookup_other hne
            simp only [List.mem_singleton] at hmi
            subst hmi
            -- hlookup: lookup env2.siteEnv s1 = some (.ref mi_bt mi_ref .siteBorrowMut)
            -- But env2.siteEnv[s1] = M_T = .basic M_T_basic
            have henv2_s1 : AssocMap.lookup env2.siteEnv s1 = some M_T := by rfl
            rw [henv2_s1] at hlookup
            -- hlookup: some M_T = some (.ref mi_bt mi_ref .siteBorrowMut)
            -- M_T is .basic, not .ref, so this is a contradiction
            simp only [M_T] at hlookup
            -- Now hlookup: some (.basic M_T_basic) = some (.ref ...), which is absurd
            cases hlookup
          · -- no_locals_borrowed env2
            -- M_new has no locals (only parameter var_g)
            -- PathEnv.init has no non-trivial paths, so not_borrowed holds for all vars
            unfold no_locals_borrowed not_borrowed
            intro x v hmem r
            simp only [env2, env1, M_new_initEnv, PathEnv.init]
            -- Goal: ¬ interpret_regex (if .root = r then ε else empty) [.root_to_var x]
            split
            · -- r = root: regex is ε, only accepts []
              simp only [Regex.interpret_regex]
              intro h; cases h
            · -- r ≠ root: regex is empty, accepts nothing
              simp only [Regex.interpret_regex]
              exact id
          · -- env' = env_final (environment cleanup)
            rfl
    · -- next block: none exists
      intro nextLabel nextEnv hnext _
      simp [next_block_label] at hnext
  }
  { sdone }

end LeanMove.Examples
