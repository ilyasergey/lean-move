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
import LeanMove.Checker.TypeCheckingAlgorithmic
import LeanMove.Lang.Macros

-- -----------------------------------------------------
-- -       Example: Basic Move IR Translation        --
-- -----------------------------------------------------

/-
Source:

https://github.com/MystenLabs/sui/blob/main/external-crates/move/crates/bytecode-verifier-transactional-tests/tests/reference_safety/deref_borrow_field_ok.mvir

 -/

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
  returnType := M_T
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

-- Initial environment for M.new: parameter g is a valid mutable int variable
def M_new_initEnv : TypeEnv := {
  siteEnv := AssocMap.empty
  varEnv := init_varEnv_from_params [(var_g, .basic .u64)]
  pathEnv := PathEnv.init
  funEnv := module_funEnv
}

-- LabelEnv for M.new: maps "b0" to the initial environment
def M_new_lenv : LabelEnv :=
  AssocMap.insert AssocMap.empty "b0" M_new_initEnv

-- Test theorem 1
theorem M_new_check: check_fun M_new M_new_lenv := by rfl

-- Theorem: M.new is well-typed
theorem M_new_welltyped : ∃ lenv, typecheck_fun M_new lenv := by
  exists M_new_lenv
  apply typecheck_fun.fun_ok (initEnv := M_new_initEnv)
  · rfl  -- initEnv.varEnv
  · rfl  -- initEnv.siteEnv
  · rfl  -- initEnv.pathEnv
  · simp only [M_new]; intro h; exact List.noConfusion h  -- blocks ≠ []
  · -- Entry block environment equivalence (now 2-tuple Block)
    intro entryLabel entryBody entryEnv hhead hlookup
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

    -- Body: letBind s0 (move g) (letBind s1 (pack ...) (ret [s1]))
    -- Type check follows CPS structure: let_bind_move -> let_bind_pack -> ret
    apply typecheck_stmt.let_bind_move
    · rfl  -- lookup varEnv var_g
    · -- not_borrowed var_g env
      unfold not_borrowed
      intro r
      simp only [M_new_initEnv, PathEnv.init]
      split
      · simp only [Regex.interpret_regex]; intro h; cases h
      · simp only [Regex.interpret_regex]; exact id
    · rfl  -- notIn siteEnv s0
    · -- continuation: letBind s1 (pack ...) (ret [s1])
      apply typecheck_stmt.let_bind_pack (fentries := AssocMap.insert AssocMap.empty field_f .u64)
      · rfl  -- s1 not in env1.siteEnv
      · -- All field sites exist with correct types
        intro f a hmem
        simp at hmem
        obtain ⟨hf, ha⟩ := hmem
        subst hf ha
        exists .u64
      · -- All field sites distinct
        intro a1 a2 hexists
        obtain ⟨f1, f2, h1, h2, hne⟩ := hexists
        simp at h1 h2
        have hf1 : f1 = field_f := h1.1
        have hf2 : f2 = field_f := h2.1
        rw [hf1, hf2] at hne
        exact absurd rfl hne
      · -- continuation: ret [s1]
        apply typecheck_stmt.ret
        · -- All return sites have correct type
          intro a ha
          simp only [List.mem_singleton] at ha
          subst ha
          rfl
        · -- no_locals_borrowed
          unfold no_locals_borrowed not_borrowed
          intro x v hmem r
          simp only [M_new_initEnv, PathEnv.init]
          split
          · simp only [Regex.interpret_regex]; intro h; cases h
          · simp only [Regex.interpret_regex]; exact id

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
  params := [(var_this, .ref M_T_basic (.varRef var_this) .siteBorrowImm)]
  returnType := .basic .tunit
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

-- Initial environment for M_t: parameter this is a valid immutable ref, local y is invalid
def M_t_initEnv : TypeEnv := {
  siteEnv := AssocMap.empty
  varEnv := init_fun_varEnv M_t
  pathEnv := PathEnv.init
  funEnv := module_funEnv
}

-- LabelEnv for M_t: maps "b0" to the initial environment
def M_t_lenv : LabelEnv :=
  AssocMap.insert AssocMap.empty "b0" M_t_initEnv

-- Test theorem 2
theorem M_t_check: check_fun M_t M_t_lenv := by rfl

-- Theorem: M_t is well-typed
theorem M_t_welltyped : ∃ lenv, typecheck_fun M_t lenv := by
  exists M_t_lenv
  apply typecheck_fun.fun_ok (initEnv := M_t_initEnv)
  · rfl  -- initEnv.varEnv = init_fun_varEnv M_t
  · rfl  -- initEnv.siteEnv = empty
  · rfl  -- initEnv.pathEnv = PathEnv.init
  · simp only [M_t]; intro h; exact List.noConfusion h  -- blocks ≠ []
  · -- Entry block environment equivalence
    intro entryLabel entryBody entryEnv hhead hlookup
    simp only [M_t, List.head?] at hhead
    injection hhead with hblock
    have h1 : entryLabel = "b0" := (congrArg Block.label hblock).symm
    subst h1
    simp only [M_t_lenv, AssocMap.insert, AssocMap.lookup] at hlookup
    injection hlookup with heq
    rw [← heq]
    unfold TypeEnv.equiv
    refine ⟨rfl, rfl, rfl, ?_⟩
    intros; rfl
  · -- Every block must type check
    intro block hmem blockEnv hlookup
    simp only [M_t, List.mem_singleton] at hmem
    subst hmem
    simp only [M_t_lenv, AssocMap.insert, AssocMap.lookup] at hlookup
    injection hlookup with heq
    subst heq
    unfold typecheck_block

    -- Step 1: let s0 = move(this)
    apply typecheck_stmt.let_bind_move
    · rfl  -- lookup varEnv var_this
    · -- not_borrowed var_this
      unfold not_borrowed
      intro r
      simp only [M_t_initEnv, PathEnv.init]
      split
      · simp only [Regex.interpret_regex]; intro h; cases h
      · simp only [Regex.interpret_regex]; exact id
    · rfl  -- notIn siteEnv s0
    · -- Step 2: let s1 = &s0.T::f (borrowField)
      apply typecheck_stmt.let_bind_borrowField (rf := .refid 0)
                   (fentries := AssocMap.insert AssocMap.empty field_f .u64)
      · rfl  -- lookup siteEnv s0
      · rfl  -- M_T_basic = .trecord fentries
      · rfl  -- lookup fentries field_f = some .u64
      · rfl  -- notIn siteEnv s1
      · -- freshRef (.refid 0) env.pathEnv
        simp [freshRef, M_t_initEnv, PathEnv.init]
      · -- Step 3: let s2 = *s1 (readRef)
        apply typecheck_stmt.let_bind_readRef
        · rfl  -- lookup siteEnv s1
        · rfl  -- notIn siteEnv s2
        · -- Step 4: y = s2 (var_assign_invalid)
          apply typecheck_stmt.var_assign_invalid
          · rfl  -- lookup varEnv var_y
          · rfl  -- lookup siteEnv s2
          · -- Step 5: ret []
            apply typecheck_stmt.ret
            · -- All return sites have correct type (vacuous)
              intro a ha
              cases ha
            · -- no_locals_borrowed
              unfold no_locals_borrowed not_borrowed
              intro x v hmem r
              simp only [delete_ref_node,
                          update_with_extension,
                          Regex.extend, Regex.der, List.foldl]
              split_ifs <;>
                simp_all [Regex.interpret_regex, var_this, var_y,
                          M_t_initEnv, PathEnv.init]
              -- remaining goal: reversed equality in if-condition
              split_ifs <;> simp_all [Regex.interpret_regex]

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
      M.t(move(x_ref));    // move x_ref into s2, call M.t
      release(s2);         // release borrow before returning
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
        -- x = T{f: 2} (M.new inlined: literal, pack, assign)
        (letsite s3 ← #2) ;;                                    -- let s3 = 2
        (letsite s0 ← pack("T", [(field_f, s3)])) ;;            -- let s0 = T{f: s3}
        (var_x ::= s0) ;;                                       -- x = s0
        -- x_ref = &x (in A-normal form: borrow then assign)
        (letsite s1 ← &var_x) ;;                                -- let s1 = &x
        (var_x_ref ::= s1) ;;                                   -- x_ref = s1
        -- M.t(move(x_ref)) (in A-normal form: move then call)
        (letsite s2 ← move var_x_ref) ;;                        -- let s2 = move(x_ref)
        (call([], "M.t", [s2])) ;;                              -- M.t(s2)
        (release s2) ;;                                         -- release borrow
        ret []                                                   -- return
    }
  ]
}

-- Initial environment for foo: no params, locals x and x_ref
def foo_initEnv : TypeEnv := {
  siteEnv := AssocMap.empty
  varEnv := init_fun_varEnv foo
  pathEnv := PathEnv.init
  funEnv := module_funEnv
}

-- LabelEnv for foo: maps "b0" to the initial environment
def foo_lenv : LabelEnv :=
  AssocMap.insert AssocMap.empty "b0" foo_initEnv

-- Test theorem 3
theorem foo_check: check_fun foo foo_lenv := by rfl

-- Theorem: foo is well-typed
theorem foo_welltyped : ∃ lenv, typecheck_fun foo lenv := by
  exists foo_lenv
  apply typecheck_fun.fun_ok (initEnv := foo_initEnv)
  · rfl  -- initEnv.varEnv = init_fun_varEnv foo
  · rfl  -- initEnv.siteEnv = empty
  · rfl  -- initEnv.pathEnv = PathEnv.init
  · simp only [foo]; intro h; exact List.noConfusion h  -- blocks ≠ []
  · -- Entry block environment equivalence
    intro entryLabel entryBody entryEnv hhead hlookup
    simp only [foo, List.head?] at hhead
    injection hhead with hblock
    have h1 : entryLabel = "b0" := (congrArg Block.label hblock).symm
    subst h1
    simp only [foo_lenv, AssocMap.insert, AssocMap.lookup] at hlookup
    injection hlookup with heq
    rw [← heq]
    unfold TypeEnv.equiv
    refine ⟨rfl, rfl, rfl, ?_⟩
    intros; rfl
  · -- Every block must type check
    intro block hmem blockEnv hlookup
    simp only [foo, List.mem_singleton] at hmem
    subst hmem
    simp only [foo_lenv, AssocMap.insert, AssocMap.lookup] at hlookup
    injection hlookup with heq
    subst heq
    unfold typecheck_block

    -- Step 1: let s3 = 2
    apply typecheck_stmt.let_bind_intLit
    · rfl  -- notIn siteEnv s3
    · -- Step 2: let s0 = pack T{f: s3}
      apply typecheck_stmt.let_bind_pack (fentries := AssocMap.insert AssocMap.empty field_f .u64)
      · rfl  -- notIn siteEnv s0
      · -- All field sites have correct types
        intro f a hmem
        simp at hmem
        obtain ⟨hf, ha⟩ := hmem
        subst hf ha
        exists .u64
      · -- All field sites distinct
        intro a1 a2 hexists
        obtain ⟨f1, f2, h1, h2, hne⟩ := hexists
        simp at h1 h2
        have hf1 : f1 = field_f := h1.1
        have hf2 : f2 = field_f := h2.1
        rw [hf1, hf2] at hne
        exact absurd rfl hne
      · -- Step 3: var_x = s0
        apply typecheck_stmt.var_assign_invalid
        · rfl  -- lookup varEnv var_x
        · rfl  -- lookup siteEnv s0 = some M_T
        · -- Step 4: let s1 = &var_x
          apply typecheck_stmt.let_bind_borrowImm (r := Aref.varRef var_x)
          · rfl  -- lookup varEnv var_x = some (.validVar, .basic M_T_basic, .mutable)
          · rfl  -- notIn siteEnv s1
          · rfl  -- freshRefBool (.varRef var_x) pathEnv
          · -- Step 5: var_x_ref = s1
            apply typecheck_stmt.var_assign_invalid
            · rfl  -- lookup varEnv var_x_ref
            · rfl  -- lookup siteEnv s1
            · -- Step 6: let s2 = move(var_x_ref)
              apply typecheck_stmt.let_bind_move
              · rfl  -- lookup varEnv var_x_ref = some (.validVar, .ref ..., .mutable)
              · -- not_borrowed var_x_ref
                unfold not_borrowed
                intro r
                simp only [update_with_extension, update_with_epsilon,
                            Regex.extend, Regex.der, List.foldl, var_x]
                -- After argument order change: z = varRef var_x, x = .root
                -- paths(.root, r) depends on whether r = varRef var_x
                by_cases hr : r = Aref.varRef ⟨"x"⟩
                · -- r = varRef var_x: path is ε ∘ [.root_to_var var_x]
                  subst hr
                  -- Simplify the nested if conditions
                  simp only [foo_initEnv, PathEnv.init, Regex.extend]
                  -- The path becomes char(.root_to_var var_x) after simplification
                  simp only [var_x_ref, and_true]
                  intro ⟨w, hw⟩
                  obtain ⟨ax2, heq, hw', hax2⟩ := hw
                  -- hax2: interpret_regex (char (.root_to_var var_x)) ax2
                  simp only [Regex.interpret_regex] at hax2
                  subst hax2
                  -- heq: [.root_to_var var_x_ref] = w ++ [.root_to_var var_x]
                  -- hw': interpret_regex (nested if) w
                  -- The nested ifs simplify: Aref.root ≠ Aref.varRef ..., so the result is ε
                  split_ifs at hw' <;> simp_all [Regex.interpret_regex]
                · -- r ≠ varRef var_x
                  simp only [hr, ↓reduceIte, foo_initEnv, PathEnv.init]
                  split_ifs <;> simp_all [Regex.interpret_regex]
              · rfl  -- notIn siteEnv s2
              · -- Step 7: call M.t(s2)
                apply typecheck_stmt.call (params := [⟨M_T_basic, some false⟩]) (rets := [])
                · rfl  -- all_fresh_sites env []
                · rfl  -- lookup funEnv "M.t"
                · -- types_conform siteEnv [s2] [⟨M_T_basic, some false⟩]
                  exact ⟨rfl, trivial, trivial⟩
                · -- types_conform siteEnv [] []
                  trivial
                · -- check_mutable_inputs_isolated (s2 is immutable, vacuous)
                  intro mi_site hmi mi_bt mi_ref hlookup
                  simp only [List.mem_singleton] at hmi
                  subst hmi
                  simp only [AssocMap.lookup, AssocMap.insert, AssocMap.empty] at hlookup
                  exact absurd hlookup (by simp)
                · -- check_mutable_inputs_have_outbound (s2 is immutable, vacuous)
                  intro mi_site hmi mi_bt mi_ref hlookup
                  simp only [List.mem_singleton] at hmi
                  subst hmi
                  simp only [AssocMap.lookup, AssocMap.insert, AssocMap.empty] at hlookup
                  exact absurd hlookup (by simp)
                · -- Step 8: release s2
                  apply typecheck_stmt.release (τ := M_T_basic) (r := Aref.varRef var_x)
                                              (isBor := .siteBorrowImm)
                  · rfl  -- lookup siteEnv s2
                  · -- Step 9: ret []
                    apply typecheck_stmt.ret
                    · -- All return sites have correct type (vacuous)
                      intro a ha
                      cases ha
                    · -- no_locals_borrowed
                      unfold no_locals_borrowed not_borrowed
                      intro x v hmem r
                      simp only [call_connect_inputs_outputs,
                                  List.filterMap, List.foldl,
                                  delete_ref_node,
                                  update_with_extension, update_with_epsilon,
                                  Regex.extend, Regex.der]
                      split_ifs <;>
                        simp_all [Regex.interpret_regex, var_x_ref, var_x,
                                  foo_initEnv, PathEnv.init]
                      -- remaining goal: reversed equality in if-condition
                      split_ifs <;> simp_all [Regex.interpret_regex]

end LeanMove.Examples
