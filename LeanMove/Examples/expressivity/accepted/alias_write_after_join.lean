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
import LeanMove.Checker.Algorithmic.TypeCheckingAlgorithmic
import LeanMove.Checker.Algorithmic.AlgorithmicTypingSoundness
import LeanMove.Lang.Macros

/-!
# Alias Write After Join

Source: https://github.com/tnowacki/sui/blob/example-tests/external-crates/move/crates/bytecode-verifier-transactional-tests/tests/reference_safety/expressivity/alias_write_after_join.mvir

Original Move IR:
```
module 0x2.alias_after_join_reborrow {
  t(cond: bool) {
    let a: u64;
    let b: u64;
    let x: &mut u64;
    let y: &mut u64;
    let z: &mut u64;
  label l0:
    a = 0;
    b = 0;
    jump_if (move(cond)) l2;
  label l1:
    x = &mut a;
    y = &mut b;
    jump l3;
  label l2:
    x = &mut b;
    y = &mut a;
    jump l3;
  label l3:
    z = &mut a;
    *move(z) = 0;
    *move(x) = 0;
    *move(y) = 0;
    return;
  }
}
```

This test demonstrates that writing through aliased mutable references is safe
after control flow joins, because all writes release the reference.
-/

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Checker
open AssocMap
open Regex

namespace LeanMove.Examples.Expressivity.AliasWriteAfterJoin

-- Variables
def var_a : Var := ⟨"a"⟩
def var_b : Var := ⟨"b"⟩
def var_x : Var := ⟨"x"⟩
def var_y : Var := ⟨"y"⟩
def var_z : Var := ⟨"z"⟩
def var_cond : Var := ⟨"cond"⟩

-- Sites (temporaries in A-normal form)
def s0 : Site := .site 0   -- integer literal 0 for a
def s1 : Site := .site 1   -- integer literal 0 for b
def s2 : Site := .site 2   -- move(cond)
def s3 : Site := .site 3   -- &mut a or &mut b (for x)
def s4 : Site := .site 4   -- &mut b or &mut a (for y)
def s5 : Site := .site 5   -- &mut a (for z)
def s6 : Site := .site 6   -- move(z)
def s7 : Site := .site 7   -- integer literal 0 for first write
def s8 : Site := .site 8   -- move(x)
def s9 : Site := .site 9   -- integer literal 0 for second write
def s10 : Site := .site 10 -- move(y)
def s11 : Site := .site 11 -- integer literal 0 for third write

/-
  Function t(cond: bool) translated to MoveLight AST
-/
def t : FunDef := {
  params := [(var_cond, .basic .tbool)]
  returnType := .basic .tunit
  locals := [
    { name := var_a, type := .basic .u64 },
    { name := var_b, type := .basic .u64 },
    { name := var_x, type := .ref .u64 (.refid 1) .siteBorrowMut },
    { name := var_y, type := .ref .u64 (.refid 42) .siteBorrowMut },
    { name := var_z, type := .ref .u64 (.refid 3) .siteBorrowMut }
  ]
  blocks := [
    -- label l0: a = 0; b = 0; branch on cond
    { label := "l0"
      body :=
        (letsite s0 ← #0) ;;            -- s0 = 0 (integer literal)
        (var_a ::= s0) ;;               -- a = s0
        (letsite s1 ← #0) ;;            -- s1 = 0 (integer literal)
        (var_b ::= s1) ;;               -- b = s1
        (letsite s2 ← move var_cond) ;; -- s2 = move(cond)
        Stmt.branch s2 "l2" "l1"
    },
    -- label l1 (false branch): x = &mut a; y = &mut b; jump l3
    { label := "l1"
      body :=
        (letsite s3 ← &mut var_a) ;;    -- s3 = &mut a
        (var_x ::= s3) ;;               -- x = s3
        (letsite s4 ← &mut var_b) ;;    -- s4 = &mut b
        (var_y ::= s4) ;;               -- y = s4
        Stmt.jump "l3"
    },
    -- label l2 (true branch): x = &mut b; y = &mut a; jump l3
    { label := "l2"
      body :=
        (letsite s3 ← &mut var_b) ;;    -- s3 = &mut b
        (var_x ::= s3) ;;               -- x = s3
        (letsite s4 ← &mut var_a) ;;    -- s4 = &mut a
        (var_y ::= s4) ;;               -- y = s4
        Stmt.jump "l3"
    },
    -- label l3: z = &mut a; writes; return
    { label := "l3"
      body :=
        (letsite s5 ← &mut var_a) ;;    -- s5 = &mut a
        (var_z ::= s5) ;;               -- z = s5
        (letsite s6 ← move var_z) ;;    -- s6 = move(z)
        (letsite s7 ← #0) ;;            -- s7 = 0 (integer literal)
        Stmt.writeRef s6 s7 ;;          -- *s6 = s7
        (letsite s8 ← move var_x) ;;    -- s8 = move(x)
        (letsite s9 ← #0) ;;            -- s9 = 0 (integer literal)
        Stmt.writeRef s8 s9 ;;          -- *s8 = s9
        (letsite s10 ← move var_y) ;;   -- s10 = move(y)
        (letsite s11 ← #0) ;;           -- s11 = 0 (integer literal)
        Stmt.writeRef s10 s11 ;;        -- *s10 = s11
        Stmt.ret []                     -- return
    }
  ]
}

-- Abbreviations for path elements and refs
def rta : PathElement := .root_to_var var_a
def rtb : PathElement := .root_to_var var_b
def r1 : Aref := .refid 1
def r2 : Aref := .refid 2

-- VarEnv at l1/l2 entry (after l0: a,b assigned, cond consumed)
def t_branch_varEnv : VarEnv :=
  let ve := init_fun_varEnv t
  let ve := update ve var_a (.validVar, .basic .u64, .mutable)
  let ve := update ve var_b (.validVar, .basic .u64, .mutable)
  update ve var_cond (.invalidVar, .basic .tbool, .mutable)

-- Environment at l1/l2 entry
def t_branch_env : TypeEnv := {
  siteEnv := AssocMap.empty
  varEnv := t_branch_varEnv
  pathEnv := PathEnv.init
  funEnv := AssocMap.empty
}

-- VarEnv at l3 entry (x and y now valid refs)
def t_l3_varEnv : VarEnv :=
  let ve := t_branch_varEnv
  let ve := update ve var_x (.validVar, .ref .u64 r1 .siteBorrowMut, .mutable)
  update ve var_y (.validVar, .ref .u64 r2 .siteBorrowMut, .mutable)

-- Environment at l3 entry (join of l1 and l2 with union paths)
def t_l3_env : TypeEnv := {
  siteEnv := AssocMap.empty
  varEnv := t_l3_varEnv
  pathEnv := {
    refs := [r2, r1, .root]
    paths := fun (u, v) =>
      if u == .root && v == .root then .ε
      else if u == r1 && v == r1 then .ε
      else if u == r2 && v == r2 then .ε
      else if u == .root && v == r1 then (.ε ⬝ ⌜rta⌝) ∣ (.ε ⬝ ⌜rtb⌝)
      else if u == .root && v == r2 then (.ε ⬝ ⌜rtb⌝) ∣ (.ε ⬝ ⌜rta⌝)
      else if u == r1 && v == .root then (∂[rta] .ε) ∣ (∂[rtb] .ε)
      else if u == r2 && v == .root then (∂[rtb] .ε) ∣ (∂[rta] .ε)
      else if u == r1 && v == r2 then ((∂[rta] .ε) ⬝ ⌜rtb⌝) ∣ ((∂[rtb] .ε) ⬝ ⌜rta⌝)
      else if u == r2 && v == r1 then (∂[rtb] (.ε ⬝ ⌜rta⌝)) ∣ (∂[rta] (.ε ⬝ ⌜rtb⌝))
      else .empty
  }
  funEnv := AssocMap.empty
}

-- Label environment
def t_lenv : LabelEnv :=
  insert (insert (insert (insert AssocMap.empty
    "l0" { siteEnv := AssocMap.empty
           varEnv := init_fun_varEnv t
           pathEnv := PathEnv.init
           funEnv := AssocMap.empty })
    "l1" t_branch_env)
    "l2" t_branch_env)
    "l3" t_l3_env

-- Initial environment (for entry block check)
def t_initEnv : TypeEnv := {
  siteEnv := AssocMap.empty, varEnv := init_fun_varEnv t,
  pathEnv := PathEnv.init, funEnv := AssocMap.empty }

-- Debug: step-by-step type checking of l1 body (incremental prefix checks)
#eval (check_stmt t_lenv t_branch_env  -- Step 1: borrow a
  (Stmt.letBind s3 (Expr.usage (Usage.borrowMut var_a)) Stmt.skip)
  (.basic .tunit)).isSome
#eval (check_stmt t_lenv t_branch_env  -- Step 2: borrow a + assign x
  (Stmt.letBind s3 (Expr.usage (Usage.borrowMut var_a))
    (Stmt.assign var_x s3 Stmt.skip))
  (.basic .tunit)).isSome
#eval (check_stmt t_lenv t_branch_env  -- Step 3: + borrow b
  (Stmt.letBind s3 (Expr.usage (Usage.borrowMut var_a))
    (Stmt.assign var_x s3
      (Stmt.letBind s4 (Expr.usage (Usage.borrowMut var_b)) Stmt.skip)))
  (.basic .tunit)).isSome
#eval (check_stmt t_lenv t_branch_env  -- Step 4: + assign y
  (Stmt.letBind s3 (Expr.usage (Usage.borrowMut var_a))
    (Stmt.assign var_x s3
      (Stmt.letBind s4 (Expr.usage (Usage.borrowMut var_b))
        (Stmt.assign var_y s4 Stmt.skip))))
  (.basic .tunit)).isSome
#eval (check_stmt t_lenv t_branch_env  -- Step 5: full l1 body with jump
  (Stmt.letBind s3 (Expr.usage (Usage.borrowMut var_a))
    (Stmt.assign var_x s3
      (Stmt.letBind s4 (Expr.usage (Usage.borrowMut var_b))
        (Stmt.assign var_y s4
          (Stmt.jump "l3")))))
  (.basic .tunit)).isSome

-- Debug: check_fun components
#eval (lookup t_lenv "l0").isSome                  -- entry label found in lenv
#eval TypeEnv.equiv_bool t_initEnv t_initEnv       -- initEnv self-equiv
#eval do                                            -- entry env ≡ initEnv
  let entryEnv ← lookup t_lenv "l0"
  return TypeEnv.equiv_bool entryEnv t_initEnv

-- Debug: per-block check via lenv lookup (as in check_fun)
#eval t.blocks.map fun block =>
  (block.label, match lookup t_lenv block.label with
  | some blockEnv => check_block t_lenv block blockEnv t.returnType
  | none => false)

-- Full function check
#eval check_fun t t_lenv

-- Theorem: t is well-typed (algorithmic)
theorem t_check : check_fun t t_lenv = true := by rfl

-- -----------------------------------------------------
-- -           Relational Type Checking Theorems      --
-- -----------------------------------------------------

-- Helper: init_fun_varEnv for t has fresh refs
private lemma t_varEnv_fresh :
    VarEnv.RefsAreFresh (init_fun_varEnv t) := by
  unfold init_fun_varEnv add_locals_to_varEnv init_varEnv_from_params
  simp only [t, List.foldl]
  apply VarEnv.insert_refs_are_fresh
  · apply VarEnv.insert_refs_are_fresh
    · apply VarEnv.insert_refs_are_fresh
      · apply VarEnv.insert_refs_are_fresh
        · apply VarEnv.insert_refs_are_fresh
          · apply VarEnv.insert_refs_are_fresh
            · exact VarEnv.empty_refs_are_fresh
            · trivial
          · trivial
        · trivial
      · exact ⟨1, rfl⟩
    · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

-- Helper: t_branch_varEnv has fresh refs (updates only basic types)
private lemma t_branch_varEnv_fresh :
    VarEnv.RefsAreFresh t_branch_varEnv := by
  unfold t_branch_varEnv
  -- update preserves RefsAreFresh when the new entry has a basic type
  apply VarEnv.insert_refs_are_fresh
  · apply VarEnv.insert_refs_are_fresh
    · apply VarEnv.insert_refs_are_fresh
      · exact t_varEnv_fresh
      · trivial
    · trivial
  · trivial

-- Helper: t_l3_varEnv has fresh refs
private lemma t_l3_varEnv_fresh :
    VarEnv.RefsAreFresh t_l3_varEnv := by
  unfold t_l3_varEnv r1 r2
  apply VarEnv.insert_refs_are_fresh
  · apply VarEnv.insert_refs_are_fresh
    · exact t_branch_varEnv_fresh
    · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩

-- Helper: t_l3_env's pathEnv is well-formed
private lemma t_l3_pathEnv_wf : PathEnv.WellFormed t_l3_env.pathEnv := by
  constructor
  · -- refs_complete: ∀ r, r ∉ refs → paths(.root, r) = .empty
    intro r hr
    simp only [t_l3_env, r1, r2, List.mem_cons, not_or] at hr
    obtain ⟨hr2, hr1, hroot, _⟩ := hr
    -- The paths function returns .empty when r ∉ {.root, .refid 1, .refid 2}
    simp [t_l3_env, r1, r2, rta, rtb, hroot, hr1, hr2]
  · -- varref_tracked: no .varRef in refs, so vacuously true
    intro x hx
    simp only [t_l3_env, r1, r2, List.mem_cons] at hx
    rcases hx with h | h | h | h
    · exact Aref.noConfusion h
    · exact Aref.noConfusion h
    · exact Aref.noConfusion h
    · nomatch h

-- Helper: t_l3_env is well-formed
private lemma t_l3_env_wellformed : TypeEnv.WellFormed t_l3_env :=
  ⟨t_l3_pathEnv_wf, SiteEnv.empty_refs_not_root, t_l3_varEnv_fresh⟩

-- All envs in t_lenv are well-formed
private lemma t_lenv_wf :
    ∀ l env, lookup t_lenv l = some env → TypeEnv.WellFormed env := by
  intro l env hlookup
  by_cases hl3 : l = "l3"
  · subst hl3
    have h : lookup t_lenv "l3" = some t_l3_env := by rfl
    rw [h] at hlookup; injection hlookup with heq; subst heq
    exact t_l3_env_wellformed
  · by_cases hl2 : l = "l2"
    · subst hl2
      have h : lookup t_lenv "l2" = some t_branch_env := by rfl
      rw [h] at hlookup; injection hlookup with heq; subst heq
      exact TypeEnv.init_wellformed _ _ t_branch_varEnv_fresh
    · by_cases hl1 : l = "l1"
      · subst hl1
        have h : lookup t_lenv "l1" = some t_branch_env := by rfl
        rw [h] at hlookup; injection hlookup with heq; subst heq
        exact TypeEnv.init_wellformed _ _ t_branch_varEnv_fresh
      · by_cases hl0 : l = "l0"
        · subst hl0
          have h : lookup t_lenv "l0" = some t_initEnv := by rfl
          rw [h] at hlookup; injection hlookup with heq; subst heq
          exact TypeEnv.init_wellformed _ _ t_varEnv_fresh
        · exfalso
          simp only [t_lenv, AssocMap.insert, AssocMap.empty, AssocMap.lookup,
                     List.filter, List.lookup] at hlookup
          have h3 : (l == "l3") = false := by
            cases h : l == "l3"
            · rfl
            · exact absurd (eq_of_beq h) hl3
          have h2 : (l == "l2") = false := by
            cases h : l == "l2"
            · rfl
            · exact absurd (eq_of_beq h) hl2
          have h1 : (l == "l1") = false := by
            cases h : l == "l1"
            · rfl
            · exact absurd (eq_of_beq h) hl1
          have h0 : (l == "l0") = false := by
            cases h : l == "l0"
            · rfl
            · exact absurd (eq_of_beq h) hl0
          simp [h3, h2, h1, h0, List.lookup] at hlookup

-- Main theorem: t is well-typed (relational)
theorem t_welltyped : ∃ lenv, typecheck_fun t lenv :=
  ⟨_, check_fun_sound _ _ t_lenv_wf t_check⟩

end LeanMove.Examples.Expressivity.AliasWriteAfterJoin
