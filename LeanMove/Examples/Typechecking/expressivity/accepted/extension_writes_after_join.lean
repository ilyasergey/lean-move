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
import LeanMove.Typing.TypeChecking
import LeanMove.Typing.Algorithmic.TypeCheckingAlgorithmic
import LeanMove.Typing.Algorithmic.AlgorithmicTypingSoundness
import LeanMove.Lang.Macros

/-!
# Extension Writes After Join

Source: https://github.com/tnowacki/sui/blob/example-tests/external-crates/move/crates/bytecode-verifier-transactional-tests/tests/reference_safety/expressivity/extension_writes_after_join.mvir

This module demonstrates writing to extensions after a control flow join.

Original Move IR:
```
module 0x2.extension_after_join {

struct S has copy, drop, store { f: u64 }

t(cond: bool, a: &mut Self.S, b: &mut Self.S): &mut Self.S {
    let x: &mut Self.S;
    let y: &mut Self.S;
    let f: &mut u64;
label l0:
    jump_if (move(cond)) l2;
label l1:
    x = move(a);
    y = move(b);
    jump l3;
label l2:
    x = move(b);
    y = move(a);
    jump l3;
label l3:
    f = &mut copy(x).S::f;
    *copy(y) = S { f: *copy(f) };
    *copy(f) = 0;
    return move(y);
}

}
```

The algorithmic checker uses lookup-based (order-independent) AssocMap equivalence
to compare VarEnvs at jump targets. This allows l1 and l2 to perform moves in
different orders while still passing the subsumption check at `jump l3`.
-/

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Typing
open AssocMap
open Regex

namespace LeanMove.Examples.Expressivity.ExtensionWritesAfterJoin

-- Field for S struct
def field_f : Field := ⟨"f"⟩

-- S { f: u64 }
def s_entries : AssocMap Field BasicMoveType := insert empty field_f .u64

-- Variables
def var_cond : Var := ⟨"cond"⟩
def var_a : Var := ⟨"a"⟩
def var_b : Var := ⟨"b"⟩
def var_x : Var := ⟨"x"⟩
def var_y : Var := ⟨"y"⟩
def var_f : Var := ⟨"f"⟩

-- Sites
def s0 : Site := .site 0
def s1 : Site := .site 1
def s2 : Site := .site 2
def s3 : Site := .site 3
def s4 : Site := .site 4
def s5 : Site := .site 5
def s6 : Site := .site 6
def s7 : Site := .site 7
def s8 : Site := .site 8
def s9 : Site := .site 9
def s10 : Site := .site 10
def s11 : Site := .site 11
def s12 : Site := .site 12 -- move(y) for return
def s13 : Site := .site 13 -- integer literal 0 for write

-- Ref abbreviation: both params a and b use the same abstract ref
-- (needed because x is assigned from either a or b in different branches,
-- and the algorithmic checker requires exact type equality in assigns)
def r0 : Aref := .refid 0

/-
  Translation notes:
  - Both a and b have type &mut S with the same abstract ref .refid 0
    (needed because x is assigned from either a or b depending on branch)
  - l1: x = move(a), y = move(b) (original Move IR order)
  - l2: x = move(b), y = move(a) (original Move IR order)
  - l3: borrows x.f, writes to y (a struct pack), writes to f, returns y
-/
def t : FunDef := {
  params := [
    (var_cond, .basic .tbool),
    (var_a, .ref (.trecord s_entries) r0 .siteBorrowMut),
    (var_b, .ref (.trecord s_entries) r0 .siteBorrowMut)
  ]
  returnType := .ref (.trecord s_entries) r0 .siteBorrowMut
  locals := [
    { name := var_x, type := .ref (.trecord s_entries) r0 .siteBorrowMut },
    { name := var_y, type := .ref (.trecord s_entries) r0 .siteBorrowMut },
    { name := var_f, type := .ref .u64 (.refid 1) .siteBorrowMut }
  ]
  blocks := [
    -- l0: jump_if (move(cond)) l2;
    { label := "l0"
      body :=
        (letsite s0 ← move var_cond) ;;  -- s0 = move(cond)
        Stmt.branch s0 "l2" "l1"         -- if s0 then l2 else l1
    },
    -- l1 (false branch): x = move(a); y = move(b); jump l3;
    { label := "l1"
      body :=
        (letsite s1 ← move var_a) ;;     -- s1 = move(a)
        (var_x ::= s1) ;;                -- x = s1
        (letsite s2 ← move var_b) ;;     -- s2 = move(b)
        (var_y ::= s2) ;;                -- y = s2
        Stmt.jump "l3"
    },
    -- l2 (true branch): x = move(b); y = move(a); jump l3;
    { label := "l2"
      body :=
        (letsite s3 ← move var_b) ;;     -- s3 = move(b)
        (var_x ::= s3) ;;                -- x = s3
        (letsite s4 ← move var_a) ;;     -- s4 = move(a)
        (var_y ::= s4) ;;                -- y = s4
        Stmt.jump "l3"
    },
    -- l3: f = &mut copy(x).S::f; *copy(y) = S { f: *copy(f) }; *copy(f) = 0; return move(y);
    { label := "l3"
      body :=
        -- f = &mut copy(x).S::f
        (letsite s5 ← copy var_x) ;;
        Stmt.letBind s6 (Expr.borrowMutField s5 (.trecord s_entries) field_f) ;;
        (var_f ::= s6) ;;
        -- *copy(y) = S { f: *copy(f) }
        -- First read *copy(f), then pack into S, then write to *copy(y)
        (letsite s7 ← copy var_f) ;;
        Stmt.letBind s8 (Expr.readRef s7) ;;              -- s8 = *s7 (the value in f)
        Stmt.letBind s9 (Expr.pack "S" [(field_f, s8)]) ;; -- s9 = S { f: s8 }
        (letsite s10 ← copy var_y) ;;
        Stmt.writeRef s10 s9 ;;                           -- *s10 = s9 (write struct to y)
        -- *copy(f) = 0
        (letsite s11 ← copy var_f) ;;
        (letsite s13 ← #0) ;;                             -- s13 = 0 (integer literal)
        Stmt.writeRef s11 s13 ;;                          -- *s11 = s13
        -- return move(y)
        (letsite s12 ← move var_y) ;;
        Stmt.ret [s12]
    }
  ]
}

-- -----------------------------------------------------
-- -           Algorithmic Type Checking Tests        --
-- -----------------------------------------------------

-- VarEnv at l1/l2 entry (after l0: cond consumed)
def t_branch_varEnv : VarEnv :=
  let ve := init_fun_varEnv t
  update ve var_cond (.invalidVar, .basic .tbool, .mutable)

-- Environment at l1/l2 entry
def t_branch_env : TypeEnv := {
  siteEnv := AssocMap.empty
  varEnv := t_branch_varEnv
  pathEnv := PathEnv.init
  funEnv := AssocMap.empty
}

-- VarEnv at l3 entry (a,b moved/invalid, x,y valid)
-- Order of updates must match checker's execution in l1: move a, assign x, move b, assign y
def t_l3_varEnv : VarEnv :=
  let ve := t_branch_varEnv
  let ve := update ve var_a (.invalidVar, .ref (.trecord s_entries) r0 .siteBorrowMut, .mutable)
  let ve := update ve var_x (.validVar, .ref (.trecord s_entries) r0 .siteBorrowMut, .mutable)
  let ve := update ve var_b (.invalidVar, .ref (.trecord s_entries) r0 .siteBorrowMut, .mutable)
  update ve var_y (.validVar, .ref (.trecord s_entries) r0 .siteBorrowMut, .mutable)

-- Environment at l3 entry (no borrows in branches, so PathEnv.init)
def t_l3_env : TypeEnv := {
  siteEnv := AssocMap.empty
  varEnv := t_l3_varEnv
  pathEnv := PathEnv.init
  funEnv := AssocMap.empty
}

-- Initial environment (for entry block)
def t_initEnv : TypeEnv := {
  siteEnv := AssocMap.empty
  varEnv := init_fun_varEnv t
  pathEnv := PathEnv.init
  funEnv := AssocMap.empty
}

-- Label environment
def t_lenv : LabelEnv :=
  insert (insert (insert (insert AssocMap.empty
    "l0" t_initEnv)
    "l1" t_branch_env)
    "l2" t_branch_env)
    "l3" t_l3_env

-- Debug: per-block check
#eval t.blocks.map fun block =>
  (block.label, match lookup t_lenv block.label with
  | some blockEnv => check_block t_lenv block blockEnv t.returnType
  | none => false)

-- Full function check
#eval check_fun t t_lenv

-- Debug: step-by-step check of l3 body to find where it fails
-- Step 1: copy var_x
#eval (check_stmt t_lenv t_l3_env
  ((letsite s5 ← copy var_x) ;;
   Stmt.ret [])
  t.returnType).isSome  -- after copy(x)

-- Step 2: copy var_x + borrowMutField
#eval (check_stmt t_lenv t_l3_env
  ((letsite s5 ← copy var_x) ;;
   Stmt.letBind s6 (Expr.borrowMutField s5 (.trecord s_entries) field_f) ;;
   Stmt.ret [])
  t.returnType).isSome  -- after borrowMutField

-- Step 3: + assign var_f
#eval (check_stmt t_lenv t_l3_env
  ((letsite s5 ← copy var_x) ;;
   Stmt.letBind s6 (Expr.borrowMutField s5 (.trecord s_entries) field_f) ;;
   (var_f ::= s6) ;;
   Stmt.ret [])
  t.returnType).isSome  -- after assign f

-- Step 4: + copy var_f
#eval (check_stmt t_lenv t_l3_env
  ((letsite s5 ← copy var_x) ;;
   Stmt.letBind s6 (Expr.borrowMutField s5 (.trecord s_entries) field_f) ;;
   (var_f ::= s6) ;;
   (letsite s7 ← copy var_f) ;;
   Stmt.ret [])
  t.returnType).isSome  -- after copy(f)

-- Step 5: + readRef
#eval (check_stmt t_lenv t_l3_env
  ((letsite s5 ← copy var_x) ;;
   Stmt.letBind s6 (Expr.borrowMutField s5 (.trecord s_entries) field_f) ;;
   (var_f ::= s6) ;;
   (letsite s7 ← copy var_f) ;;
   Stmt.letBind s8 (Expr.readRef s7) ;;
   Stmt.ret [])
  t.returnType).isSome  -- after readRef

-- Step 6: + pack
#eval (check_stmt t_lenv t_l3_env
  ((letsite s5 ← copy var_x) ;;
   Stmt.letBind s6 (Expr.borrowMutField s5 (.trecord s_entries) field_f) ;;
   (var_f ::= s6) ;;
   (letsite s7 ← copy var_f) ;;
   Stmt.letBind s8 (Expr.readRef s7) ;;
   Stmt.letBind s9 (Expr.pack "S" [(field_f, s8)]) ;;
   Stmt.ret [])
  t.returnType).isSome  -- after pack

-- Step 7: + copy var_y
#eval (check_stmt t_lenv t_l3_env
  ((letsite s5 ← copy var_x) ;;
   Stmt.letBind s6 (Expr.borrowMutField s5 (.trecord s_entries) field_f) ;;
   (var_f ::= s6) ;;
   (letsite s7 ← copy var_f) ;;
   Stmt.letBind s8 (Expr.readRef s7) ;;
   Stmt.letBind s9 (Expr.pack "S" [(field_f, s8)]) ;;
   (letsite s10 ← copy var_y) ;;
   Stmt.ret [])
  t.returnType).isSome  -- after copy(y)

-- Step 8: + writeRef s10 s9
#eval (check_stmt t_lenv t_l3_env
  ((letsite s5 ← copy var_x) ;;
   Stmt.letBind s6 (Expr.borrowMutField s5 (.trecord s_entries) field_f) ;;
   (var_f ::= s6) ;;
   (letsite s7 ← copy var_f) ;;
   Stmt.letBind s8 (Expr.readRef s7) ;;
   Stmt.letBind s9 (Expr.pack "S" [(field_f, s8)]) ;;
   (letsite s10 ← copy var_y) ;;
   Stmt.writeRef s10 s9 ;;
   Stmt.ret [])
  t.returnType).isSome  -- after writeRef y

-- Step 9: + copy var_f + intLit
#eval (check_stmt t_lenv t_l3_env
  ((letsite s5 ← copy var_x) ;;
   Stmt.letBind s6 (Expr.borrowMutField s5 (.trecord s_entries) field_f) ;;
   (var_f ::= s6) ;;
   (letsite s7 ← copy var_f) ;;
   Stmt.letBind s8 (Expr.readRef s7) ;;
   Stmt.letBind s9 (Expr.pack "S" [(field_f, s8)]) ;;
   (letsite s10 ← copy var_y) ;;
   Stmt.writeRef s10 s9 ;;
   (letsite s11 ← copy var_f) ;;
   (letsite s13 ← #0) ;;
   Stmt.ret [])
  t.returnType).isSome  -- after copy(f) + intLit

-- Full l3 body
#eval (check_stmt t_lenv t_l3_env
  ((letsite s5 ← copy var_x) ;;
   Stmt.letBind s6 (Expr.borrowMutField s5 (.trecord s_entries) field_f) ;;
   (var_f ::= s6) ;;
   (letsite s7 ← copy var_f) ;;
   Stmt.letBind s8 (Expr.readRef s7) ;;
   Stmt.letBind s9 (Expr.pack "S" [(field_f, s8)]) ;;
   (letsite s10 ← copy var_y) ;;
   Stmt.writeRef s10 s9 ;;
   (letsite s11 ← copy var_f) ;;
   (letsite s13 ← #0) ;;
   Stmt.writeRef s11 s13 ;;
   (letsite s12 ← move var_y) ;;
   Stmt.ret [s12])
  t.returnType).isSome  -- full l3 body

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
          · exact ⟨0, rfl⟩
        · exact ⟨0, rfl⟩
      · exact ⟨0, rfl⟩
    · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩

-- Helper: t_branch_varEnv has fresh refs
private lemma t_branch_varEnv_fresh :
    VarEnv.RefsAreFresh t_branch_varEnv := by
  unfold t_branch_varEnv
  apply VarEnv.insert_refs_are_fresh
  · exact t_varEnv_fresh
  · trivial

-- Helper: t_l3_varEnv has fresh refs
private lemma t_l3_varEnv_fresh :
    VarEnv.RefsAreFresh t_l3_varEnv := by
  unfold t_l3_varEnv r0
  apply VarEnv.insert_refs_are_fresh
  · apply VarEnv.insert_refs_are_fresh
    · apply VarEnv.insert_refs_are_fresh
      · apply VarEnv.insert_refs_are_fresh
        · exact t_branch_varEnv_fresh
        · exact ⟨0, rfl⟩
      · exact ⟨0, rfl⟩
    · exact ⟨0, rfl⟩
  · exact ⟨0, rfl⟩

-- All envs in t_lenv are well-formed
private lemma t_lenv_wf :
    ∀ l env, lookup t_lenv l = some env → TypeEnv.WellFormed env := by
  intro l env hlookup
  by_cases hl3 : l = "l3"
  · subst hl3
    have h : lookup t_lenv "l3" = some t_l3_env := by rfl
    rw [h] at hlookup; injection hlookup with heq; subst heq
    exact TypeEnv.init_wellformed _ _ t_l3_varEnv_fresh
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

end LeanMove.Examples.Expressivity.ExtensionWritesAfterJoin
