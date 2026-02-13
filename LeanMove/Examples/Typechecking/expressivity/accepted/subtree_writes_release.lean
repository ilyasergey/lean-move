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
# Subtree Writes Release

Source: https://github.com/tnowacki/sui/blob/example-tests/external-crates/move/crates/bytecode-verifier-transactional-tests/tests/reference_safety/expressivity/subtree_writes_release.mvir

This module demonstrates that "release is lossy in the graph" - writes to
references are safe even when there's complex aliasing, as long as references
are properly released.

Nested struct hierarchy:
- Tree { l: Sub1, r: Sub1 }
- Sub1 { l: Sub2, r: Sub2 }
- Sub2 { l: u64, r: u64 }

Original MVIR:
```
t(cond: bool, root: &mut Self.Tree) {
    let x: &mut Self.Sub1;
    let y: &mut u64;
label l0:
    jump_if (move(cond)) l2;
label l1:
    x = &mut copy(root).Tree::l;
    y = &mut (&mut copy(x).Sub1::l).Sub2::l;
    jump l3;
label l2:
    x = &mut copy(root).Tree::r;
    y = &mut (&mut copy(x).Sub1::r).Sub2::r;
    jump l3;
label l3:
    _ = move(x);
    // should be safe root.l.r is not borrowed
    *(&mut (&mut copy(root).Tree::l).Sub1::r) = Sub2 { l: 0, r: 0 };
    *move(y) = 0;
    return;
}
```
-/

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Typing
open AssocMap
open Regex

namespace LeanMove.Examples.Expressivity.SubtreeWritesRelease

-- Fields for nested structs
def field_l : Field := ⟨"l"⟩
def field_r : Field := ⟨"r"⟩

-- Sub2 { l: u64, r: u64 }
def sub2_entries : AssocMap Field BasicMoveType :=
  insert (insert empty field_l .u64) field_r .u64

-- Sub1 { l: Sub2, r: Sub2 }
def sub1_entries : AssocMap Field BasicMoveType :=
  insert (insert empty field_l (.trecord sub2_entries)) field_r (.trecord sub2_entries)

-- Tree { l: Sub1, r: Sub1 }
def tree_entries : AssocMap Field BasicMoveType :=
  insert (insert empty field_l (.trecord sub1_entries)) field_r (.trecord sub1_entries)

-- Abstract reference for the parameter
def r0 : Aref := .refid 0

-- Variables
def var_cond : Var := ⟨"cond"⟩
def var_root : Var := ⟨"root"⟩
def var_x : Var := ⟨"x"⟩
def var_y : Var := ⟨"y"⟩

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
def s12 : Site := .site 12
def s13 : Site := .site 13 -- integer literal 0 for Sub2.l
def s14 : Site := .site 14 -- integer literal 0 for Sub2.r
def s15 : Site := .site 15 -- packed Sub2 struct
def s16 : Site := .site 16 -- integer literal 0 for *move(y)

/-
  t(cond: bool, root: &mut Self.Tree)
  Navigates the tree based on condition, performs writes.

  The function:
  1. Branches based on cond to select left or right Sub1
  2. In each branch, navigates deep to a u64 field
  3. After join, releases x and writes to root.l.r and y

  The writes are safe because "release is lossy in the graph" - when we
  move(x) the reference is released, removing it from the path graph.
-/
def t : FunDef := {
  params := [
    (var_cond, .basic .tbool),
    (var_root, .ref (.trecord tree_entries) r0 .siteBorrowMut)
  ]
  returnType := .basic .tunit
  locals := [
    -- Algorithmic checker assigns .refid 1 for borrowMutField of copy(root) (first borrow in body)
    { name := var_x, type := .ref (.trecord sub1_entries) (.refid 1) .siteBorrowMut },
    -- Algorithmic checker assigns .refid 3 for second borrowMutField chain (Sub2.field → u64)
    { name := var_y, type := .ref .u64 (.refid 3) .siteBorrowMut }
  ]
  blocks := [
    -- l0: branch on condition
    { label := "l0"
      body :=
        (letsite s0 ← move var_cond) ;;  -- s0 = move(cond)
        Stmt.branch s0 "l2" "l1"         -- if s0 then l2 else l1
    },
    -- l1 (false branch): x = &mut root.l; y = &mut x.l.l
    { label := "l1"
      body :=
        -- x = &mut copy(root).Tree::l
        (letsite s1 ← copy var_root) ;;
        Stmt.letBind s2 (Expr.borrowMutField s1 (.trecord tree_entries) field_l) ;;
        (var_x ::= s2) ;;
        -- y = &mut (&mut copy(x).Sub1::l).Sub2::l
        (letsite s3 ← copy var_x) ;;
        Stmt.letBind s4 (Expr.borrowMutField s3 (.trecord sub1_entries) field_l) ;;  -- Sub2
        Stmt.letBind s5 (Expr.borrowMutField s4 (.trecord sub2_entries) field_l) ;;  -- u64
        (var_y ::= s5) ;;
        Stmt.jump "l3"
    },
    -- l2 (true branch): x = &mut root.r; y = &mut x.r.r
    { label := "l2"
      body :=
        -- x = &mut copy(root).Tree::r
        (letsite s1 ← copy var_root) ;;
        Stmt.letBind s2 (Expr.borrowMutField s1 (.trecord tree_entries) field_r) ;;
        (var_x ::= s2) ;;
        -- y = &mut (&mut copy(x).Sub1::r).Sub2::r
        (letsite s3 ← copy var_x) ;;
        Stmt.letBind s4 (Expr.borrowMutField s3 (.trecord sub1_entries) field_r) ;;  -- Sub2
        Stmt.letBind s5 (Expr.borrowMutField s4 (.trecord sub2_entries) field_r) ;;  -- u64
        (var_y ::= s5) ;;
        Stmt.jump "l3"
    },
    -- l3: release x, write to root.l.r, write through y
    { label := "l3"
      body :=
        -- _ = move(x) -- release x
        (letsite s6 ← move var_x) ;;
        -- *(&mut (&mut copy(root).Tree::l).Sub1::r) = Sub2 { l: 0, r: 0 }
        -- This is safe because root.l.r is not borrowed
        (letsite s7 ← copy var_root) ;;
        Stmt.letBind s8 (Expr.borrowMutField s7 (.trecord tree_entries) field_l) ;;  -- &mut Sub1
        Stmt.letBind s9 (Expr.borrowMutField s8 (.trecord sub1_entries) field_r) ;;  -- &mut Sub2
        -- Pack Sub2 { l: 0, r: 0 }
        (letsite s13 ← #0) ;;            -- s13 = 0 (integer literal for l)
        (letsite s14 ← #0) ;;            -- s14 = 0 (integer literal for r)
        Stmt.letBind s15 (Expr.pack "Sub2" [(field_l, s13), (field_r, s14)]) ;;
        Stmt.writeRef s9 s15 ;;          -- *s9 = Sub2 { l: 0, r: 0 }
        -- *move(y) = 0
        (letsite s10 ← move var_y) ;;
        (letsite s16 ← #0) ;;            -- s16 = 0 (integer literal)
        Stmt.writeRef s10 s16 ;;
        Stmt.ret []
    }
  ]
}

-- -----------------------------------------------------
-- -           Algorithmic Type Checking Tests        --
-- -----------------------------------------------------

-- Initial environment for l0 (entry block)
def t_initEnv : TypeEnv := {
  siteEnv := AssocMap.empty
  varEnv := init_fun_varEnv t
  pathEnv := PathEnv.init
  funEnv := AssocMap.empty
}

-- VarEnv at l1/l2 entry (after l0: cond consumed by move)
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

-- VarEnv at l3 entry (x,y assigned/valid; cond still invalid)
def t_l3_varEnv : VarEnv :=
  let ve := t_branch_varEnv
  let ve := update ve var_x (.validVar, .ref (.trecord sub1_entries) (.refid 5) .siteBorrowMut, .mutable)
  update ve var_y (.validVar, .ref .u64 (.refid 8) .siteBorrowMut, .mutable)

-- PathEnv at l3 entry: union of paths from l1 (field_l) and l2 (field_r)
-- l1: root →[field_l]→ Sub1 →[field_l]→ Sub2 →[field_l]→ u64
-- l2: root →[field_r]→ Sub1 →[field_r]→ Sub2 →[field_r]→ u64
-- Refs: .refid 5 = Sub1 borrow, .refid 7 = intermediate Sub2, .refid 8 = u64 borrow
--
-- The checker also produces "reverse" derivative paths via `der` in update_with_extension.
-- These are `Regex.deriv ε (.field f)` values that are semantically empty but not recognized
-- as such by `is_empty` (since is_empty(.deriv r _) = is_empty r, and is_empty ε = false).
-- We must include them in the l3 PathEnv so that regexSubsumedBy can match them exactly.
def t_l3_pathEnv : PathEnv :=
  -- Forward paths: concat ε (char (.field f))
  let fl := Regex.concat Regex.ε (Regex.char (PathElement.field field_l))
  let fr := Regex.concat Regex.ε (Regex.char (PathElement.field field_r))
  let fl2 := Regex.concat fl (Regex.char (PathElement.field field_l))
  let fr2 := Regex.concat fr (Regex.char (PathElement.field field_r))
  -- Reverse derivative paths: deriv ε (.field f)
  let dfl := Regex.deriv Regex.ε (PathElement.field field_l)
  let dfr := Regex.deriv Regex.ε (PathElement.field field_r)
  let dfl2 := Regex.deriv dfl (PathElement.field field_l)
  let dfr2 := Regex.deriv dfr (PathElement.field field_r)
  { refs := [.refid 8, .refid 7, .refid 5, .refid 0, .root]
    paths := fun (u, v) =>
      if u = v then Regex.ε
      -- Forward paths (from field borrows: parent → child)
      else if u = .refid 5 ∧ v = .refid 7 then Regex.union fl fr
      else if u = .refid 7 ∧ v = .refid 8 then Regex.union fl fr
      else if u = .refid 5 ∧ v = .refid 8 then Regex.union fl2 fr2
      -- Reverse derivative paths (child → parent, from der in update_with_extension)
      else if u = .refid 7 ∧ v = .refid 5 then Regex.union dfl dfr
      else if u = .refid 8 ∧ v = .refid 7 then Regex.union dfl dfr
      else if u = .refid 8 ∧ v = .refid 5 then Regex.union dfl2 dfr2
      else Regex.empty }

-- Environment at l3 entry
def t_l3_env : TypeEnv := {
  siteEnv := AssocMap.empty
  varEnv := t_l3_varEnv
  pathEnv := t_l3_pathEnv
  funEnv := AssocMap.empty
}

-- Label environment: maps each label to its entry environment
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

-- Debug: step-by-step check of l1 body
-- Step 1: copy root
#eval (check_stmt t_lenv t_branch_env
  ((letsite s1 ← copy var_root) ;;
   Stmt.jump "l3")
  t.returnType).isSome

-- Step 2: + borrowMutField (Tree::l)
#eval (check_stmt t_lenv t_branch_env
  ((letsite s1 ← copy var_root) ;;
   Stmt.letBind s2 (Expr.borrowMutField s1 (.trecord tree_entries) field_l) ;;
   Stmt.jump "l3")
  t.returnType).isSome

-- Step 3: + assign var_x
#eval (check_stmt t_lenv t_branch_env
  ((letsite s1 ← copy var_root) ;;
   Stmt.letBind s2 (Expr.borrowMutField s1 (.trecord tree_entries) field_l) ;;
   (var_x ::= s2) ;;
   Stmt.jump "l3")
  t.returnType).isSome

-- Step 4: + copy var_x
#eval (check_stmt t_lenv t_branch_env
  ((letsite s1 ← copy var_root) ;;
   Stmt.letBind s2 (Expr.borrowMutField s1 (.trecord tree_entries) field_l) ;;
   (var_x ::= s2) ;;
   (letsite s3 ← copy var_x) ;;
   Stmt.jump "l3")
  t.returnType).isSome

-- Step 5: + borrowMutField (Sub1::l)
#eval (check_stmt t_lenv t_branch_env
  ((letsite s1 ← copy var_root) ;;
   Stmt.letBind s2 (Expr.borrowMutField s1 (.trecord tree_entries) field_l) ;;
   (var_x ::= s2) ;;
   (letsite s3 ← copy var_x) ;;
   Stmt.letBind s4 (Expr.borrowMutField s3 (.trecord sub1_entries) field_l) ;;
   Stmt.jump "l3")
  t.returnType).isSome

-- Step 6: + borrowMutField (Sub2::l)
#eval (check_stmt t_lenv t_branch_env
  ((letsite s1 ← copy var_root) ;;
   Stmt.letBind s2 (Expr.borrowMutField s1 (.trecord tree_entries) field_l) ;;
   (var_x ::= s2) ;;
   (letsite s3 ← copy var_x) ;;
   Stmt.letBind s4 (Expr.borrowMutField s3 (.trecord sub1_entries) field_l) ;;
   Stmt.letBind s5 (Expr.borrowMutField s4 (.trecord sub2_entries) field_l) ;;
   Stmt.jump "l3")
  t.returnType).isSome

-- Step 7: + assign var_y
#eval (check_stmt t_lenv t_branch_env
  ((letsite s1 ← copy var_root) ;;
   Stmt.letBind s2 (Expr.borrowMutField s1 (.trecord tree_entries) field_l) ;;
   (var_x ::= s2) ;;
   (letsite s3 ← copy var_x) ;;
   Stmt.letBind s4 (Expr.borrowMutField s3 (.trecord sub1_entries) field_l) ;;
   Stmt.letBind s5 (Expr.borrowMutField s4 (.trecord sub2_entries) field_l) ;;
   (var_y ::= s5) ;;
   Stmt.jump "l3")
  t.returnType).isSome

-- Full l1 body (same as step 7 — this IS the full l1)
-- Should match the per-block check for l1

-- Debug: what nextFreshRefInEnv produces at l1 entry
#eval nextFreshRefInEnv t_branch_env

-- Theorem: t type checks algorithmically
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
        · exact VarEnv.empty_refs_are_fresh
        · trivial
      · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
  · exact ⟨3, rfl⟩

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
  unfold t_l3_varEnv
  apply VarEnv.insert_refs_are_fresh
  · apply VarEnv.insert_refs_are_fresh
    · exact t_branch_varEnv_fresh
    · exact ⟨5, rfl⟩
  · exact ⟨8, rfl⟩

-- Helper: t_l3_pathEnv is well-formed
private lemma t_l3_pathEnv_wf : PathEnv.WellFormed t_l3_pathEnv := by
  constructor
  · -- refs_complete: for r ∉ refs, paths (.root, r) = .empty
    intro r hr
    simp only [t_l3_pathEnv]
    -- Since u = .root, none of the refid conditions (u = .refid N) can be true
    -- The function falls through all conditions to Regex.empty
    have hne : Aref.root ≠ r := by
      intro heq; subst heq
      exact hr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr
        (Or.inr (List.mem_cons.mpr (Or.inr (List.mem_cons.mpr
          (Or.inr (List.mem_cons.mpr (Or.inl rfl))))))))))
    simp [hne]
  · -- varref_tracked: vacuously true (no .varRef in refs)
    intro x hx
    simp only [t_l3_pathEnv, List.mem_cons] at hx
    rcases hx with h | h | h | h | h
    all_goals (first | exact absurd h Aref.noConfusion | simp at h)
  · -- root_in_refs
    simp only [t_l3_pathEnv, List.mem_cons]
    right; right; right; right; left; trivial

-- Helper: t_l3_env is well-formed
private lemma t_l3_env_wf : TypeEnv.WellFormed t_l3_env := by
  constructor
  · exact t_l3_pathEnv_wf
  · exact SiteEnv.empty_refs_not_root
  · exact t_l3_varEnv_fresh

-- All envs in t_lenv are well-formed
private lemma t_lenv_wf :
    ∀ l env, lookup t_lenv l = some env → TypeEnv.WellFormed env := by
  intro l env hlookup
  by_cases hl3 : l = "l3"
  · subst hl3
    have h : lookup t_lenv "l3" = some t_l3_env := by rfl
    rw [h] at hlookup; injection hlookup with heq; subst heq
    exact t_l3_env_wf
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

end LeanMove.Examples.Expressivity.SubtreeWritesRelease
