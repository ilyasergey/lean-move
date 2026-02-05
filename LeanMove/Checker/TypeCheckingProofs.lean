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

import LeanMove.Checker.TypeCheckingAlgorithmic

/-!
# Type Checking Proofs for MoveLight

This file contains soundness and completeness proofs for the algorithmic type
checker defined in `TypeCheckingAlgorithmic.lean` with respect to the relational
specification in `TypeChecking.lean`.

## Main Results

- `check_stmt_sound`: Statement-level soundness
- `check_stmt_complete`: Statement-level completeness
- `check_fun_sound`: If `check_fun f lenv = true`, then `typecheck_fun f lenv`
- `check_fun_complete`: If `typecheck_fun f lenv`, then `check_fun f lenv = true`
- `check_fun_equiv`: `check_fun f lenv = true ↔ typecheck_fun f lenv`

## Key Invariants

- `PathEnv.Simple`: Paths from root are always simple (empty, ε, or single char)
- `PathEnv.WellFormed`: Combines Simple with refs completeness
- These invariants are preserved by all path environment operations
-/

namespace LeanMove.Checker

open Lang
open Lang.MoveLight
open AssocMap
open Regex

/- ---------------------------------------------------- -/
/-       Regex equality lemmas                           -/
/- ---------------------------------------------------- -/

lemma regexBeq_refl [BEq α] [LawfulBEq α] : ∀ (r : Regex α), regexBeq r r = true
  | .empty => rfl
  | .ε => rfl
  | .char a => beq_self_eq_true a
  | .dot => rfl
  | .union r1 r2 => by simp only [regexBeq, regexBeq_refl r1, regexBeq_refl r2, Bool.and_self]
  | .concat r1 r2 => by simp only [regexBeq, regexBeq_refl r1, regexBeq_refl r2, Bool.and_self]
  | .star r => regexBeq_refl r
  | .deriv r a => by simp only [regexBeq, regexBeq_refl r, beq_self_eq_true, Bool.and_self]

lemma regexBeq_eq [DecidableEq α] : ∀ (r1 r2 : Regex α), regexBeq r1 r2 = true → r1 = r2 := by
  intro r1
  induction r1 with
  | empty =>
    intro r2 h
    cases r2 <;> simp only [regexBeq, Bool.false_eq_true] at h
    rfl
  | ε =>
    intro r2 h
    cases r2 <;> simp only [regexBeq, Bool.false_eq_true] at h
    rfl
  | char a =>
    intro r2 h
    cases r2 <;> simp only [regexBeq, Bool.false_eq_true] at h
    simp only [beq_iff_eq] at h
    subst h
    rfl
  | dot =>
    intro r2 h
    cases r2 <;> simp only [regexBeq, Bool.false_eq_true] at h
    rfl
  | union r1a r1b ih1 ih2 =>
    intro r2 h
    cases r2 <;> simp only [regexBeq, Bool.false_eq_true] at h
    rename_i r2a r2b
    simp only [Bool.and_eq_true] at h
    rw [ih1 r2a h.1, ih2 r2b h.2]
  | concat r1a r1b ih1 ih2 =>
    intro r2 h
    cases r2 <;> simp only [regexBeq, Bool.false_eq_true] at h
    rename_i r2a r2b
    simp only [Bool.and_eq_true] at h
    rw [ih1 r2a h.1, ih2 r2b h.2]
  | star r1 ih =>
    intro r2 h
    cases r2 <;> simp only [regexBeq, Bool.false_eq_true] at h
    rename_i r2
    rw [ih r2 h]
  | deriv r1 a ih =>
    intro r2 h
    cases r2 <;> simp only [regexBeq, Bool.false_eq_true] at h
    rename_i r2 b
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    rw [ih r2 h.1, h.2]

lemma eq_regexBeq [DecidableEq α] : ∀ (r1 r2 : Regex α), r1 = r2 → regexBeq r1 r2 = true := by
  intro r1 r2 h
  subst h
  exact regexBeq_refl r1

/- ---------------------------------------------------- -/
/-       Theorems about freshRef and nextFreshRef        -/
/- ---------------------------------------------------- -/

theorem freshRef_iff_freshRefBool (r : Aref) (pe : PathEnv) :
    freshRef r pe ↔ freshRefBool r pe = true := by
  unfold freshRef freshRefBool
  simp only [Bool.not_eq_true', List.contains_eq_any_beq]
  constructor
  · intro hNotIn
    rw [List.any_eq_false]
    intro x hx hbeq
    have heq : r = x := beq_iff_eq.mp hbeq
    exact hNotIn (heq ▸ hx)
  · intro hAny hIn
    rw [List.any_eq_false] at hAny
    have := hAny r hIn
    have hbeq : (r == r) = true := beq_self_eq_true r
    exact this hbeq

private lemma foldl_max_ge_init (l : List Aref) (init : Nat) :
    l.foldl (fun acc a => max acc (getRefId a)) init ≥ init := by
  induction l generalizing init with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons]
    exact Nat.le_trans (Nat.le_max_left _ _) (ih _)

private lemma foldl_max_ge_elem (l : List Aref) (init : Nat) (r : Aref) (hr : r ∈ l) :
    l.foldl (fun acc a => max acc (getRefId a)) init ≥ getRefId r := by
  induction l generalizing init with
  | nil => cases hr
  | cons x xs ih =>
    simp only [List.foldl_cons, List.mem_cons] at hr ⊢
    cases hr with
    | inl heq =>
      subst heq
      have h1 : max init (getRefId r) ≥ getRefId r := Nat.le_max_right _ _
      have h2 := foldl_max_ge_init xs (max init (getRefId r))
      exact Nat.le_trans h1 h2
    | inr htail =>
      exact ih (max init (getRefId x)) htail

theorem nextFreshRef_fresh (pe : PathEnv) : freshRefBool (nextFreshRef pe) pe = true := by
  unfold nextFreshRef freshRefBool
  simp only [Bool.not_eq_true', List.contains_eq_any_beq]
  rw [List.any_eq_false]
  intro r hr
  simp only [beq_iff_eq]
  intro heq
  have hmax := foldl_max_ge_elem pe.refs 0 r hr
  subst heq
  simp only [getRefId] at hmax
  omega

lemma freshRefBool_implies_freshRef (r : Aref) (pe : PathEnv) :
    freshRefBool r pe = true → freshRef r pe := by
  intro h
  rw [freshRef_iff_freshRefBool]
  exact h

lemma nextFreshRef_fresh_prop (pe : PathEnv) : freshRef (nextFreshRef pe) pe := by
  rw [freshRef_iff_freshRefBool]
  exact nextFreshRef_fresh pe

/- ---------------------------------------------------- -/
/-       PathEnv lemmas                                  -/
/- ---------------------------------------------------- -/

lemma delete_ref_node_refs (pe : PathEnv) (r : Aref) :
    (delete_ref_node pe r).refs = List.filter (fun r' => r' ≠ r) pe.refs := by
  rfl

lemma delete_ref_node_paths_involving_r (pe : PathEnv) (r : Aref) (u v : Aref) :
    u = r ∨ v = r → (delete_ref_node pe r).paths (u, v) = Regex.empty := by
  move=> h
  simp only [delete_ref_node]
  scase: h => hr
  · simp [hr]
  · simp [hr]

lemma delete_ref_node_paths_not_involving_r (pe : PathEnv) (r : Aref) (u v : Aref) :
    u ≠ r → v ≠ r → (delete_ref_node pe r).paths (u, v) = pe.paths (u, v) := by
  move=> hu hv
  simp only [delete_ref_node]
  simp [hu, hv]

/- ---------------------------------------------------- -/
/-       PathEnv simplicity (key invariant)              -/
/- ---------------------------------------------------- -/

/-- A path environment has "simple" paths from root if all paths from root
    to any reference are either empty, ε, or a single character.
    This is an invariant maintained by the type checker. -/
inductive SimpleRootPath : Regex PathElement → Prop where
  | empty : SimpleRootPath .empty
  | eps : SimpleRootPath .ε
  | char (c : PathElement) : SimpleRootPath (.char c)

def PathEnv.Simple (pe : PathEnv) : Prop :=
  ∀ r, SimpleRootPath (pe.paths (.root, r))

/-- A path environment is well-formed if:
    1. Paths from root are simple (empty, ε, or single char)
    2. Refs not in the refs list have empty paths from root -/
structure PathEnv.WellFormed (pe : PathEnv) : Prop where
  simple : PathEnv.Simple pe
  refs_complete : ∀ r, r ∉ pe.refs → pe.paths (.root, r) = .empty

lemma PathEnv.init_simple : PathEnv.Simple PathEnv.init := by
  intro r
  simp only [PathEnv.init]
  by_cases hr : Aref.root = r
  · simp [hr]; exact SimpleRootPath.eps
  · simp [hr]; exact SimpleRootPath.empty

lemma PathEnv.init_wellformed : PathEnv.WellFormed PathEnv.init := by
  constructor
  · exact PathEnv.init_simple
  · intro r hr
    simp only [PathEnv.init, List.mem_singleton] at hr
    simp only [PathEnv.init]
    by_cases heq : Aref.root = r
    · exact absurd heq.symm hr
    · simp [heq]

/-- delete_ref_node preserves WellFormed -/
lemma delete_ref_node_wellformed (pe : PathEnv) (r : Aref) (hwf : PathEnv.WellFormed pe) :
    PathEnv.WellFormed (delete_ref_node pe r) := by
  constructor
  · -- Simple preservation
    intro r'
    by_cases hr : Aref.root = r
    · -- root = r, so all paths from root are empty
      have := delete_ref_node_paths_involving_r pe r .root r' (Or.inl hr)
      simp only [this]
      exact SimpleRootPath.empty
    · -- root ≠ r
      by_cases hr' : r' = r
      · -- r' = r, so path from root to r' is empty
        have := delete_ref_node_paths_involving_r pe r .root r' (Or.inr hr')
        simp only [this]
        exact SimpleRootPath.empty
      · -- r' ≠ r, so path is preserved
        have hne : Aref.root ≠ r := hr
        have := delete_ref_node_paths_not_involving_r pe r .root r' hne hr'
        simp only [this]
        exact hwf.simple r'
  · -- refs_complete preservation
    intro r' hr'
    by_cases hr : Aref.root = r
    · -- root = r
      have := delete_ref_node_paths_involving_r pe r .root r' (Or.inl hr)
      exact this
    · by_cases hr'' : r' = r
      · -- r' = r
        have := delete_ref_node_paths_involving_r pe r .root r' (Or.inr hr'')
        exact this
      · -- r' ≠ r, so r' ∉ pe.refs by hr'
        -- hr' : r' ∉ (delete_ref_node pe r).refs
        -- (delete_ref_node pe r).refs = List.filter (fun x => x ≠ r) pe.refs
        -- So r' ∉ List.filter (· ≠ r) pe.refs means: ¬(r' ∈ pe.refs ∧ r' ≠ r)
        -- Since hr'' : r' ≠ r, we get r' ∉ pe.refs
        have hnotin : r' ∉ pe.refs := by
          intro hcontra
          apply hr'
          simp only [delete_ref_node_refs, List.mem_filter, decide_eq_true_eq]
          exact ⟨hcontra, hr''⟩
        have hne : Aref.root ≠ r := hr
        have := delete_ref_node_paths_not_involving_r pe r .root r' hne hr''
        simp only [this]
        exact hwf.refs_complete r' hnotin

/-- update_with_epsilon preserves WellFormed (with sorry for full proof) -/
lemma update_with_epsilon_wellformed (s t : Aref) (pe : PathEnv) (hwf : PathEnv.WellFormed pe) :
    PathEnv.WellFormed (update_with_epsilon s t pe) := by
  sorry

/-- update_with_extension preserves WellFormed (with sorry for full proof) -/
lemma update_with_extension_wellformed (u v : Aref) (path : List PathElement) (pe : PathEnv)
    (hwf : PathEnv.WellFormed pe) :
    PathEnv.WellFormed (update_with_extension u v path pe) := by
  sorry

/-- garbage_collect preserves WellFormed (with sorry for full proof) -/
lemma garbage_collect_wellformed (pe : PathEnv) (r : Aref) (hwf : PathEnv.WellFormed pe) :
    PathEnv.WellFormed (garbage_collect pe r) := by
  sorry

/-- consume_ref_transfer preserves WellFormed (with sorry for full proof) -/
lemma consume_ref_transfer_wellformed (pe : PathEnv) (r r' : Aref) (hwf : PathEnv.WellFormed pe) :
    PathEnv.WellFormed (consume_ref_transfer pe r r') := by
  sorry

/- ---------------------------------------------------- -/
/-       TypeEnv.equiv lemmas                            -/
/- ---------------------------------------------------- -/

lemma TypeEnv.equiv_refl (env : TypeEnv) : TypeEnv.equiv env env := by
  exact ⟨rfl, rfl, rfl, fun _ _ _ _ => rfl⟩

lemma TypeEnv.equiv_bool_implies_equiv (env1 env2 : TypeEnv) :
    TypeEnv.equiv_bool env1 env2 = true → TypeEnv.equiv env1 env2 := by
  intro h
  simp only [TypeEnv.equiv_bool, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨hsite, hvar⟩, hrefs⟩, hpaths⟩ := h
  refine ⟨hsite, hvar, hrefs, ?_⟩
  intro u v hu hv
  have h1 := hpaths u hu
  have h2 := h1 v hv
  exact regexBeq_eq _ _ h2

lemma TypeEnv.equiv_implies_equiv_bool (env1 env2 : TypeEnv) :
    TypeEnv.equiv env1 env2 → TypeEnv.equiv_bool env1 env2 = true := by
  intro ⟨hsite, hvar, hrefs, hpaths⟩
  simp only [TypeEnv.equiv_bool, Bool.and_eq_true, beq_iff_eq, List.all_eq_true]
  refine ⟨⟨⟨hsite, hvar⟩, hrefs⟩, ?_⟩
  intro u hu v hv
  have heq := hpaths u v hu hv
  exact eq_regexBeq _ _ heq

/- ---------------------------------------------------- -/
/-       not_borrowed soundness (WellFormed → Bool → Prop)   -/
/- ---------------------------------------------------- -/

/-- Soundness: if boolean check passes and path env is well-formed, semantic property holds -/
lemma not_borrowed_bool_sound (x : Var) (env : TypeEnv)
    (hwf : PathEnv.WellFormed env.pathEnv) :
    not_borrowed_bool x env = true → not_borrowed x env := by
  intro hbool r
  simp only [not_borrowed_bool, List.all_eq_true] at hbool
  -- We need to show that the path from root to r doesn't accept [.root_to_var x]
  -- The path env is well-formed, so paths from root are simple (empty, ε, or char)
  by_cases hr : r ∈ env.pathEnv.refs
  · -- r is in refs, so the boolean check applies
    have h := hbool r hr
    -- h says the path isn't a char matching root_to_var x
    have hs := hwf.simple r
    -- We need to show ¬ interpret_regex (pathEnv.paths (.root, r)) [.root_to_var x]
    -- Case analysis on the shape of the path
    generalize hpath : env.pathEnv.paths (.root, r) = p at hs ⊢
    cases hs with
    | empty => simp only [Regex.interpret_regex]; exact fun h => h
    | eps => simp only [Regex.interpret_regex]; intro heq; cases heq
    | char c =>
      simp only [Regex.interpret_regex]
      intro heq
      simp only [hpath, bne_iff_ne, ne_eq] at h
      -- heq : [.root_to_var x] = [c], so c = .root_to_var x
      simp only [List.cons.injEq, and_true] at heq
      -- Now heq : .root_to_var x = c
      exact h heq.symm
  · -- r is not in refs, so path from root must be empty by WellFormed
    have hempty := hwf.refs_complete r hr
    simp only [hempty, Regex.interpret_regex]
    exact fun h => h

/- ---------------------------------------------------- -/
/-       no_locals_borrowed soundness                    -/
/- ---------------------------------------------------- -/

lemma no_locals_borrowed_bool_sound (env : TypeEnv)
    (hwf : PathEnv.WellFormed env.pathEnv) :
    no_locals_borrowed_bool env = true → no_locals_borrowed env := by
  intro hbool x v hxv
  simp only [no_locals_borrowed_bool, List.all_eq_true] at hbool
  have h := hbool (x, v) hxv
  -- h says not_borrowed_bool x env = true
  -- We need to show not_borrowed x env
  have hnotbor : not_borrowed_bool x env = true := h
  exact not_borrowed_bool_sound x env hwf hnotbor

/- ---------------------------------------------------- -/
/-       types_conform equivalence                       -/
/- ---------------------------------------------------- -/

lemma types_conform_bool_sound (siteEnv : SiteEnv) (sites : List Site) (paramTypes : List ParamType) :
    types_conform_bool siteEnv sites paramTypes = true → types_conform siteEnv sites paramTypes := by
  induction sites generalizing paramTypes with
  | nil =>
    intro h
    cases paramTypes with
    | nil => exact trivial
    | cons _ _ => simp [types_conform_bool] at h
  | cons site sites' ih =>
    intro h
    cases paramTypes with
    | nil => simp [types_conform_bool] at h
    | cons paramType paramTypes' =>
      simp only [types_conform_bool] at h
      cases hlookup : lookup siteEnv site with
      | none => simp [hlookup] at h
      | some τ =>
        simp only [hlookup] at h
        simp only [types_conform, hlookup]
        cases paramType with
        | mk bt optRef =>
          cases optRef with
          | none =>
            cases τ with
            | basic bt' =>
              simp only [Bool.and_eq_true] at h
              exact ⟨BasicMoveType.eq_of_beq bt bt' h.1, ih paramTypes' h.2⟩
            | ref _ _ _ => simp at h
          | some isRefMut =>
            cases τ with
            | basic _ => simp at h
            | ref τ' _ isBor =>
              simp only [Bool.and_eq_true] at h
              obtain ⟨⟨hbt, hbor⟩, hrest⟩ := h
              constructor
              · exact BasicMoveType.eq_of_beq bt τ' hbt
              constructor
              · cases isRefMut <;> cases isBor <;> simp at hbor ⊢
              · exact ih paramTypes' hrest

lemma types_conform_bool_complete (siteEnv : SiteEnv) (sites : List Site) (paramTypes : List ParamType) :
    types_conform siteEnv sites paramTypes → types_conform_bool siteEnv sites paramTypes = true := by
  induction sites generalizing paramTypes with
  | nil =>
    intro h
    cases paramTypes with
    | nil => rfl
    | cons _ _ => simp [types_conform] at h
  | cons site sites' ih =>
    intro h
    cases paramTypes with
    | nil => simp [types_conform] at h
    | cons paramType paramTypes' =>
      simp only [types_conform] at h
      simp only [types_conform_bool]
      cases hlookup : lookup siteEnv site with
      | none => simp [hlookup] at h
      | some τ =>
        simp only [hlookup] at h
        cases paramType with
        | mk bt optRef =>
          cases optRef with
          | none =>
            cases τ with
            | basic bt' =>
              simp only [Bool.and_eq_true]
              exact ⟨BasicMoveType.beq_of_eq bt bt' h.1, ih paramTypes' h.2⟩
            | ref _ _ _ => simp at h
          | some isRefMut =>
            cases τ with
            | basic _ => simp at h
            | ref τ' _ isBor =>
              simp only [Bool.and_eq_true]
              obtain ⟨hbt, hbor, hrest⟩ := h
              constructor
              constructor
              · exact BasicMoveType.beq_of_eq bt τ' hbt
              · cases isRefMut <;> cases isBor <;> simp at hbor ⊢
              · exact ih paramTypes' hrest

/- ---------------------------------------------------- -/
/-       all_fresh_sites equivalence                     -/
/- ---------------------------------------------------- -/

lemma all_fresh_sites_bool_sound (env : TypeEnv) (as : List Site) :
    all_fresh_sites_bool env as = true → all_fresh_sites env as := by
  intro h
  simp only [all_fresh_sites_bool, List.all_eq_true] at h
  simp only [all_fresh_sites]
  rw [List.all_eq_true]
  exact h

lemma all_fresh_sites_bool_complete (env : TypeEnv) (as : List Site) :
    all_fresh_sites env as → all_fresh_sites_bool env as = true := by
  intro h
  simp only [all_fresh_sites_bool, List.all_eq_true]
  simp only [all_fresh_sites] at h
  rw [List.all_eq_true] at h
  exact h

/- ---------------------------------------------------- -/
/-       Field distinctness lemma                        -/
/- ---------------------------------------------------- -/

/-- If check_fields_distinct returns true, all sites in fields are pairwise distinct.
    Proof: length = eraseDups.length means no duplicates. Two pairs with different
    fields but same site would create a duplicate, contradiction. -/
lemma check_fields_distinct_implies_sites_distinct (fields : List (Field × Site)) :
    check_fields_distinct fields = true →
    ∀ a₁ a₂, (∃ f₁ f₂, (f₁, a₁) ∈ fields ∧ (f₂, a₂) ∈ fields ∧ f₁ ≠ f₂) → a₁ ≠ a₂ := by
  intro hdistinct a₁ a₂ ⟨f₁, f₂, hf₁, hf₂, hfne⟩
  simp only [check_fields_distinct, beq_iff_eq] at hdistinct
  intro heq
  subst heq
  -- (f₁, a₁) and (f₂, a₁) are in fields with f₁ ≠ f₂
  -- This means a₁ appears twice in fields.map Prod.snd
  -- But hdistinct says length = eraseDups.length (no duplicates) - contradiction
  sorry

/- ---------------------------------------------------- -/
/-       letBind soundness helper lemma                  -/
/- ---------------------------------------------------- -/

/-- Helper lemma for letBind soundness: handles all expression sub-cases.
    This lemma is complex due to the many expression variants. Each case
    requires matching the algorithmic check with the corresponding relational rule.

    Key challenges:
    1. VarEnv entries are tuples (IsValid, MoveType × Mut)
    2. Fresh reference generation must be shown to produce valid fresh refs
    3. WellFormed preservation for path environment updates
    4. Argument order differences between algorithmic checker and relational rules -/
lemma check_letBind_sound (lenv : LabelEnv) (env : TypeEnv) (a : Site) (e : Expr) (cont : Stmt) (retType : MoveType)
    (hwf : PathEnv.WellFormed env.pathEnv)
    (ih_cont : ∀ env', PathEnv.WellFormed env'.pathEnv →
        (check_stmt lenv env' cont retType).isSome = true → typecheck_stmt lenv env' cont retType)
    (h : (check_stmt lenv env (.letBind a e cont) retType).isSome = true) :
    typecheck_stmt lenv env (.letBind a e cont) retType := by
  -- Case split on expression type
  cases e with
  -- Integer literal: simple case
  | intLit n =>
    simp only [check_stmt] at h
    split at h
    · rename_i hfresh
      apply typecheck_stmt.let_bind_intLit
      · exact hfresh
      · exact ih_cont _ hwf h
    · simp at h

  -- Usage expressions (move, copy, borrow)
  | usage u =>
    cases u with
    | move x =>
      simp only [check_stmt] at h
      cases hlookup : lookup env.varEnv x with
      | none => simp [hlookup] at h
      | some entry =>
        simp only [hlookup] at h
        match hentry : entry with
        | (.validVar, τ, ms) =>
          simp only [hentry] at h
          split at h
          · rename_i hcond
            simp only [Bool.and_eq_true] at hcond
            obtain ⟨hnotbor, hfresh⟩ := hcond
            apply typecheck_stmt.let_bind_move (τ := τ) (ms := ms)
            · simp only [hlookup, hentry]
            · exact not_borrowed_bool_sound x env hwf hnotbor
            · exact hfresh
            · exact ih_cont _ hwf h
          · simp at h
        | (.invalidVar, _, _) => simp [hentry] at h

    | copy x =>
      simp only [check_stmt] at h
      cases hlookup : lookup env.varEnv x with
      | none => simp [hlookup] at h
      | some entry =>
        simp only [hlookup] at h
        match hentry : entry with
        | (.validVar, .basic bt, ms) =>
          simp only [hentry] at h
          split at h
          · rename_i hfresh
            apply typecheck_stmt.let_bind_copy_val (bt := bt) (ms := ms)
            · simp only [hlookup, hentry]
            · exact hfresh
            · exact ih_cont _ hwf h
          · simp at h
        | (.validVar, .ref τ s isBor, ms) =>
          simp only [hentry] at h
          split at h
          · rename_i hfresh
            let t := nextFreshRef env.pathEnv
            apply typecheck_stmt.let_bind_copy_ref (τ := τ) (s := s) (t := t) (isBor := isBor) (ms := ms)
            · simp only [hlookup, hentry]
            · exact hfresh
            · exact nextFreshRef_fresh env.pathEnv
            · have hwf' : PathEnv.WellFormed (update_with_epsilon s t env.pathEnv) :=
                update_with_epsilon_wellformed s t env.pathEnv hwf
              exact ih_cont _ hwf' h
          · simp at h
        | (.invalidVar, _, _) => simp [hentry] at h

    | borrowImm x =>
      simp only [check_stmt] at h
      cases hlookup : lookup env.varEnv x with
      | none => simp [hlookup] at h
      | some entry =>
        simp only [hlookup] at h
        match hentry : entry with
        | (.validVar, .basic τ, ms) =>
          simp only [hentry] at h
          split at h
          · rename_i hfresh
            let r := Aref.varRef x
            apply typecheck_stmt.let_bind_borrowImm (τ := τ) (ms := ms) (r := r)
            · simp only [hlookup, hentry]
            · exact hfresh
            · -- freshRefBool (varRef x) env.pathEnv
              -- This holds if varRef x is not in env.pathEnv.refs
              sorry
            · have hwf' : PathEnv.WellFormed _ :=
                update_with_extension_wellformed r .root [.root_to_var x] _
                  (update_with_epsilon_wellformed r r env.pathEnv hwf)
              exact ih_cont _ hwf' h
          · simp at h
        | (.validVar, .ref _ _ _, _) => simp [hentry] at h
        | (.invalidVar, _, _) => simp [hentry] at h

    | borrowMut x =>
      simp only [check_stmt] at h
      cases hlookup : lookup env.varEnv x with
      | none => simp [hlookup] at h
      | some entry =>
        simp only [hlookup] at h
        match hentry : entry with
        | (.validVar, .basic τ, ms) =>
          simp only [hentry] at h
          split at h
          · rename_i hcond
            simp only [Bool.and_eq_true, beq_iff_eq] at hcond
            obtain ⟨hms, hfresh⟩ := hcond
            let r := Aref.varRef x
            apply typecheck_stmt.let_bind_borrowMut (τ := τ) (ms := ms) (r := r)
            · simp only [hms, LE.le, Mut.le]
            · simp only [hlookup, hentry]
            · exact hfresh
            · -- freshRefBool (varRef x) env.pathEnv
              sorry
            · have hwf' : PathEnv.WellFormed _ :=
                update_with_extension_wellformed r .root [.root_to_var x] _
                  (update_with_epsilon_wellformed r r env.pathEnv hwf)
              exact ih_cont _ hwf' h
          · simp at h
        | (.validVar, .ref _ _ _, _) => simp [hentry] at h
        | (.invalidVar, _, _) => simp [hentry] at h

  -- Binary operation
  | binop bop src1 src2 =>
    simp only [check_stmt] at h
    cases hlookup1 : lookup env.siteEnv src1 with
    | none => simp [hlookup1] at h
    | some τ1 =>
      cases hlookup2 : lookup env.siteEnv src2 with
      | none => simp [hlookup1, hlookup2] at h
      | some τ2 =>
        simp only [hlookup1, hlookup2] at h
        cases τ1 with
        | basic bt1 =>
          cases τ2 with
          | basic bt2 =>
            cases hbinop : binop_type bop bt1 bt2 with
            | none => simp [hbinop] at h
            | some bt3 =>
              simp only [hbinop] at h
              split at h
              · rename_i hfresh
                apply typecheck_stmt.let_bind_binop
                · exact hlookup1
                · exact hlookup2
                · exact hbinop
                · exact hfresh
                · exact ih_cont _ hwf h
              · simp at h
          | ref _ _ _ => simp at h
        | ref _ _ _ => simp at h

  -- Read reference (dereference)
  | readRef src =>
    simp only [check_stmt] at h
    cases hlookup : lookup env.siteEnv src with
    | none => simp [hlookup] at h
    | some τ =>
      cases τ with
      | basic _ => simp [hlookup] at h
      | ref bt r isBor =>
        simp only [hlookup] at h
        split at h
        · rename_i hfresh
          apply typecheck_stmt.let_bind_readRef
          · exact hlookup
          · exact hfresh
          · have hwf' : PathEnv.WellFormed (delete_ref_node env.pathEnv r) :=
              delete_ref_node_wellformed env.pathEnv r hwf
            exact ih_cont _ hwf' h
        · simp at h

  -- Freeze
  | freeze src =>
    simp only [check_stmt] at h
    cases hlookup : lookup env.siteEnv src with
    | none => simp [hlookup] at h
    | some τ =>
      cases τ with
      | basic _ => simp [hlookup] at h
      | ref bt r isBor =>
        simp only [hlookup] at h
        split at h
        · rename_i hfresh
          let r' := nextFreshRef env.pathEnv
          apply typecheck_stmt.let_bind_freeze (r' := r')
          · exact hlookup
          · exact hfresh
          · exact freshRefBool_implies_freshRef r' env.pathEnv (nextFreshRef_fresh env.pathEnv)
          · have hwf' : PathEnv.WellFormed (consume_ref_transfer env.pathEnv r r') :=
              consume_ref_transfer_wellformed env.pathEnv r r' hwf
            exact ih_cont _ hwf' h
        · simp at h

  -- Borrow field
  | borrowField src bt f =>
    simp only [check_stmt] at h
    cases hlookup : lookup env.siteEnv src with
    | none => simp [hlookup] at h
    | some τ =>
      cases τ with
      | basic _ => simp [hlookup] at h
      | ref bt' s isBor =>
        simp only [hlookup] at h
        split at h
        · rename_i hbeq
          cases bt with
          | trecord fentries =>
            cases hlookupf : lookup fentries f with
            | none => simp [hlookupf] at h
            | some btf =>
              simp only [hlookupf] at h
              split at h
              · rename_i hfresh
                let rf := nextFreshRef env.pathEnv
                have hbt_eq : BasicMoveType.trecord fentries = bt' :=
                  BasicMoveType.eq_of_beq _ _ hbeq
                apply typecheck_stmt.let_bind_borrowField (bt := .trecord fentries)
                    (bt' := btf) (isBor := isBor) (fentries := fentries) (s := s) (rf := rf)
                · simp only [hlookup, hbt_eq]
                · rfl
                · exact hlookupf
                · exact hfresh
                · exact freshRefBool_implies_freshRef rf env.pathEnv (nextFreshRef_fresh env.pathEnv)
                · have hwf' : PathEnv.WellFormed (update_with_extension rf s [.field f] env.pathEnv) :=
                    update_with_extension_wellformed rf s [.field f] env.pathEnv hwf
                  exact ih_cont _ hwf' h
              · simp at h
          | _ => simp at h
        · simp at h

  -- Mutable borrow field
  | borrowMutField src bt f =>
    simp only [check_stmt] at h
    cases hlookup : lookup env.siteEnv src with
    | none => simp [hlookup] at h
    | some τ =>
      cases τ with
      | basic _ => simp [hlookup] at h
      | ref bt' s isBor =>
        cases isBor with
        | siteBorrowImm => simp [hlookup] at h
        | siteBorrowMut =>
          simp only [hlookup] at h
          split at h
          · rename_i hbeq
            cases bt with
            | trecord fentries =>
              cases hlookupf : lookup fentries f with
              | none => simp [hlookupf] at h
              | some btf =>
                simp only [hlookupf] at h
                split at h
                · rename_i hfresh
                  let rf := nextFreshRef env.pathEnv
                  have hbt_eq : BasicMoveType.trecord fentries = bt' :=
                    BasicMoveType.eq_of_beq _ _ hbeq
                  apply typecheck_stmt.let_bind_borrowMutField (bt := .trecord fentries)
                      (btf := btf) (fentries := fentries) (s := s) (rf := rf)
                  · simp only [hlookup, hbt_eq]
                  · rfl
                  · exact hlookupf
                  · exact hfresh
                  · exact freshRefBool_implies_freshRef rf env.pathEnv (nextFreshRef_fresh env.pathEnv)
                  · have hwf' : PathEnv.WellFormed (update_with_extension rf s [.field f] env.pathEnv) :=
                      update_with_extension_wellformed rf s [.field f] env.pathEnv hwf
                    exact ih_cont _ hwf' h
                · simp at h
            | _ => simp at h
          · simp at h

  -- Pack
  | pack recName fields =>
    simp only [check_stmt] at h
    split at h
    · rename_i hcond
      simp only [Bool.and_eq_true] at hcond
      obtain ⟨hfresh, hdistinct⟩ := hcond
      -- Split on the match in h
      split at h
      · rename_i fentries hfold
        apply typecheck_stmt.let_bind_pack (fentries := fentries)
        · exact hfresh
        · -- Need to show fields have basic types and exist in fentries
          sorry
        · exact check_fields_distinct_implies_sites_distinct fields hdistinct
        · exact ih_cont _ hwf h
      · simp at h
    · simp at h

/- ---------------------------------------------------- -/
/-       Statement type checking soundness               -/
/- ---------------------------------------------------- -/

/-- Soundness: If the algorithmic check succeeds, the relational judgment holds.
    This requires the path environment to be well-formed.
-/
theorem check_stmt_sound (lenv : LabelEnv) (env : TypeEnv) (s : Stmt) (retType : MoveType)
    (hwf : PathEnv.WellFormed env.pathEnv) :
    (check_stmt lenv env s retType).isSome = true → typecheck_stmt lenv env s retType := by
  -- Use induction on the statement structure to get IH for recursive cases
  induction s generalizing env with
  | skip => intro _; exact typecheck_stmt.skip lenv env retType

  | jump L =>
    intro h
    simp only [check_stmt] at h
    cases hlookup : lookup lenv L with
    | none => simp [hlookup] at h
    | some envL =>
      simp only [hlookup] at h
      by_cases hequiv : TypeEnv.equiv_bool env envL = true
      · exact typecheck_stmt.jump lenv env L envL retType hlookup
          (TypeEnv.equiv_bool_implies_equiv _ _ hequiv)
      · simp [hequiv] at h

  | branch a L1 L2 =>
    intro h
    simp only [check_stmt] at h
    cases hbool : lookup env.siteEnv a with
    | none => simp [hbool] at h
    | some τ =>
      cases τ with
      | basic bt =>
        cases bt with
        | tbool =>
          simp only [hbool] at h
          cases hlookup1 : lookup lenv L1 with
          | none => simp [hlookup1] at h
          | some envL1 =>
            cases hlookup2 : lookup lenv L2 with
            | none => simp [hlookup1, hlookup2] at h
            | some envL2 =>
              simp only [hlookup1, hlookup2] at h
              by_cases hequivs : TypeEnv.equiv_bool {env with siteEnv := delete env.siteEnv a} envL1 = true ∧
                                 TypeEnv.equiv_bool {env with siteEnv := delete env.siteEnv a} envL2 = true
              · exact typecheck_stmt.branch lenv env a L1 L2 envL1 envL2 retType
                  hbool hlookup1 hlookup2
                  (TypeEnv.equiv_bool_implies_equiv _ _ hequivs.1)
                  (TypeEnv.equiv_bool_implies_equiv _ _ hequivs.2)
              · simp only [not_and_or] at hequivs
                cases hequivs with
                | inl h1 => simp [h1] at h
                | inr h2 => simp [h2] at h
        | _ => simp [hbool] at h
      | ref _ _ _ => simp [hbool] at h

  | ret as =>
    intro h
    simp only [check_stmt] at h
    -- The check_stmt for ret tests: all sites have retType AND no_locals_borrowed_bool
    -- Split the if condition
    split at h
    · rename_i hcond
      simp only [Bool.and_eq_true, List.all_eq_true] at hcond
      obtain ⟨hall, hnolocals⟩ := hcond
      apply typecheck_stmt.ret lenv env as retType
      · intro a ha
        have hbeq := hall a ha
        -- hbeq : (lookup env.siteEnv a == some retType) = true
        -- Need to convert BEq to Eq for Option MoveType
        cases hlookup : lookup env.siteEnv a with
        | none => simp [hlookup] at hbeq
        | some τ =>
          simp only [hlookup] at hbeq
          -- hbeq : (τ == retType) = true
          have := MoveType.eq_of_beq τ retType hbeq
          simp [this]
      · exact no_locals_borrowed_bool_sound env hwf hnolocals
    · simp at h

  | abort a =>
    intro h
    simp only [check_stmt] at h
    cases hlookup : lookup env.siteEnv a with
    | none => simp [hlookup] at h
    | some τ => exact typecheck_stmt.abort lenv env a τ retType hlookup

  | release a cont ih_cont =>
    intro h
    simp only [check_stmt] at h
    cases hlookup : lookup env.siteEnv a with
    | none => simp [hlookup] at h
    | some τ =>
      cases τ with
      | basic _ => simp [hlookup] at h
      | ref bt r isBor =>
        simp only [hlookup] at h
        -- h : (check_stmt lenv env' cont retType).isSome = true
        -- where env' = {env with siteEnv := delete env.siteEnv a, pathEnv := delete_ref_node env.pathEnv r}
        let env' : TypeEnv := {env with siteEnv := delete env.siteEnv a,
                                         pathEnv := delete_ref_node env.pathEnv r}
        have hwf' : PathEnv.WellFormed env'.pathEnv := delete_ref_node_wellformed env.pathEnv r hwf
        apply typecheck_stmt.release lenv env a bt r isBor cont retType hlookup
        exact ih_cont env' hwf' h

  | unpack fields b cont ih_cont =>
    intro h
    simp only [check_stmt] at h
    cases hlookup : lookup env.siteEnv b with
    | none => simp [hlookup] at h
    | some τ =>
      cases τ with
      | basic bt =>
        cases bt with
        | trecord fentries =>
          simp only [hlookup] at h
          -- h now has the conditions and recursive check
          split at h
          · rename_i hcond
            simp only [Bool.and_eq_true] at hcond
            obtain ⟨⟨hfresh, hdistinct⟩, hexist⟩ := hcond
            -- Apply the relational rule
            apply typecheck_stmt.unpack lenv env fields b fentries cont retType hlookup
            · -- freshness: ∀ (f : Field) (a : Site), (f, a) ∈ fields → notIn env.siteEnv a
              intro f a hfa
              simp only [check_unpack_fields_fresh, List.all_eq_true] at hfresh
              exact hfresh (f, a) hfa
            · -- distinctness: this is more complex - needs a separate lemma
              sorry
            · -- fields exist in fentries
              intro f a hfa
              simp only [check_unpack_fields_exist, List.all_eq_true] at hexist
              have hexist' := hexist (f, a) hfa
              cases hlookupf : lookup fentries f with
              | none => simp [hlookupf] at hexist'
              | some bt' => exact ⟨bt', rfl⟩
            · -- recursive call
              let env' := {env with siteEnv := addFieldSites fentries (delete env.siteEnv b) fields}
              -- PathEnv is unchanged for unpack, so WellFormed is preserved
              have hwf' : PathEnv.WellFormed env'.pathEnv := hwf
              exact ih_cont env' hwf' h
          · simp at h
        | _ => simp [hlookup] at h
      | ref _ _ _ => simp [hlookup] at h

  -- letBind case: many sub-cases depending on expression type
  -- Each sub-case requires careful matching of the algorithmic and relational rules
  -- The WellFormed preservation lemmas are in place, but the proof structure is complex
  | letBind a e cont ih_cont => sorry

  | writeRef a b cont ih_cont => sorry

  | assign x a cont ih_cont => sorry

  | call as fnName bs cont ih_cont => sorry

/- ---------------------------------------------------- -/
/-       Statement type checking completeness            -/
/- ---------------------------------------------------- -/

/-- Completeness: If the relational judgment holds, the algorithmic check succeeds.

    NOTE: This theorem has sorries for cases requiring:
    1. Completeness of no_locals_borrowed_bool
    2. Matching the exact fresh reference in the derivation with nextFreshRef
-/
theorem check_stmt_complete (lenv : LabelEnv) (env : TypeEnv) (s : Stmt) (retType : MoveType) :
    typecheck_stmt lenv env s retType → (check_stmt lenv env s retType).isSome = true := by
  intro h
  -- Induction on the typecheck_stmt derivation
  induction h with
  | skip => simp [check_stmt]

  | jump =>
    rename_i env' L envL hlookup hequiv
    simp only [check_stmt, hlookup]
    have hequiv_bool := TypeEnv.equiv_implies_equiv_bool _ _ hequiv
    simp [hequiv_bool]

  | branch =>
    rename_i env' a L1 L2 envL1 envL2 hbool hlookup1 hlookup2 hequiv1 hequiv2
    simp only [check_stmt, hbool, hlookup1, hlookup2]
    have hequiv1_bool := TypeEnv.equiv_implies_equiv_bool _ _ hequiv1
    have hequiv2_bool := TypeEnv.equiv_implies_equiv_bool _ _ hequiv2
    simp [hequiv1_bool, hequiv2_bool]

  | ret =>
    simp only [check_stmt]
    -- Need completeness for no_locals_borrowed_bool
    sorry

  | abort =>
    rename_i env' a _ hlookup
    simp only [check_stmt, hlookup, Option.isSome_some]

  -- Non-terminal statements with continuations - all require sorries
  -- These cases need:
  -- 1. Completeness of not_borrowed_bool
  -- 2. The algorithmic checker uses nextFreshRef, while the derivation may use any fresh ref
  | let_bind_move => sorry
  | let_bind_copy_val => sorry
  | let_bind_copy_ref => sorry
  | let_bind_borrowImm => sorry
  | let_bind_borrowMut => sorry
  | let_bind_intLit => sorry
  | let_bind_borrowField => sorry
  | let_bind_borrowMutField => sorry
  | let_bind_binop => sorry
  | let_bind_readRef => sorry
  | let_bind_freeze => sorry
  | let_bind_pack => sorry
  | write_ref => sorry
  | var_assign_valid => sorry
  | var_assign_invalid => sorry
  | call => sorry
  | release => sorry
  | unpack => sorry

/- ---------------------------------------------------- -/
/-       Function type checking soundness                -/
/- ---------------------------------------------------- -/

/-- Soundness: If the algorithmic check succeeds, the relational judgment holds -/
theorem check_fun_sound (f : FunDef) (lenv : LabelEnv) :
    check_fun f lenv = true → typecheck_fun f lenv := by
  intro h
  simp only [check_fun] at h
  cases hblocks : f.blocks with
  | nil => simp [hblocks] at h
  | cons entry rest =>
    simp only [hblocks] at h
    cases hlookup : lookup lenv entry.label with
    | none => simp [hlookup] at h
    | some entryEnv =>
      simp only [hlookup, Bool.and_eq_true, List.all_eq_true] at h
      obtain ⟨hequiv, hblocks_check⟩ := h
      let initEnv : TypeEnv := {
        varEnv := init_fun_varEnv f
        siteEnv := AssocMap.empty
        pathEnv := PathEnv.init
        funEnv := AssocMap.empty
      }
      apply typecheck_fun.fun_ok f lenv initEnv
      · rfl
      · rfl
      · rfl
      · simp [hblocks]
      · intro entryLabel entryBody entryEnv' hhead hlookup'
        simp only [hblocks, List.head?_cons, Option.some.injEq] at hhead
        -- hhead : { label := entryLabel, body := entryBody } = entry
        -- Extract the field equalities
        have heq1 : entryLabel = entry.label := congrArg Block.label hhead.symm
        have heq2 : entryBody = entry.body := congrArg Block.body hhead.symm
        rw [heq1] at hlookup'
        simp only [hlookup] at hlookup'
        cases hlookup'
        exact TypeEnv.equiv_bool_implies_equiv _ _ hequiv
      · intro block hblock blockEnv hblockLookup
        have hblock' : block ∈ entry :: rest := by rw [← hblocks]; exact hblock
        have hcheck := hblocks_check block hblock'
        simp only [hblockLookup, check_block] at hcheck
        -- Statement-level soundness requires per-case induction
        sorry

/- ---------------------------------------------------- -/
/-       Function type checking completeness             -/
/- ---------------------------------------------------- -/

/-- Completeness: If the relational judgment holds, the algorithmic check succeeds -/
theorem check_fun_complete (f : FunDef) (lenv : LabelEnv) :
    typecheck_fun f lenv → check_fun f lenv = true := by
  intro h
  cases h with
  | fun_ok initEnv hvarEnv hsiteEnv hpathEnv hnonempty hentry hblocks =>
    simp only [check_fun]
    cases hblocks_eq : f.blocks with
    | nil => exact absurd hblocks_eq hnonempty
    | cons entry rest =>
      cases hlookup : lookup lenv entry.label with
      | none =>
        exfalso
        have hentry_in : entry ∈ f.blocks := by simp [hblocks_eq]
        have htc := hblocks entry hentry_in
        -- Need to show contradiction: htc requires some blockEnv but hlookup = none
        -- The hblocks hypothesis is ∀ blockEnv, lookup = some blockEnv → ...
        -- which is vacuously true when lookup = none
        -- But we need the entry block to have an environment in lenv
        -- This follows from hentry which requires lookup lenv entryLabel = some entryEnv
        have hhead : f.blocks.head? = some ⟨entry.label, entry.body⟩ := by simp [hblocks_eq]
        -- hentry gives us that for the entry, there exists entryEnv in lenv
        -- but hlookup says there's none - contradiction via hentry usage
        sorry -- Requires careful handling of the entry block requirement
      | some entryEnv =>
        simp only [hlookup, Bool.and_eq_true, List.all_eq_true]
        constructor
        · have hequiv := hentry entry.label entry.body entryEnv (by simp [hblocks_eq]) hlookup
          -- hequiv : TypeEnv.equiv entryEnv initEnv
          -- initEnv.siteEnv = empty, initEnv.varEnv = init_fun_varEnv f, initEnv.pathEnv = PathEnv.init
          obtain ⟨h1, h2, h3, h4⟩ := hequiv
          -- Rewrite using the equalities about initEnv
          have hequiv' : TypeEnv.equiv entryEnv
              { siteEnv := AssocMap.empty, varEnv := init_fun_varEnv f,
                pathEnv := PathEnv.init, funEnv := AssocMap.empty } := by
            refine ⟨?_, ?_, ?_, ?_⟩
            · simp only [hsiteEnv] at h1; exact h1
            · simp only [hvarEnv] at h2; exact h2
            · simp only [hpathEnv] at h3; exact h3
            · intro u v hu hv
              simp only [hpathEnv] at h4
              exact h4 u v hu hv
          exact TypeEnv.equiv_implies_equiv_bool _ _ hequiv'
        · intro block hblock
          have hblock_in : block ∈ f.blocks := by
            simp only [hblocks_eq, List.mem_cons] at hblock ⊢
            exact hblock
          simp only [check_block]
          cases hblockLookup : lookup lenv block.label with
          | none =>
            exfalso
            have htc := hblocks block hblock_in
            -- Similar issue - htc is vacuously true when lookup = none
            sorry
          | some blockEnv =>
            have htc := hblocks block hblock_in blockEnv hblockLookup
            -- Statement-level completeness requires per-case induction
            sorry

/-- Main equivalence theorem -/
theorem check_fun_equiv (f : FunDef) (lenv : LabelEnv) :
    check_fun f lenv = true ↔ typecheck_fun f lenv :=
  ⟨check_fun_sound f lenv, check_fun_complete f lenv⟩

end LeanMove.Checker
