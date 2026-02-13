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

import LeanMove.Typing.TypeChecking

/-!
# Type Environment Properties and Invariants

Generic definitions and lemmas about type environments, path environments,
and their invariants. These do not depend on the algorithmic type checker
and can be reused for semantic soundness proofs.

## Contents
- `freshRef` / `nextFreshRef` properties
- `PathEnv.WellFormed` — path environment invariant and preservation
- `SiteEnv.RefsNotRoot` / `VarEnv.RefsNotRoot` — reference invariants
- `VarEnv.RefsAreFresh` — stronger freshness invariant
- `TypeEnv.WellFormed` — combined environment invariant and preservation
- `varRef_fresh_when_not_borrowed` — key semantic property
- `call_connect_inputs_outputs_wf` — WellFormed preservation for call connections
-/

namespace LeanMove.Typing

open Lang
open Lang.MoveLight
open AssocMap
open Regex

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

/-- A path from root is a "borrow path" for variable x if it accepts [.root_to_var x].
    This happens when the path is char (.root_to_var x) or concat ε (char (.root_to_var x)). -/
def isBorrowPath (x : Var) (regex : Regex PathElement) : Prop :=
  match regex with
  | .char c => c = .root_to_var x
  | .concat .ε (.char c) => c = .root_to_var x
  | _ => False

/-- A path environment is well-formed if:
    1. Refs not in the refs list have empty paths from root
    2. VarRef x is in refs only if the path from root is a borrow path for x
    3. The root reference is always in the refs list -/
structure PathEnv.WellFormed (pe : PathEnv) : Prop where
  refs_complete : ∀ r, r ∉ pe.refs → pe.paths (.root, r) = .empty
  varref_tracked : ∀ x, Aref.varRef x ∈ pe.refs → isBorrowPath x (pe.paths (.root, Aref.varRef x))
  root_in_refs : Aref.root ∈ pe.refs

lemma PathEnv.init_wellformed : PathEnv.WellFormed PathEnv.init := by
  constructor
  · intro r hr
    simp only [PathEnv.init, List.mem_singleton] at hr
    simp only [PathEnv.init]
    by_cases heq : Aref.root = r
    · exact absurd heq.symm hr
    · simp [heq]
  · -- varref_tracked: varRef x is not in init.refs (which is just [.root])
    intro x hx
    simp only [PathEnv.init, List.mem_singleton] at hx
    -- hx says Aref.varRef x = Aref.root, which is false
    cases hx
  · -- root_in_refs: .root ∈ [.root]
    simp only [PathEnv.init, List.mem_singleton]

/-- delete_ref_node preserves WellFormed when r ≠ root.
    In practice, we never delete root - it's only used for borrow references. -/
lemma delete_ref_node_wellformed (pe : PathEnv) (r : Aref) (hwf : PathEnv.WellFormed pe)
    (hr_not_root : r ≠ Aref.root) :
    PathEnv.WellFormed (delete_ref_node pe r) := by
  constructor
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
  · -- varref_tracked preservation
    intro x hx
    simp only [delete_ref_node_refs, List.mem_filter, decide_eq_true_eq] at hx
    obtain ⟨hxin, hxne⟩ := hx
    -- varRef x was in pe.refs and varRef x ≠ r
    have hborrow := hwf.varref_tracked x hxin
    -- root ≠ r by hr_not_root
    have hroot_ne : Aref.root ≠ r := fun h => hr_not_root h.symm
    have := delete_ref_node_paths_not_involving_r pe r .root (Aref.varRef x) hroot_ne hxne
    simp only [this]
    exact hborrow
  · -- root_in_refs: .root survives filter since r ≠ .root
    simp only [delete_ref_node_refs, List.mem_filter, decide_eq_true_eq]
    exact ⟨hwf.root_in_refs, fun h => hr_not_root h.symm⟩

/-- nextFreshRef always returns a .refid, never .root or .varRef -/
lemma nextFreshRef_not_root (pe : PathEnv) : nextFreshRef pe ≠ Aref.root := by
  simp only [nextFreshRef]
  intro h
  cases h

/-- nextFreshRef returns a .refid -/
lemma nextFreshRef_is_refid (pe : PathEnv) : ∃ n, nextFreshRef pe = Aref.refid n := by
  simp only [nextFreshRef]
  exact ⟨_, rfl⟩

/-- nextFreshRef never returns a varRef -/
lemma nextFreshRef_not_varRef (pe : PathEnv) (x : Var) : nextFreshRef pe ≠ Aref.varRef x := by
  simp only [nextFreshRef]
  intro h
  cases h

/- ---------------------------------------------------- -/
/-       SiteEnv.RefsNotRoot invariant                   -/
/- ---------------------------------------------------- -/

/-- All references in a SiteEnv are not root.
    This invariant is maintained because refs come from:
    1. nextFreshRef (always .refid n)
    2. Function parameters (always .varRef x)
    3. Copies of existing refs (preserves non-root) -/
def SiteEnv.RefsNotRoot (senv : SiteEnv) : Prop :=
  ∀ s τ, lookup senv s = some τ →
    match τ with
    | .ref _ r _ => r ≠ Aref.root
    | .basic _ => True

/-- Empty siteEnv satisfies RefsNotRoot -/
lemma SiteEnv.empty_refs_not_root : SiteEnv.RefsNotRoot AssocMap.empty := by
  intro s τ h
  simp only [AssocMap.lookup, AssocMap.empty, List.lookup] at h
  cases h

/-- Inserting a non-root ref preserves RefsNotRoot -/
lemma SiteEnv.insert_refs_not_root (senv : SiteEnv) (s : Site) (τ : MoveType)
    (hwf : SiteEnv.RefsNotRoot senv)
    (hτ : match τ with | .ref _ r _ => r ≠ Aref.root | .basic _ => True) :
    SiteEnv.RefsNotRoot (insert senv s τ) := by
  intro s' τ' hlookup
  simp only [AssocMap.insert, AssocMap.lookup, List.lookup] at hlookup
  by_cases heq : s' == s
  · -- s' = s: the inserted value τ is returned
    simp only [heq] at hlookup
    cases hlookup
    exact hτ
  · -- s' ≠ s: lookup in the filtered original list
    simp only [heq] at hlookup
    have hne : s' ≠ s := by simp only [beq_iff_eq] at heq; exact heq
    have hlookup' : lookup senv s' = some τ' := by
      simp only [AssocMap.lookup]
      exact List.lookup_filter_of_lookup senv.entries s' s τ' hne hlookup
    exact hwf s' τ' hlookup'

/-- Deleting from siteEnv preserves RefsNotRoot.
    The key insight: any value in the filtered siteEnv was also in the original,
    and all values in the original satisfy RefsNotRoot. -/
lemma SiteEnv.delete_refs_not_root (senv : SiteEnv) (s : Site)
    (hwf : SiteEnv.RefsNotRoot senv) :
    SiteEnv.RefsNotRoot (delete senv s) := by
  intro s' τ' hlookup
  simp only [AssocMap.delete, AssocMap.lookup] at hlookup
  -- s' ≠ s, otherwise lookup would return none
  have hne : s' ≠ s := by
    intro heq
    have hself := List.lookup_filter_self_none senv.entries s
    rw [heq] at hlookup
    rw [hself] at hlookup
    cases hlookup
  -- Lookup in filtered list equals lookup in original
  have hlookup' : lookup senv s' = some τ' := by
    simp only [AssocMap.lookup]
    rw [← List.lookup_filter_ne senv.entries s' s hne]
    exact hlookup
  exact hwf s' τ' hlookup'

/-- Deleting multiple sites from siteEnv preserves RefsNotRoot -/
lemma SiteEnv.deleteAll_refs_not_root (senv : SiteEnv) (ss : List Site)
    (hwf : SiteEnv.RefsNotRoot senv) :
    SiteEnv.RefsNotRoot (deleteAll senv ss) := by
  intro s' τ' hlookup
  simp only [AssocMap.deleteAll, AssocMap.lookup] at hlookup
  -- s' ∉ ss, otherwise lookup would return none
  have hnotin : s' ∉ ss := by
    intro hmem
    have := List.lookup_filter_mem_none senv.entries s' ss hmem
    rw [this] at hlookup
    cases hlookup
  -- Lookup in filtered list equals lookup in original
  have hlookup' : lookup senv s' = some τ' := by
    simp only [AssocMap.lookup]
    rw [← List.lookup_filter_notin senv.entries s' ss hnotin]
    exact hlookup
  exact hwf s' τ' hlookup'

/-- addFieldSites preserves RefsNotRoot because it only inserts basic types -/
lemma addFieldSites_refs_not_root (fentries : AssocMap Field BasicMoveType)
    (se : SiteEnv) (fields : List (Field × Site))
    (hwf : SiteEnv.RefsNotRoot se) :
    SiteEnv.RefsNotRoot (addFieldSites fentries se fields) := by
  unfold addFieldSites
  induction fields generalizing se with
  | nil => simp [List.foldl]; exact hwf
  | cons hd tl ih =>
    simp only [List.foldl]
    apply ih
    cases lookup fentries hd.1 with
    | none => exact hwf
    | some bt => exact SiteEnv.insert_refs_not_root se hd.2 (.basic bt) hwf trivial

/- ---------------------------------------------------- -/
/-       VarEnv.RefsNotRoot invariant                    -/
/- ---------------------------------------------------- -/

/-- All references in a VarEnv are not root.
    VarEnv entries are tuples (IsValid, MoveType, Mut).
    We require that all reference types have refs that are not root. -/
def VarEnv.RefsNotRoot (venv : VarEnv) : Prop :=
  ∀ x entry, lookup venv x = some entry →
    match entry.2.1 with  -- entry = (isValid, (τ, mut)), so entry.2.1 = τ
    | .ref _ r _ => r ≠ Aref.root
    | .basic _ => True

/-- Empty varEnv satisfies RefsNotRoot -/
lemma VarEnv.empty_refs_not_root : VarEnv.RefsNotRoot AssocMap.empty := by
  intro x entry h
  simp only [AssocMap.lookup, AssocMap.empty, List.lookup] at h
  cases h

/-- Inserting a non-root ref preserves VarEnv.RefsNotRoot -/
lemma VarEnv.insert_refs_not_root (venv : VarEnv) (x : Var) (entry : IsValid × MoveType × Mut)
    (hwf : VarEnv.RefsNotRoot venv)
    (hentry : match entry.2.1 with | .ref _ r _ => r ≠ Aref.root | .basic _ => True) :
    VarEnv.RefsNotRoot (insert venv x entry) := by
  intro x' entry' hlookup
  simp only [AssocMap.insert, AssocMap.lookup, List.lookup] at hlookup
  by_cases heq : x' == x
  · simp only [heq] at hlookup
    cases hlookup
    exact hentry
  · simp only [heq] at hlookup
    have hne : x' ≠ x := by simp only [beq_iff_eq] at heq; exact heq
    have hlookup' : lookup venv x' = some entry' := by
      simp only [AssocMap.lookup]
      exact List.lookup_filter_of_lookup venv.entries x' x entry' hne hlookup
    exact hwf x' entry' hlookup'

/-- Updating (which is same as insert for AssocMap) preserves VarEnv.RefsNotRoot -/
lemma VarEnv.update_refs_not_root (venv : VarEnv) (x : Var) (entry : IsValid × MoveType × Mut)
    (hwf : VarEnv.RefsNotRoot venv)
    (hentry : match entry.2.1 with | .ref _ r _ => r ≠ Aref.root | .basic _ => True) :
    VarEnv.RefsNotRoot (update venv x entry) := by
  -- update is the same as insert for AssocMap
  exact VarEnv.insert_refs_not_root venv x entry hwf hentry

/-- If we lookup a type from a VarEnv that satisfies RefsNotRoot,
    the type satisfies the refs-not-root condition -/
lemma VarEnv.lookup_refs_not_root (venv : VarEnv) (x : Var) (entry : IsValid × MoveType × Mut)
    (hwf : VarEnv.RefsNotRoot venv) (hlookup : lookup venv x = some entry) :
    match entry.2.1 with | .ref _ r _ => r ≠ Aref.root | .basic _ => True :=
  hwf x entry hlookup

/-- Helper function: predicate that a MoveType's ref is not root -/
def moveTypeRefsNotRoot (τ : MoveType) : Prop :=
  match τ with | .ref _ r _ => r ≠ Aref.root | .basic _ => True

/-- Helper: extract the type condition for a specific MoveType from varEnv lookup -/
lemma VarEnv.lookup_type_refs_not_root (venv : VarEnv) (x : Var) (isValid : IsValid) (τ : MoveType) (m : Mut)
    (hwf : VarEnv.RefsNotRoot venv) (hlookup : lookup venv x = some (isValid, τ, m)) :
    moveTypeRefsNotRoot τ := by
  have h := hwf x (isValid, τ, m) hlookup
  cases τ <;> exact h

/-- moveTypeRefsNotRoot unfolds to the match expression -/
lemma moveTypeRefsNotRoot_eq (τ : MoveType) :
    moveTypeRefsNotRoot τ = (match τ with | .ref _ r _ => r ≠ Aref.root | .basic _ => True) := by
  cases τ <;> rfl

/-- An Aref is a "fresh ref" if it's a refid (not root or varRef) -/
def Aref.isFreshRef (a : Aref) : Prop := ∃ n, a = Aref.refid n

lemma Aref.isFreshRef_not_root (a : Aref) (h : Aref.isFreshRef a) : a ≠ Aref.root := by
  obtain ⟨n, hn⟩ := h
  rw [hn]
  intro hcontra
  cases hcontra

lemma Aref.isFreshRef_not_varRef (a : Aref) (h : Aref.isFreshRef a) (x : Var) : a ≠ Aref.varRef x := by
  obtain ⟨n, hn⟩ := h
  rw [hn]
  intro hcontra
  cases hcontra

lemma nextFreshRef_isFreshRef (pe : PathEnv) : Aref.isFreshRef (nextFreshRef pe) := by
  exact nextFreshRef_is_refid pe

/-- If r1 is a fresh ref and r1 is Aref-compatible with r2, then r2 is also a fresh ref. -/
lemma Aref.Compatible_preserves_freshRef (r1 r2 : Aref)
    (hfresh : Aref.isFreshRef r1) (hcompat : Aref.Compatible r1 r2) : Aref.isFreshRef r2 := by
  obtain ⟨n, hn⟩ := hfresh
  subst hn
  cases r2 with
  | refid m => exact ⟨m, rfl⟩
  | root => exact absurd hcompat (by simp [Aref.Compatible])
  | varRef _ => exact absurd hcompat (by simp [Aref.Compatible])

/-- Helper function: predicate that a MoveType's ref is a fresh ref (refid) -/
def moveTypeIsFreshRef (τ : MoveType) : Prop :=
  match τ with | .ref _ r _ => Aref.isFreshRef r | .basic _ => True

/-- If τ has a fresh ref and τ' is compatible with τ, then τ' also has a fresh ref. -/
lemma MoveType.compatible_preserves_freshRef (τ τ' : MoveType)
    (hfresh : moveTypeIsFreshRef τ) (hcompat : MoveType.compatible τ τ') : moveTypeIsFreshRef τ' := by
  cases τ with
  | basic bt =>
    cases τ' with
    | basic _ => trivial
    | ref _ _ _ => exact absurd hcompat (by simp [MoveType.compatible])
  | ref bt r bk =>
    cases τ' with
    | basic _ => exact absurd hcompat (by simp [MoveType.compatible])
    | ref bt' r' bk' =>
      simp only [MoveType.compatible] at hcompat
      obtain ⟨_, hr, _⟩ := hcompat
      simp only [moveTypeIsFreshRef] at hfresh ⊢
      exact Aref.Compatible_preserves_freshRef r r' hfresh hr

/-- All references in a VarEnv are fresh refs (refids).
    This is a stronger invariant than RefsNotRoot. -/
def VarEnv.RefsAreFresh (venv : VarEnv) : Prop :=
  ∀ x entry, lookup venv x = some entry →
    match entry.2.1 with
    | .ref _ r _ => Aref.isFreshRef r
    | .basic _ => True

/-- RefsAreFresh implies RefsNotRoot -/
lemma VarEnv.refsAreFresh_implies_refsNotRoot (venv : VarEnv) (h : VarEnv.RefsAreFresh venv) :
    VarEnv.RefsNotRoot venv := by
  intro x entry hlookup
  have hfresh := h x entry hlookup
  cases hτ : entry.2.1 with
  | basic _ => trivial
  | ref bt r bk =>
    simp only [hτ] at hfresh ⊢
    exact Aref.isFreshRef_not_root r hfresh

/-- Empty varEnv satisfies RefsAreFresh -/
lemma VarEnv.empty_refs_are_fresh : VarEnv.RefsAreFresh AssocMap.empty := by
  intro x entry h
  simp only [AssocMap.lookup, AssocMap.empty, List.lookup] at h
  cases h

/-- Inserting a fresh ref preserves VarEnv.RefsAreFresh -/
lemma VarEnv.insert_refs_are_fresh (venv : VarEnv) (x : Var) (entry : IsValid × MoveType × Mut)
    (hwf : VarEnv.RefsAreFresh venv)
    (hentry : moveTypeIsFreshRef entry.2.1) :
    VarEnv.RefsAreFresh (insert venv x entry) := by
  intro x' entry' hlookup
  simp only [AssocMap.insert, AssocMap.lookup, List.lookup] at hlookup
  by_cases heq : x' == x
  · simp only [heq] at hlookup
    cases hlookup
    simp only [moveTypeIsFreshRef] at hentry
    cases hτ : entry.2.1 <;> simp only ; simp only [hτ] at hentry ; exact hentry
  · simp only [heq] at hlookup
    have hne : x' ≠ x := by simp only [beq_iff_eq] at heq; exact heq
    have hlookup' : lookup venv x' = some entry' := by
      simp only [AssocMap.lookup]
      exact List.lookup_filter_of_lookup venv.entries x' x entry' hne hlookup
    exact hwf x' entry' hlookup'

/-- Updating preserves VarEnv.RefsAreFresh -/
lemma VarEnv.update_refs_are_fresh (venv : VarEnv) (x : Var) (entry : IsValid × MoveType × Mut)
    (hwf : VarEnv.RefsAreFresh venv)
    (hentry : moveTypeIsFreshRef entry.2.1) :
    VarEnv.RefsAreFresh (update venv x entry) := by
  exact VarEnv.insert_refs_are_fresh venv x entry hwf hentry

/-- Lookup from RefsAreFresh gives a fresh ref type -/
lemma VarEnv.lookup_type_is_fresh (venv : VarEnv) (x : Var) (isValid : IsValid) (τ : MoveType) (m : Mut)
    (hwf : VarEnv.RefsAreFresh venv) (hlookup : lookup venv x = some (isValid, τ, m)) :
    moveTypeIsFreshRef τ := by
  have h := hwf x (isValid, τ, m) hlookup
  cases τ <;> exact h

/- ---------------------------------------------------- -/
/-       Combined TypeEnv.WellFormed                     -/
/- ---------------------------------------------------- -/

/-- A type environment is well-formed if:
    1. The path environment is well-formed
    2. All references in siteEnv are not root
    3. All references in varEnv are fresh refs (refids) -/
structure TypeEnv.WellFormed (env : TypeEnv) : Prop where
  pathEnv_wf : PathEnv.WellFormed env.pathEnv
  siteEnv_wf : SiteEnv.RefsNotRoot env.siteEnv
  varEnv_wf : VarEnv.RefsAreFresh env.varEnv

/-- Helper: get RefsNotRoot from WellFormed -/
lemma TypeEnv.WellFormed.varEnv_refs_not_root (hwf : TypeEnv.WellFormed env) :
    VarEnv.RefsNotRoot env.varEnv :=
  VarEnv.refsAreFresh_implies_refsNotRoot env.varEnv hwf.varEnv_wf

/-- Initial TypeEnv with empty siteEnv and PathEnv.init is well-formed
    when the provided varEnv satisfies RefsAreFresh -/
lemma TypeEnv.init_wellformed (varEnv : VarEnv) (funEnv : FunEnv)
    (hvarEnv : VarEnv.RefsAreFresh varEnv) :
    TypeEnv.WellFormed { siteEnv := AssocMap.empty, varEnv := varEnv, pathEnv := PathEnv.init, funEnv := funEnv } := by
  constructor
  · exact PathEnv.init_wellformed
  · exact SiteEnv.empty_refs_not_root
  · exact hvarEnv

/-- Updating siteEnv with insert preserves TypeEnv.WellFormed if the new type satisfies RefsNotRoot -/
lemma TypeEnv.insert_siteEnv_wf (env : TypeEnv) (s : Site) (τ : MoveType) (hwf : TypeEnv.WellFormed env)
    (hτ : match τ with | .ref _ r _ => r ≠ Aref.root | .basic _ => True) :
    TypeEnv.WellFormed {env with siteEnv := insert env.siteEnv s τ} := by
  constructor
  · exact hwf.pathEnv_wf
  · exact SiteEnv.insert_refs_not_root env.siteEnv s τ hwf.siteEnv_wf hτ
  · exact hwf.varEnv_wf

/-- Updating siteEnv with delete preserves TypeEnv.WellFormed -/
lemma TypeEnv.delete_siteEnv_wf (env : TypeEnv) (s : Site) (hwf : TypeEnv.WellFormed env) :
    TypeEnv.WellFormed {env with siteEnv := delete env.siteEnv s} := by
  constructor
  · exact hwf.pathEnv_wf
  · exact SiteEnv.delete_refs_not_root env.siteEnv s hwf.siteEnv_wf
  · exact hwf.varEnv_wf

/-- Updating siteEnv with deleteAll preserves TypeEnv.WellFormed -/
lemma TypeEnv.deleteAll_siteEnv_wf (env : TypeEnv) (ss : List Site) (hwf : TypeEnv.WellFormed env) :
    TypeEnv.WellFormed {env with siteEnv := deleteAll env.siteEnv ss} := by
  constructor
  · exact hwf.pathEnv_wf
  · exact SiteEnv.deleteAll_refs_not_root env.siteEnv ss hwf.siteEnv_wf
  · exact hwf.varEnv_wf

/-- Updating varEnv preserves TypeEnv.WellFormed if the new entry satisfies RefsAreFresh -/
lemma TypeEnv.update_varEnv_wf (env : TypeEnv) (x : Var) (v : IsValid × MoveType × Mut)
    (hwf : TypeEnv.WellFormed env)
    (hv : moveTypeIsFreshRef v.2.1) :
    TypeEnv.WellFormed {env with varEnv := update env.varEnv x v} := by
  constructor
  · exact hwf.pathEnv_wf
  · exact hwf.siteEnv_wf
  · exact VarEnv.update_refs_are_fresh env.varEnv x v hwf.varEnv_wf hv

/-- Combined update: insert site and update varEnv preserves WellFormed -/
lemma TypeEnv.insert_update_wf (env : TypeEnv) (s : Site) (τ : MoveType) (x : Var) (v : IsValid × MoveType × Mut)
    (hwf : TypeEnv.WellFormed env)
    (hτ : match τ with | .ref _ r _ => r ≠ Aref.root | .basic _ => True)
    (hv : moveTypeIsFreshRef v.2.1) :
    TypeEnv.WellFormed {env with siteEnv := insert env.siteEnv s τ, varEnv := update env.varEnv x v} := by
  constructor
  · exact hwf.pathEnv_wf
  · exact SiteEnv.insert_refs_not_root env.siteEnv s τ hwf.siteEnv_wf hτ
  · exact VarEnv.update_refs_are_fresh env.varEnv x v hwf.varEnv_wf hv

/-- Combined: insert site and update pathEnv preserves WellFormed -/
lemma TypeEnv.insert_pathEnv_wf (env : TypeEnv) (s : Site) (τ : MoveType) (pe' : PathEnv)
    (hwf : TypeEnv.WellFormed env) (hpe : PathEnv.WellFormed pe')
    (hτ : match τ with | .ref _ r _ => r ≠ Aref.root | .basic _ => True) :
    TypeEnv.WellFormed {env with siteEnv := insert env.siteEnv s τ, pathEnv := pe'} := by
  constructor
  · exact hpe
  · exact SiteEnv.insert_refs_not_root env.siteEnv s τ hwf.siteEnv_wf hτ
  · exact hwf.varEnv_wf

/-- Combined: delete+insert site and update pathEnv preserves WellFormed -/
lemma TypeEnv.delete_insert_pathEnv_wf (env : TypeEnv) (sdel sins : Site) (τ : MoveType) (pe' : PathEnv)
    (hwf : TypeEnv.WellFormed env) (hpe : PathEnv.WellFormed pe')
    (hτ : match τ with | .ref _ r _ => r ≠ Aref.root | .basic _ => True) :
    TypeEnv.WellFormed {env with siteEnv := insert (delete env.siteEnv sdel) sins τ, pathEnv := pe'} := by
  constructor
  · exact hpe
  · have hdel := SiteEnv.delete_refs_not_root env.siteEnv sdel hwf.siteEnv_wf
    exact SiteEnv.insert_refs_not_root (delete env.siteEnv sdel) sins τ hdel hτ
  · exact hwf.varEnv_wf

/-- Combined: delete+delete+insert site preserves WellFormed -/
lemma TypeEnv.delete_delete_insert_wf (env : TypeEnv) (s1 s2 sins : Site) (τ : MoveType)
    (hwf : TypeEnv.WellFormed env)
    (hτ : match τ with | .ref _ r _ => r ≠ Aref.root | .basic _ => True) :
    TypeEnv.WellFormed {env with siteEnv := insert (delete (delete env.siteEnv s1) s2) sins τ} := by
  constructor
  · exact hwf.pathEnv_wf
  · have hdel1 := SiteEnv.delete_refs_not_root env.siteEnv s1 hwf.siteEnv_wf
    have hdel2 := SiteEnv.delete_refs_not_root (delete env.siteEnv s1) s2 hdel1
    exact SiteEnv.insert_refs_not_root _ sins τ hdel2 hτ
  · exact hwf.varEnv_wf

/-- Combined: deleteAll+insert site preserves WellFormed -/
lemma TypeEnv.deleteAll_insert_wf (env : TypeEnv) (ss : List Site) (sins : Site) (τ : MoveType)
    (hwf : TypeEnv.WellFormed env)
    (hτ : match τ with | .ref _ r _ => r ≠ Aref.root | .basic _ => True) :
    TypeEnv.WellFormed {env with siteEnv := insert (deleteAll env.siteEnv ss) sins τ} := by
  constructor
  · exact hwf.pathEnv_wf
  · have hdel := SiteEnv.deleteAll_refs_not_root env.siteEnv ss hwf.siteEnv_wf
    exact SiteEnv.insert_refs_not_root _ sins τ hdel hτ
  · exact hwf.varEnv_wf

/-- update_with_extension preserves WellFormed when z ≠ root and z is not a varRef.
    In practice, z is always a fresh ref from nextFreshRef (never .root or varRef). -/
lemma update_with_extension_wellformed (z x : Aref) (path : List PathElement) (pe : PathEnv)
    (hwf : PathEnv.WellFormed pe) (hz_not_root : z ≠ Aref.root)
    (hz_not_varRef : ∀ v, z ≠ Aref.varRef v) :
    PathEnv.WellFormed (update_with_extension z x path pe) := by
  have hnotz : Aref.root ≠ z := fun h => hz_not_root h.symm
  constructor
  · -- refs_complete: refs not in list have empty paths from root
    intro r hr
    simp only [update_with_extension] at hr ⊢
    have hnotboth : ¬(Aref.root = z ∧ r = z) := fun h => hz_not_root h.1.symm
    simp only [hnotboth, ↓reduceIte]
    by_cases hzin : z ∈ pe.refs
    · -- z already in refs, so refs' = pe.refs
      simp only [hzin, not_true_eq_false, ↓reduceIte] at hr
      have hempty := hwf.refs_complete r hr
      by_cases hrz : r = z
      · exact absurd (hrz ▸ hzin) hr
      · simp only [hrz, hnotz, ↓reduceIte]
        exact hempty
    · -- z not in refs, so refs' = z :: pe.refs
      simp only [hzin, not_false_eq_true, ↓reduceIte, List.mem_cons, not_or] at hr
      obtain ⟨hrz, hrnot⟩ := hr
      have hempty := hwf.refs_complete r hrnot
      simp only [hrz, hnotz, ↓reduceIte]
      exact hempty
  · -- varref_tracked: varRef x' in refs implies borrow path
    intro x' hx'
    simp only [update_with_extension] at hx' ⊢
    by_cases hzin : z ∈ pe.refs
    · -- z already in refs
      simp only [hzin, not_true_eq_false, ↓reduceIte] at hx'
      have hborrow := hwf.varref_tracked x' hx'
      by_cases hvz : Aref.varRef x' = z
      · -- varRef x' = z: impossible since z is not a varRef
        exact absurd hvz.symm (hz_not_varRef x')
      · have hnotboth : ¬(Aref.root = z ∧ Aref.varRef x' = z) := fun h => hz_not_root h.1.symm
        simp only [hvz, hnotz, ↓reduceIte]
        exact hborrow
    · -- z not in refs
      simp only [hzin, not_false_eq_true, ↓reduceIte, List.mem_cons] at hx'
      cases hx' with
      | inl hvz =>
        -- varRef x' = z: impossible since z is not a varRef
        exact absurd hvz.symm (hz_not_varRef x')
      | inr hx'in =>
        have hborrow := hwf.varref_tracked x' hx'in
        by_cases hvz : Aref.varRef x' = z
        · exact absurd (hvz ▸ hx'in) hzin
        · have hnotboth : ¬(Aref.root = z ∧ Aref.varRef x' = z) := fun h => hz_not_root h.1.symm
          simp only [hvz, hnotz, ↓reduceIte]
          exact hborrow
  · -- root_in_refs: .root stays in refs (z ≠ .root so root was already there)
    simp only [update_with_extension]
    by_cases hzin : z ∈ pe.refs
    · simp only [hzin, not_true_eq_false, ↓reduceIte]
      exact hwf.root_in_refs
    · simp only [hzin, not_false_eq_true, ↓reduceIte, List.mem_cons]
      exact Or.inr hwf.root_in_refs

/-- update_with_epsilon preserves WellFormed -/
lemma update_with_epsilon_wellformed (s t : Aref) (pe : PathEnv) (hwf : PathEnv.WellFormed pe)
    (hs_not_root : s ≠ Aref.root) (hs_not_varRef : ∀ v, s ≠ Aref.varRef v) :
    PathEnv.WellFormed (update_with_epsilon s t pe) := by
  unfold update_with_epsilon
  exact update_with_extension_wellformed s t [] pe hwf hs_not_root hs_not_varRef

/-- garbage_collect preserves WellFormed.
    Removes ref r from refs and clears all paths involving r. -/
lemma garbage_collect_wellformed (pe : PathEnv) (r : Aref) (hwf : PathEnv.WellFormed pe)
    (hr_not_root : r ≠ Aref.root) :
    PathEnv.WellFormed (garbage_collect pe r) := by
  constructor
  · -- refs_complete: refs not in list have empty paths from root
    intro v hv
    simp only [garbage_collect, List.mem_filter, decide_eq_true_eq] at hv
    simp only [garbage_collect]
    -- v ∉ filter (≠ r) pe.refs means: ¬(v ∈ pe.refs ∧ v ≠ r) = v ∉ pe.refs ∨ v = r
    by_cases hvr : v = r
    · -- v = r: path from root to r is empty (condition is true since r = r)
      subst hvr
      simp only [or_true, ↓reduceIte]
    · -- v ≠ r: v ∉ pe.refs, so original path was empty
      have hvnotin : v ∉ pe.refs := by
        intro hcontra
        exact hv ⟨hcontra, hvr⟩
      have horiginal := hwf.refs_complete v hvnotin
      -- Now show the new path is also empty
      have hcond : ¬(Aref.root = r ∨ v = r) := by
        intro hcontra
        cases hcontra with
        | inl h => exact hr_not_root h.symm
        | inr h => exact hvr h
      simp only [hcond, ↓reduceIte]
      exact horiginal
  · -- varref_tracked: varRef x in refs implies borrow path
    intro x hx
    simp only [garbage_collect, List.mem_filter, decide_eq_true_eq] at hx
    obtain ⟨hxin, hxne⟩ := hx
    simp only [garbage_collect]
    -- varRef x ≠ r, and root ≠ r, so the path is unchanged
    have hcond : ¬(Aref.root = r ∨ Aref.varRef x = r) := by
      intro hcontra
      cases hcontra with
      | inl h => exact hr_not_root h.symm
      | inr h => exact hxne h
    simp only [hcond, ↓reduceIte]
    exact hwf.varref_tracked x hxin
  · -- root_in_refs: .root survives filter since r ≠ .root
    simp only [garbage_collect, List.mem_filter, decide_eq_true_eq]
    exact ⟨hwf.root_in_refs, fun h => hr_not_root h.symm⟩

/-- consume_ref_transfer preserves WellFormed.
    Transfers edges from r to r' and removes r. -/
lemma consume_ref_transfer_wellformed (pe : PathEnv) (r r' : Aref) (hwf : PathEnv.WellFormed pe)
    (hr_not_root : r ≠ Aref.root)
    (hr'_fresh : r' ∉ pe.refs) (hr'_not_varRef : ∀ v, r' ≠ Aref.varRef v) :
    PathEnv.WellFormed (consume_ref_transfer pe r r') := by
  constructor
  · -- refs_complete: refs not in new list have empty paths from root
    intro v hv
    simp only [consume_ref_transfer] at hv ⊢
    -- Determine if root = r ∨ v = r
    by_cases hvr : Aref.root = r ∨ v = r
    · -- Path is empty
      simp only [hvr, ↓reduceIte]
    · -- root ≠ r and v ≠ r
      have hroot_ne_r : Aref.root ≠ r := fun h => hvr (Or.inl h)
      have hv_ne_r : v ≠ r := fun h => hvr (Or.inr h)
      simp only [hvr, ↓reduceIte]
      by_cases hvr' : v = r'
      · -- v = r': r' should be in new refs, contradiction with hv
        exfalso
        apply hv
        simp only [hr'_fresh, not_false_eq_true, ↓reduceIte, List.mem_filter, decide_eq_true_eq,
                    List.mem_cons]
        exact ⟨Or.inl hvr', hv_ne_r⟩
      · -- v ≠ r': path is G(root, v)
        simp only [hvr', ↓reduceIte]
        have hv_notin : v ∉ pe.refs := by
          intro hcontra
          apply hv
          simp only [hr'_fresh, not_false_eq_true, ↓reduceIte, List.mem_filter, decide_eq_true_eq,
                      List.mem_cons]
          exact ⟨Or.inr hcontra, hv_ne_r⟩
        exact hwf.refs_complete v hv_notin
  · -- varref_tracked: varRef x in new refs implies borrow path
    intro x hx
    simp only [consume_ref_transfer] at hx ⊢
    simp only [hr'_fresh, not_false_eq_true, ↓reduceIte, List.mem_filter, decide_eq_true_eq,
                List.mem_cons] at hx
    obtain ⟨hxin, hx_ne_r⟩ := hx
    -- varRef x ≠ r and (varRef x = r' ∨ varRef x ∈ pe.refs)
    -- But r' is not a varRef, so varRef x ≠ r'
    have hvx_ne_r' : Aref.varRef x ≠ r' := fun h => absurd h.symm (hr'_not_varRef x)
    have hxin_orig : Aref.varRef x ∈ pe.refs := by
      cases hxin with
      | inl h => exact absurd h hvx_ne_r'
      | inr h => exact h
    -- root ≠ r and varRef x ≠ r, so condition is false
    have hcond : ¬(Aref.root = r ∨ Aref.varRef x = r) := by
      intro hcontra
      cases hcontra with
      | inl h => exact hr_not_root h.symm
      | inr h => exact hx_ne_r h
    simp only [hcond, ↓reduceIte]
    -- varRef x ≠ r', so path is G(root, varRef x)
    simp only [hvx_ne_r', ↓reduceIte]
    exact hwf.varref_tracked x hxin_orig
  · -- root_in_refs: .root survives filter since r ≠ .root
    simp only [consume_ref_transfer]
    have hroot_ne_r : Aref.root ≠ r := fun h => hr_not_root h.symm
    by_cases hr'in : r' ∈ pe.refs
    · simp only [hr'in, not_true_eq_false, ↓reduceIte, List.mem_filter, decide_eq_true_eq]
      exact ⟨hwf.root_in_refs, hroot_ne_r⟩
    · simp only [hr'in, not_false_eq_true, ↓reduceIte, List.mem_filter, decide_eq_true_eq,
                  List.mem_cons]
      exact ⟨Or.inr hwf.root_in_refs, hroot_ne_r⟩

/- ---------------------------------------------------- -/
/-       TypeEnv.equiv lemmas                            -/
/- ---------------------------------------------------- -/

lemma TypeEnv.equiv_refl (env : TypeEnv) : TypeEnv.equiv env env := by
  exact ⟨LookupEquiv.refl _, VarEnvLookupCompatible.refl _, rfl, fun _ _ _ _ => rfl⟩

/- ---------------------------------------------------- -/
/-       varRef freshness lemma                          -/
/- ---------------------------------------------------- -/

/-- Key lemma: If a variable is not borrowed (paths from root don't accept [.root_to_var x]),
    then its varRef is fresh (not in pathEnv.refs).
    This uses the varref_tracked invariant from WellFormed. -/
lemma varRef_fresh_when_not_borrowed (x : Var) (pe : PathEnv) (hwf : PathEnv.WellFormed pe) :
    (∀ r, ¬ Regex.interpret_regex (pe.paths (.root, r)) [.root_to_var x]) →
    freshRefBool (Aref.varRef x) pe = true := by
  intro hnotbor
  -- We need to show varRef x ∉ pe.refs
  unfold freshRefBool
  simp only [Bool.not_eq_true', List.contains_eq_any_beq]
  rw [List.any_eq_false]
  intro r hr
  simp only [beq_iff_eq]
  intro heq
  -- heq : varRef x = r, so r = varRef x
  subst heq
  -- By varref_tracked: varRef x ∈ pe.refs → isBorrowPath x (pe.paths (.root, varRef x))
  have hborrow := hwf.varref_tracked x hr
  -- isBorrowPath means the path is char (.root_to_var x) or concat ε (char (.root_to_var x))
  -- Either way, the path accepts [.root_to_var x]
  have haccepts : Regex.interpret_regex (pe.paths (.root, Aref.varRef x)) [.root_to_var x] := by
    unfold isBorrowPath at hborrow
    generalize hpath : pe.paths (.root, Aref.varRef x) = p at hborrow ⊢
    cases p with
    | char c =>
      simp only [Regex.interpret_regex]
      exact congrArg (fun c => [c]) hborrow.symm
    | concat r1 r2 =>
      cases r1 with
      | ε =>
        cases r2 with
        | char c =>
          simp only [Regex.interpret_regex]
          exact ⟨[], [.root_to_var x], rfl, rfl, congrArg (fun c => [c]) hborrow.symm⟩
        | _ => exact False.elim hborrow
      | _ => exact False.elim hborrow
    | _ => exact False.elim hborrow
  -- But hnotbor says for all r, the path doesn't accept [.root_to_var x]
  exact hnotbor (Aref.varRef x) haccepts

/- ---------------------------------------------------- -/
/-       call_connect_inputs_outputs WellFormed          -/
/- ---------------------------------------------------- -/

/-- call_connect_inputs_outputs preserves WellFormed when outputs are fresh -/
lemma call_connect_inputs_outputs_wf (env : TypeEnv) (as bs : List Site)
    (hwf : TypeEnv.WellFormed env)
    (hfresh : all_fresh_sites env as) :
    TypeEnv.WellFormed (call_connect_inputs_outputs env as bs) := by
  -- All output sites have lookup = none
  simp only [all_fresh_sites] at hfresh
  rw [List.all_eq_true] at hfresh
  have hlookup_none : ∀ a ∈ as, lookup env.siteEnv a = none :=
    fun a ha => notIn_implies_lookup_none env.siteEnv a (hfresh a ha)
  -- call_connect_inputs_outputs only changes pathEnv; siteEnv and varEnv are unchanged
  constructor
  · -- pathEnv_wf: show pathEnv is unchanged because io=[] and mo=[]
    show PathEnv.WellFormed (call_connect_inputs_outputs env as bs).pathEnv
    unfold call_connect_inputs_outputs
    -- When all outputs are fresh, io and mo filterMaps over `as` give [].
    -- Use rw with _ for f to let Lean's unifier match the exact lambda.
    rw [List.filterMap_all_none as _ (fun a ha => by simp [hlookup_none a ha])]
    rw [List.filterMap_all_none as _ (fun a ha => by simp [hlookup_none a ha])]
    -- Now io=[] and mo=[], so foldls over [] are identity, pathEnv = env.pathEnv
    exact hwf.pathEnv_wf
  · exact hwf.siteEnv_wf
  · exact hwf.varEnv_wf

end LeanMove.Typing
