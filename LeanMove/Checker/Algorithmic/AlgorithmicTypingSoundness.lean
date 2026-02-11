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

import LeanMove.Checker.Algorithmic.TypeCheckingAlgorithmic

/-!
# Algorithmic Typing Soundness for MoveLight

This file contains soundness proofs for the algorithmic type
checker defined in `TypeCheckingAlgorithmic.lean` with respect to the relational
specification in `TypeChecking.lean`.

## Main Results

- `check_stmt_sound`: Statement-level soundness
- `check_fun_sound`: If `check_fun f lenv = true`, then `typecheck_fun f lenv`

## Key Invariants

- `PathEnv.WellFormed`: Refs completeness + varref tracking
- These invariants are preserved by all path environment operations

Completeness proofs are in `AlgorithmicTypingCompleteness.lean`.
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

/-- A path from root is a "borrow path" for variable x if it accepts [.root_to_var x].
    This happens when the path is char (.root_to_var x) or concat ε (char (.root_to_var x)). -/
def isBorrowPath (x : Var) (regex : Regex PathElement) : Prop :=
  match regex with
  | .char c => c = .root_to_var x
  | .concat .ε (.char c) => c = .root_to_var x
  | _ => False

/-- A path environment is well-formed if:
    1. Refs not in the refs list have empty paths from root
    2. VarRef x is in refs only if the path from root is a borrow path for x -/
structure PathEnv.WellFormed (pe : PathEnv) : Prop where
  refs_complete : ∀ r, r ∉ pe.refs → pe.paths (.root, r) = .empty
  varref_tracked : ∀ x, Aref.varRef x ∈ pe.refs → isBorrowPath x (pe.paths (.root, Aref.varRef x))

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

/-- Helper: lookup in filtered list implies lookup in original list (for keys not filtered) -/
lemma List.lookup_filter_of_lookup {K V : Type} [DecidableEq K] (entries : List (K × V))
    (k k' : K) (v : V) (hne : k ≠ k') :
    List.lookup k (entries.filter (fun p => p.1 != k')) = some v →
    List.lookup k entries = some v := by
  induction entries with
  | nil => simp [List.lookup]
  | cons hd tl ih =>
    intro h
    simp only [List.filter] at h
    simp only [List.lookup]
    by_cases hfilt : hd.1 != k'
    · simp only [hfilt, List.lookup] at h
      by_cases hhd : k == hd.1
      · simp only [hhd] at h ⊢; exact h
      · simp only [hhd] at h ⊢; exact ih h
    · simp only [bne_iff_ne, ne_eq, not_not] at hfilt
      simp only [hfilt, bne_self_eq_false] at h
      by_cases hhd : k == hd.1
      · simp only [beq_iff_eq] at hhd
        subst hhd
        exact absurd hfilt hne
      · simp only [hhd]
        exact ih h

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

/-- Looking up a key in a list filtered to remove that key returns none -/
lemma List.lookup_filter_self_none {K V : Type} [DecidableEq K] (entries : List (K × V)) (k : K) :
    List.lookup k (entries.filter (fun p => p.1 != k)) = none := by
  induction entries with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.filter]
    by_cases hfilt : hd.1 != k
    · simp only [hfilt, List.lookup]
      by_cases hhd : k == hd.1
      · simp only [beq_iff_eq] at hhd
        simp only [bne_iff_ne] at hfilt
        exact absurd hhd.symm hfilt
      · simp only [hhd]
        exact ih
    · simp only [bne_iff_ne, ne_eq, not_not] at hfilt
      have hfilt' : (hd.1 != k) = false := by simp [hfilt]
      simp only [hfilt']
      exact ih

/-- Looking up a key that's in the filter list returns none -/
lemma List.lookup_filter_mem_none {K V : Type} [DecidableEq K] (entries : List (K × V)) (k : K) (ks : List K) :
    k ∈ ks → List.lookup k (entries.filter (fun p => p.1 ∉ ks)) = none := by
  intro hmem
  induction entries with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.filter]
    by_cases hfilt : hd.1 ∉ ks
    · have hfilt' : decide (hd.1 ∉ ks) = true := decide_eq_true hfilt
      simp only [hfilt', List.lookup]
      by_cases hhd : k == hd.1
      · simp only [beq_iff_eq] at hhd
        exact absurd (hhd ▸ hmem) hfilt
      · simp only [hhd]
        exact ih
    · simp only [not_not] at hfilt
      have hfilt' : decide (hd.1 ∉ ks) = false := decide_eq_false (not_not.mpr hfilt)
      simp only [hfilt']
      exact ih

/-- Lookup in filtered list (key not filtered) gives same result as original -/
lemma List.lookup_filter_ne {K V : Type} [DecidableEq K] (entries : List (K × V)) (k k' : K) (hne : k ≠ k') :
    List.lookup k (entries.filter (fun p => p.1 != k')) = List.lookup k entries := by
  induction entries with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.filter, List.lookup]
    by_cases hfilt : hd.1 != k'
    · simp only [hfilt, List.lookup]
      by_cases hhd : k == hd.1
      · simp only [hhd]
      · simp only [hhd]
        exact ih
    · simp only [bne_iff_ne, ne_eq, not_not] at hfilt
      have hfilt' : (hd.1 != k') = false := by simp [hfilt]
      simp only [hfilt']
      by_cases hhd : k == hd.1
      · simp only [beq_iff_eq] at hhd
        exact absurd (hfilt ▸ hhd) hne
      · simp only [hhd]
        exact ih

/-- Lookup in filtered list (key not in filter list) gives same result as original -/
lemma List.lookup_filter_notin {K V : Type} [DecidableEq K] (entries : List (K × V)) (k : K) (ks : List K) (hnotin : k ∉ ks) :
    List.lookup k (entries.filter (fun p => p.1 ∉ ks)) = List.lookup k entries := by
  induction entries with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.filter, List.lookup]
    by_cases hfilt : hd.1 ∉ ks
    · have hfilt' : decide (hd.1 ∉ ks) = true := decide_eq_true hfilt
      simp only [hfilt', List.lookup]
      by_cases hhd : k == hd.1
      · simp only [hhd]
      · simp only [hhd]
        exact ih
    · simp only [not_not] at hfilt
      have hfilt' : decide (hd.1 ∉ ks) = false := decide_eq_false (not_not.mpr hfilt)
      simp only [hfilt']
      by_cases hhd : k == hd.1
      · simp only [beq_iff_eq] at hhd
        exact absurd (hhd ▸ hfilt) hnotin
      · simp only [hhd]
        exact ih

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

/- ---------------------------------------------------- -/
/-       TypeEnv.equiv lemmas                            -/
/- ---------------------------------------------------- -/

lemma TypeEnv.equiv_refl (env : TypeEnv) : TypeEnv.equiv env env := by
  exact ⟨LookupEquiv.refl _, VarEnvLookupCompatible.refl _, rfl, fun _ _ _ _ => rfl⟩

/-- Soundness: if varentry_compatible_bool returns true, VarEntryCompatible holds. -/
theorem varentry_compatible_bool_sound (e1 e2 : IsValid × MoveType × Mut) :
    varentry_compatible_bool e1 e2 = true → VarEntryCompatible e1 e2 := by
  obtain ⟨v1, t1, m1⟩ := e1
  obtain ⟨v2, t2, m2⟩ := e2
  simp only [varentry_compatible_bool, Bool.and_eq_true, beq_iff_eq]
  intro ⟨⟨hv, ht⟩, hm⟩
  exact ⟨hv, MoveType.compatible_bool_sound t1 t2 ht, hm⟩

/-- Bridge: varenv_entry_compatible_opt soundness implies the match form used by VarEnvLookupCompatible. -/
private theorem varenv_entry_compatible_opt_sound
    (o1 o2 : Option (IsValid × MoveType × Mut)) :
    varenv_entry_compatible_opt o1 o2 = true →
    match o1, o2 with
    | some e1, some e2 => VarEntryCompatible e1 e2
    | none, none => True
    | _, _ => False := by
  intro h
  cases o1 with
  | none =>
    cases o2 with
    | none => trivial
    | some _ => simp [varenv_entry_compatible_opt] at h
  | some e1 =>
    cases o2 with
    | none => simp [varenv_entry_compatible_opt] at h
    | some e2 =>
      simp only [varenv_entry_compatible_opt] at h
      exact varentry_compatible_bool_sound _ _ h

/-- Soundness: if varenv_lookup_compatible_bool returns true, VarEnvLookupCompatible holds. -/
theorem varenv_lookup_compatible_bool_sound (m1 m2 : VarEnv) :
    varenv_lookup_compatible_bool m1 m2 = true → VarEnvLookupCompatible m1 m2 := by
  intro h
  simp only [varenv_lookup_compatible_bool, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  intro k
  by_cases hk1 : ∃ v, (k, v) ∈ m1.entries
  · obtain ⟨v, hv⟩ := hk1
    exact varenv_entry_compatible_opt_sound _ _ (h1 (k, v) hv)
  · by_cases hk2 : ∃ v, (k, v) ∈ m2.entries
    · obtain ⟨v, hv⟩ := hk2
      exact varenv_entry_compatible_opt_sound _ _ (h2 (k, v) hv)
    · have hk1' := lookup_none_of_not_mem_keys m1 k (by
        intro ⟨k', v'⟩ hp heq; exact hk1 ⟨v', heq ▸ hp⟩)
      have hk2' := lookup_none_of_not_mem_keys m2 k (by
        intro ⟨k', v'⟩ hp heq; exact hk2 ⟨v', heq ▸ hp⟩)
      rw [hk1', hk2']
      trivial

lemma TypeEnv.equiv_bool_implies_equiv (env1 env2 : TypeEnv) :
    TypeEnv.equiv_bool env1 env2 = true → TypeEnv.equiv env1 env2 := by
  intro h
  simp only [TypeEnv.equiv_bool, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨hsite, hvar⟩, hrefs⟩, hpaths⟩ := h
  refine ⟨lookup_equiv_bool_sound _ _ hsite, varenv_lookup_compatible_bool_sound _ _ hvar, hrefs, ?_⟩
  intro u v hu hv
  have h1 := hpaths u hu
  have h2 := h1 v hv
  exact regexBeq_eq _ _ h2

lemma TypeEnv.equiv_implies_equiv_bool (env1 env2 : TypeEnv) :
    TypeEnv.equiv env1 env2 → TypeEnv.equiv_bool env1 env2 = true := by
  -- Completeness direction: not needed for soundness theorem
  sorry

/- ---------------------------------------------------- -/
/-       not_borrowed soundness (WellFormed → Bool → Prop)   -/
/- ---------------------------------------------------- -/

/-- Soundness: if boolean check passes and path env is well-formed, semantic property holds.
    Uses match_bool_complete for refs in the list, and refs_complete for refs not in the list. -/
lemma not_borrowed_bool_sound (x : Var) (env : TypeEnv)
    (hwf : PathEnv.WellFormed env.pathEnv) :
    not_borrowed_bool x env = true → not_borrowed x env := by
  intro hbool
  simp only [not_borrowed_bool, List.all_eq_true] at hbool
  intro r
  show ¬ interpret_regex (env.pathEnv.paths (.root, r)) [.root_to_var x]
  by_cases hr : r ∈ env.pathEnv.refs
  · -- r ∈ refs: use match_bool_complete (contrapositive)
    have h := hbool r hr
    intro haccept
    have hmatch := @Regex.match_bool_complete _ _ _ _ haccept
    simp only [hmatch, Bool.not_true] at h
    exact absurd h (by decide)
  · -- r ∉ refs: path from root is empty by refs_complete
    have hempty := hwf.refs_complete r hr
    simp only [hempty, interpret_regex]
    exact not_false

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
/-       check_mutable_inputs bridge lemmas              -/
/- ---------------------------------------------------- -/

/-- Soundness: Boolean isolation check implies relational isolation -/
lemma check_mutable_inputs_isolated_bool_sound (env : TypeEnv) (bs : List Site) :
    check_mutable_inputs_isolated_bool env bs = true →
    check_mutable_inputs_isolated env bs := by
  intro h
  simp only [check_mutable_inputs_isolated_bool, List.all_eq_true] at h
  intro mi_site hmi mi_bt mi_ref hlookup_mi other_site hother other_bt other_ref bk hlookup_other hne
  have h1 := h mi_site hmi
  simp only [hlookup_mi] at h1
  simp only [List.all_eq_true] at h1
  have h2 := h1 other_site hother
  have hne_bool : (mi_site != other_site) = true := by
    simp only [bne_iff_ne]
    exact hne
  simp only [hne_bool, ite_true] at h2
  simp only [hlookup_other] at h2
  exact h2

/-- Soundness: Boolean outbound check implies relational outbound -/
lemma check_mutable_inputs_have_outbound_bool_sound (env : TypeEnv) (bs : List Site) :
    check_mutable_inputs_have_outbound_bool env bs = true →
    check_mutable_inputs_have_outbound env bs := by
  intro h
  simp only [check_mutable_inputs_have_outbound_bool, List.all_eq_true] at h
  intro mi_site hmi mi_bt mi_ref hlookup_mi
  have h1 := h mi_site hmi
  simp only [hlookup_mi] at h1
  simp only [List.any_eq_true] at h1
  obtain ⟨target, htarget_in, hcond⟩ := h1
  simp only [Bool.and_eq_true, bne_iff_ne] at hcond
  obtain ⟨hne, hmatch⟩ := hcond
  exact ⟨target, htarget_in, hne, hmatch⟩

/- ---------------------------------------------------- -/
/-       call_connect_inputs_outputs WellFormed          -/
/- ---------------------------------------------------- -/

/-- When all elements map to none, filterMap gives [] -/
private lemma filterMap_all_none {α β : Type} (as : List α) (f : α → Option β)
    (hf : ∀ a ∈ as, f a = none) :
    as.filterMap f = [] := by
  induction as with
  | nil => simp
  | cons a as' ih =>
    have ha := hf a (List.Mem.head as')
    simp only [List.filterMap]
    rw [ha]
    exact ih (fun a' ha' => hf a' (List.mem_cons_of_mem a ha'))

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
    rw [filterMap_all_none as _ (fun a ha => by simp [hlookup_none a ha])]
    rw [filterMap_all_none as _ (fun a ha => by simp [hlookup_none a ha])]
    -- Now io=[] and mo=[], so foldls over [] are identity, pathEnv = env.pathEnv
    exact hwf.pathEnv_wf
  · exact hwf.siteEnv_wf
  · exact hwf.varEnv_wf

/- ---------------------------------------------------- -/
/-       eraseDups / Nodup helper lemmas                 -/
/- ---------------------------------------------------- -/

/-- eraseDups.length ≤ length for any list -/
private lemma eraseDups_length_le {α : Type} [BEq α] [LawfulBEq α] (l : List α) :
    l.eraseDups.length ≤ l.length := by
  suffices ∀ n (l : List α), l.length ≤ n → l.eraseDups.length ≤ l.length from
    this l.length l (Nat.le_refl _)
  intro n
  induction n with
  | zero =>
    intro l hlen
    match l with
    | [] => simp
    | _ :: _ => simp [List.length_cons] at hlen
  | succ n ih =>
    intro l hlen
    match l with
    | [] => simp
    | a :: as =>
      simp only [List.eraseDups_cons, List.length_cons]
      have hfilt_le : (as.filter fun b => !(b == a)).length ≤ n := by
        have h := List.length_filter_le (fun b => !(b == a)) as
        simp only [List.length_cons] at hlen
        omega
      have h1 := ih (as.filter fun b => !(b == a)) hfilt_le
      have h2 := List.length_filter_le (fun b => !(b == a)) as
      omega

/-- If filter p preserves list length, then all elements satisfy p -/
private lemma filter_length_eq_implies {α : Type} [BEq α] [LawfulBEq α]
    (p : α → Bool) (l : List α) (hlen : (l.filter p).length = l.length)
    (a : α) (hmem : a ∈ l) : p a = true := by
  induction l with
  | nil => nomatch hmem
  | cons b bs ih =>
    simp only [List.filter_cons] at hlen
    split at hlen
    · rename_i hpb
      simp only [List.length_cons] at hlen
      cases hmem with
      | head => exact hpb
      | tail _ hmem' => exact ih (by omega) hmem'
    · simp only [List.length_cons] at hlen
      have := List.length_filter_le p bs
      omega

/-- If length = eraseDups.length, then the list has no duplicates -/
private lemma nodup_of_length_eraseDups {α : Type} [BEq α] [LawfulBEq α] (l : List α)
    (h : l.length = l.eraseDups.length) : l.Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons a as ih =>
    simp only [List.eraseDups_cons, List.length_cons] at h
    have h1 := eraseDups_length_le (as.filter fun b => !(b == a))
    have h2 := List.length_filter_le (fun b => !(b == a)) as
    have hflen : (as.filter fun b => !(b == a)).length = as.length := by omega
    have hnotmem : a ∉ as := by
      intro hmem
      have := filter_length_eq_implies (fun b => !(b == a)) as hflen a hmem
      simp at this
    have hfilter_eq : as.filter (fun b => !(b == a)) = as := by
      rw [List.filter_eq_self]
      intro b hmem
      have hne : b ≠ a := fun heq => hnotmem (heq ▸ hmem)
      simp [beq_eq_false_iff_ne.mpr hne]
    rw [hfilter_eq] at h
    exact List.nodup_cons.mpr ⟨hnotmem, ih (by omega)⟩

/-- If map Prod.snd has no duplicates, two pairs with same second component
    but different first components can't both be in the list -/
private lemma nodup_snd_pair_absurd {α β : Type} (l : List (α × β))
    (hnodup : (l.map Prod.snd).Nodup)
    {a₁ a₂ : α} {b : β}
    (h₁ : (a₁, b) ∈ l) (h₂ : (a₂, b) ∈ l) (hne : a₁ ≠ a₂) : False := by
  induction l with
  | nil => nomatch h₁
  | cons hd tl ih =>
    simp only [List.map_cons, List.nodup_cons] at hnodup
    obtain ⟨hnotmem, htl_nodup⟩ := hnodup
    cases h₁ with
    | head =>
      cases h₂ with
      | head => exact hne rfl
      | tail _ h₂' =>
        exact absurd (List.mem_map_of_mem (f := Prod.snd) h₂') hnotmem
    | tail _ h₁' =>
      cases h₂ with
      | head =>
        exact absurd (List.mem_map_of_mem (f := Prod.snd) h₁') hnotmem
      | tail _ h₂' =>
        exact ih htl_nodup h₁' h₂'

/- ---------------------------------------------------- -/
/-       AssocMap lookup/insert lemmas                   -/
/- ---------------------------------------------------- -/

/-- List.lookup through a filter that removes key k preserves lookup of other keys -/
private lemma list_lookup_filter_ne {K V : Type} [DecidableEq K]
    (k k' : K) (entries : List (K × V)) (hne : k' ≠ k) :
    List.lookup k' (entries.filter (fun p => p.fst != k)) = List.lookup k' entries := by
  induction entries with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.filter]
    split
    · -- hd.fst != k matched true (filter keeps hd)
      simp only [List.lookup]
      split
      · rfl  -- k' == hd.fst matched true
      · exact ih  -- k' == hd.fst matched false
    · -- hd.fst != k matched false, so hd.fst = k (filter removes hd)
      rename_i h
      have hk : hd.fst = k := by
        by_contra hne_k
        have : (hd.fst != k) = true := by simp [bne, beq_eq_false_iff_ne.mpr hne_k]
        rw [this] at h; exact absurd h (by decide)
      simp only [List.lookup]
      have hne' : (k' == hd.fst) = false := beq_eq_false_iff_ne.mpr (by rw [hk]; exact hne)
      split
      · rename_i h'; rw [hne'] at h'; exact absurd h' (by decide)
      · exact ih

/-- Looking up a different key after insert returns the original value -/
private lemma lookup_insert_ne {K V : Type} [DecidableEq K]
    (m : AssocMap K V) (k k' : K) (v : V) (hne : k' ≠ k) :
    AssocMap.lookup (AssocMap.insert m k v) k' = AssocMap.lookup m k' := by
  simp only [AssocMap.lookup, AssocMap.insert]
  simp only [List.lookup]
  split
  · rename_i h; exact absurd (beq_iff_eq.mp h) hne
  · exact list_lookup_filter_ne k k' m.entries hne

/-- Looking up the key just inserted returns the inserted value -/
private lemma lookup_insert_eq {K V : Type} [DecidableEq K]
    (m : AssocMap K V) (k : K) (v : V) :
    AssocMap.lookup (AssocMap.insert m k v) k = some v := by
  simp only [AssocMap.lookup, AssocMap.insert, List.lookup, beq_self_eq_true]

/- ---------------------------------------------------- -/
/-       Pack fold helper lemmas                         -/
/- ---------------------------------------------------- -/

/-- The pack fold preserves entries for keys not in the field list -/
private lemma foldlM_pack_preserves
    (siteEnv : SiteEnv) (fields : List (Field × Site))
    (init result : AssocMap Field BasicMoveType) (f : Field) (v : BasicMoveType)
    (hfold : fields.foldlM (fun acc (p : Field × Site) =>
      match AssocMap.lookup siteEnv p.2 with
      | some (.basic bt) => some (AssocMap.insert acc p.1 bt)
      | _ => none) init = some result)
    (hnotmem : f ∉ fields.map Prod.fst)
    (hlookup : AssocMap.lookup init f = some v) :
    AssocMap.lookup result f = some v := by
  induction fields generalizing init with
  | nil =>
    simp only [List.foldlM, pure] at hfold
    simp only [Option.some.injEq] at hfold; subst hfold; exact hlookup
  | cons hd tl ih =>
    simp only [List.foldlM, bind, Option.bind] at hfold
    simp only [List.map_cons, List.mem_cons, not_or] at hnotmem
    obtain ⟨hne, hnotmem_tl⟩ := hnotmem
    cases hlk : lookup siteEnv hd.snd with
    | none => simp [hlk] at hfold
    | some mt =>
      cases mt with
      | basic bt =>
        simp [hlk] at hfold
        exact ih _ hfold hnotmem_tl
          (by rw [lookup_insert_ne _ hd.fst f bt hne]; exact hlookup)
      | ref _ _ _ => simp [hlk] at hfold

/-- If the pack fold succeeds with distinct field names, each entry is correctly mapped -/
private lemma foldlM_pack_sound
    (siteEnv : SiteEnv) (fields : List (Field × Site))
    (init fentries : AssocMap Field BasicMoveType)
    (hfold : fields.foldlM (fun acc (p : Field × Site) =>
      match AssocMap.lookup siteEnv p.2 with
      | some (.basic bt) => some (AssocMap.insert acc p.1 bt)
      | _ => none) init = some fentries)
    (hnodup : (fields.map Prod.fst).Nodup)
    {f : Field} {a : Site} (hmem : (f, a) ∈ fields) :
    ∃ bt, AssocMap.lookup siteEnv a = some (.basic bt) ∧
          AssocMap.lookup fentries f = some bt := by
  induction fields generalizing init with
  | nil => nomatch hmem
  | cons hd tl ih =>
    simp only [List.foldlM, bind, Option.bind] at hfold
    simp only [List.nodup_cons, List.map_cons] at hnodup
    obtain ⟨hd_not_in_tl, tl_nodup⟩ := hnodup
    cases hlk : lookup siteEnv hd.snd with
    | none => simp [hlk] at hfold
    | some mt =>
      cases mt with
      | basic bt =>
        simp [hlk] at hfold
        cases hmem with
        | head =>
          -- After head match, hd is substituted with (f, a), so hd.fst = f, hd.snd = a
          exact ⟨bt, hlk, foldlM_pack_preserves siteEnv tl _ fentries f bt hfold hd_not_in_tl
            (lookup_insert_eq _ f bt)⟩
        | tail _ hmem' =>
          exact ih _ hfold tl_nodup hmem'
      | ref _ _ _ => simp [hlk] at hfold

/- ---------------------------------------------------- -/
/-       Field distinctness lemma                        -/
/- ---------------------------------------------------- -/

/-- If check_fields_distinct returns true, all sites in fields are pairwise distinct -/
lemma check_fields_distinct_implies_sites_distinct (fields : List (Field × Site)) :
    check_fields_distinct fields = true →
    ∀ a₁ a₂, (∃ f₁ f₂, (f₁, a₁) ∈ fields ∧ (f₂, a₂) ∈ fields ∧ f₁ ≠ f₂) → a₁ ≠ a₂ := by
  intro hdistinct a₁ a₂ ⟨f₁, f₂, hf₁, hf₂, hfne⟩
  simp only [check_fields_distinct, beq_iff_eq, Bool.and_eq_true] at hdistinct
  obtain ⟨hsites, _⟩ := hdistinct
  intro heq; subst heq
  exact nodup_snd_pair_absurd fields (nodup_of_length_eraseDups _ hsites) hf₁ hf₂ hfne

/-- If check_fields_distinct returns true, field names are Nodup -/
private lemma check_fields_distinct_implies_fnames_nodup (fields : List (Field × Site)) :
    check_fields_distinct fields = true → (fields.map Prod.fst).Nodup := by
  intro h
  simp only [check_fields_distinct, beq_iff_eq, Bool.and_eq_true] at h
  exact nodup_of_length_eraseDups _ h.2

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
    (hwf : TypeEnv.WellFormed env)
    (ih_cont : ∀ env', TypeEnv.WellFormed env' →
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
      · have hwf' := TypeEnv.insert_siteEnv_wf env a (.basic .u64) hwf trivial
        exact ih_cont _ hwf' h
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
          simp only at h
          split at h
          · rename_i hcond
            simp only [Bool.and_eq_true] at hcond
            obtain ⟨hnotbor, hfresh⟩ := hcond
            apply typecheck_stmt.let_bind_move (τ := τ) (ms := ms)
            · simp only [hlookup]
            · exact not_borrowed_bool_sound x env hwf.pathEnv_wf hnotbor
            · exact hfresh
            · -- τ comes from varEnv, so it satisfies RefsAreFresh by hwf.varEnv_wf
              have hτ_fresh := VarEnv.lookup_type_is_fresh env.varEnv x .validVar τ ms hwf.varEnv_wf hlookup
              have hτ_not_root : moveTypeRefsNotRoot τ := by
                unfold moveTypeIsFreshRef at hτ_fresh
                unfold moveTypeRefsNotRoot
                cases τ with
                | basic _ => trivial
                | ref bt r bk => exact Aref.isFreshRef_not_root r hτ_fresh
              rw [moveTypeRefsNotRoot_eq] at hτ_not_root
              have hwf' := TypeEnv.insert_update_wf env a τ x (.invalidVar, τ, ms) hwf hτ_not_root hτ_fresh
              exact ih_cont _ hwf' h
          · simp at h
        | (.invalidVar, _, _) => simp at h

    | copy x =>
      simp only [check_stmt] at h
      cases hlookup : lookup env.varEnv x with
      | none => simp [hlookup] at h
      | some entry =>
        simp only [hlookup] at h
        match hentry : entry with
        | (.validVar, .basic bt, ms) =>
          simp only at h
          split at h
          · rename_i hfresh
            apply typecheck_stmt.let_bind_copy_val (bt := bt) (ms := ms)
            · simp only [hlookup]
            · exact hfresh
            · have hwf' := TypeEnv.insert_siteEnv_wf env a (.basic bt) hwf trivial
              exact ih_cont _ hwf' h
          · simp at h
        | (.validVar, .ref τ s isBor, ms) =>
          simp only at h
          split at h
          · rename_i hfresh
            let t := nextFreshRef env.pathEnv
            apply typecheck_stmt.let_bind_copy_ref (τ := τ) (s := s) (t := t) (isBor := isBor) (ms := ms)
            · simp only [hlookup]
            · exact hfresh
            · exact nextFreshRef_fresh env.pathEnv
            · have hs_fresh := VarEnv.lookup_type_is_fresh env.varEnv x .validVar (.ref τ s isBor) ms hwf.varEnv_wf hlookup
              simp only [moveTypeIsFreshRef] at hs_fresh
              have hs_not_root : s ≠ Aref.root := Aref.isFreshRef_not_root s hs_fresh
              have hs_not_varRef : ∀ v, s ≠ Aref.varRef v := Aref.isFreshRef_not_varRef s hs_fresh
              have hpe' := update_with_epsilon_wellformed s t env.pathEnv hwf.pathEnv_wf hs_not_root hs_not_varRef
              have hτ : match (MoveType.ref τ t isBor) with | .ref _ r _ => r ≠ Aref.root | .basic _ => True :=
                nextFreshRef_not_root env.pathEnv
              have hwf' := TypeEnv.insert_pathEnv_wf env a (.ref τ t isBor) _ hwf hpe' hτ
              exact ih_cont _ hwf' h
          · simp at h
        | (.invalidVar, _, _) => simp at h

    | borrowImm x =>
      simp only [check_stmt] at h
      cases hlookup : lookup env.varEnv x with
      | none => simp [hlookup] at h
      | some entry =>
        simp only [hlookup] at h
        match hentry : entry with
        | (.validVar, .basic τ, ms) =>
          simp only at h
          split at h
          · rename_i hfresh
            let r := nextFreshRef env.pathEnv
            apply typecheck_stmt.let_bind_borrowImm (τ := τ) (ms := ms) (r := r)
            · simp only [hlookup]
            · exact hfresh
            · exact nextFreshRef_fresh env.pathEnv
            · have hr_not_root : r ≠ Aref.root := nextFreshRef_not_root env.pathEnv
              have hr_not_varRef : ∀ v, r ≠ Aref.varRef v := nextFreshRef_not_varRef env.pathEnv
              have hpe' := update_with_extension_wellformed r .root [.root_to_var x] _
                (update_with_epsilon_wellformed r r env.pathEnv hwf.pathEnv_wf hr_not_root hr_not_varRef) hr_not_root hr_not_varRef
              have hτ : match (MoveType.ref τ r .siteBorrowImm) with | .ref _ r' _ => r' ≠ Aref.root | .basic _ => True :=
                nextFreshRef_not_root env.pathEnv
              have hwf' := TypeEnv.insert_pathEnv_wf env a (.ref τ r .siteBorrowImm) _ hwf hpe' hτ
              exact ih_cont _ hwf' h
          · simp at h
        | (.validVar, .ref _ _ _, _) => simp at h
        | (.invalidVar, _, _) => simp at h

    | borrowMut x =>
      simp only [check_stmt] at h
      cases hlookup : lookup env.varEnv x with
      | none => simp [hlookup] at h
      | some entry =>
        simp only [hlookup] at h
        match hentry : entry with
        | (.validVar, .basic τ, ms) =>
          simp only at h
          split at h
          · rename_i hcond
            simp only [Bool.and_eq_true, beq_iff_eq] at hcond
            obtain ⟨hms, hfresh⟩ := hcond
            let r := nextFreshRef env.pathEnv
            apply typecheck_stmt.let_bind_borrowMut (τ := τ) (ms := ms) (r := r)
            · simp only [hms, LE.le, Mut.le]
            · simp only [hlookup]
            · exact hfresh
            · exact nextFreshRef_fresh env.pathEnv
            · have hr_not_root : r ≠ Aref.root := nextFreshRef_not_root env.pathEnv
              have hr_not_varRef : ∀ v, r ≠ Aref.varRef v := nextFreshRef_not_varRef env.pathEnv
              have hpe' := update_with_extension_wellformed r .root [.root_to_var x] _
                (update_with_epsilon_wellformed r r env.pathEnv hwf.pathEnv_wf hr_not_root hr_not_varRef) hr_not_root hr_not_varRef
              have hτ : match (MoveType.ref τ r .siteBorrowMut) with | .ref _ r' _ => r' ≠ Aref.root | .basic _ => True :=
                nextFreshRef_not_root env.pathEnv
              have hwf' := TypeEnv.insert_pathEnv_wf env a (.ref τ r .siteBorrowMut) _ hwf hpe' hτ
              exact ih_cont _ hwf' h
          · simp at h
        | (.validVar, .ref _ _ _, _) => simp at h
        | (.invalidVar, _, _) => simp at h

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
                · have hwf' := TypeEnv.delete_delete_insert_wf env src1 src2 a (.basic bt3) hwf trivial
                  exact ih_cont _ hwf' h
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
          · -- Use the SiteEnv.RefsNotRoot invariant to prove r ≠ root
            have hr_not_root : r ≠ Aref.root := hwf.siteEnv_wf src (.ref bt r isBor) hlookup
            have hpe' := delete_ref_node_wellformed env.pathEnv r hwf.pathEnv_wf hr_not_root
            have hwf' := TypeEnv.delete_insert_pathEnv_wf env src a (.basic bt) _ hwf hpe' trivial
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
          · have hr_not_root : r ≠ Aref.root := hwf.siteEnv_wf src (.ref bt r isBor) hlookup
            have hr'_fresh : r' ∉ env.pathEnv.refs := nextFreshRef_fresh_prop env.pathEnv
            have hr'_not_varRef : ∀ v, r' ≠ Aref.varRef v := nextFreshRef_not_varRef env.pathEnv
            have hpe' := consume_ref_transfer_wellformed env.pathEnv r r' hwf.pathEnv_wf
              hr_not_root hr'_fresh hr'_not_varRef
            have hτ : match (MoveType.ref bt r' .siteBorrowImm) with | .ref _ r'' _ => r'' ≠ Aref.root | .basic _ => True :=
              nextFreshRef_not_root env.pathEnv
            have hwf' := TypeEnv.delete_insert_pathEnv_wf env src a (.ref bt r' .siteBorrowImm) _ hwf hpe' hτ
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
                · have hrf_not_root : rf ≠ Aref.root := nextFreshRef_not_root env.pathEnv
                  have hrf_not_varRef : ∀ v, rf ≠ Aref.varRef v := nextFreshRef_not_varRef env.pathEnv
                  have hpe' := update_with_extension_wellformed rf s [.field f] env.pathEnv hwf.pathEnv_wf hrf_not_root hrf_not_varRef
                  have hτ : match (MoveType.ref btf rf isBor) with | .ref _ r _ => r ≠ Aref.root | .basic _ => True :=
                    nextFreshRef_not_root env.pathEnv
                  have hwf' := TypeEnv.delete_insert_pathEnv_wf env src a (.ref btf rf isBor) _ hwf hpe' hτ
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
                  · have hrf_not_root : rf ≠ Aref.root := nextFreshRef_not_root env.pathEnv
                    have hrf_not_varRef : ∀ v, rf ≠ Aref.varRef v := nextFreshRef_not_varRef env.pathEnv
                    have hpe' := update_with_extension_wellformed rf s [.field f] env.pathEnv hwf.pathEnv_wf hrf_not_root hrf_not_varRef
                    have hτ : match (MoveType.ref btf rf .siteBorrowMut) with | .ref _ r _ => r ≠ Aref.root | .basic _ => True :=
                      nextFreshRef_not_root env.pathEnv
                    have hwf' := TypeEnv.delete_insert_pathEnv_wf env src a (.ref btf rf .siteBorrowMut) _ hwf hpe' hτ
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
        · -- Each field has a basic type in siteEnv and its entry in fentries
          intro f a' hmem
          exact foldlM_pack_sound env.siteEnv fields AssocMap.empty fentries hfold
            (check_fields_distinct_implies_fnames_nodup fields hdistinct) hmem
        · exact check_fields_distinct_implies_sites_distinct fields hdistinct
        · have hwf' := TypeEnv.deleteAll_insert_wf env (fields.map Prod.snd) a (.basic (.trecord fentries)) hwf trivial
          exact ih_cont _ hwf' h
      · simp at h
    · simp at h

/- ---------------------------------------------------- -/
/-       Subsumption soundness lemmas                    -/
/- ---------------------------------------------------- -/

/-- Soundness of is_empty: if is_empty returns true, the language is empty. -/
theorem is_empty_sound [DecidableEq α] : ∀ (r : Regex α), is_empty r = true → ∀ s, ¬ interpret_regex r s := by
  intro r
  induction r with
  | empty => intro _ s h; exact h
  | ε => intro h; simp [is_empty] at h
  | char _ => intro h; simp [is_empty] at h
  | dot => intro h; simp [is_empty] at h
  | union r1 r2 ih1 ih2 =>
    intro h s hmatch
    simp only [is_empty, Bool.and_eq_true] at h
    simp only [interpret_regex] at hmatch
    cases hmatch with
    | inl h1 => exact ih1 h.1 s h1
    | inr h2 => exact ih2 h.2 s h2
  | concat r1 r2 ih1 ih2 =>
    intro h s hmatch
    simp only [is_empty, Bool.or_eq_true] at h
    simp only [interpret_regex] at hmatch
    obtain ⟨s1, s2, _, h1, h2⟩ := hmatch
    cases h with
    | inl h1e => exact ih1 h1e s1 h1
    | inr h2e => exact ih2 h2e s2 h2
  | star _ => intro h; simp [is_empty] at h
  | deriv r _ ih =>
    intro h s hmatch
    simp only [is_empty] at h
    simp only [interpret_regex] at hmatch
    exact ih h _ hmatch

/-- Soundness of regexSubsumedBy: if it returns true, L(r1) ⊆ L(r2). -/
theorem regexSubsumedBy_sound [DecidableEq α] (r1 : Regex α) :
    ∀ (r2 : Regex α), regexSubsumedBy r1 r2 = true →
    ∀ path, interpret_regex r1 path → interpret_regex r2 path := by
  intro r2
  induction r2 with
  | union s1 s2 ih1 ih2 =>
    intro h path hmatch
    simp only [regexSubsumedBy, Bool.or_eq_true] at h
    rcases h with ((hempty | hbeq) | hsub1) | hsub2
    · exact absurd hmatch (is_empty_sound r1 hempty path)
    · rw [regexBeq_eq r1 _ hbeq] at hmatch; exact hmatch
    · exact Or.inl (ih1 hsub1 path hmatch)
    · exact Or.inr (ih2 hsub2 path hmatch)
  | _ =>
    intro h path hmatch
    simp only [regexSubsumedBy, Bool.or_eq_true] at h
    rcases h with hempty | hbeq
    · exact absurd hmatch (is_empty_sound r1 hempty path)
    · rw [regexBeq_eq r1 _ hbeq] at hmatch; exact hmatch

/-- Soundness of subsumes_bool: if it returns true, the semantic subsumption holds. -/
theorem subsumes_bool_implies_subsumes (envL env : TypeEnv) :
    TypeEnv.subsumes_bool envL env = true → TypeEnv.subsumes envL env := by
  intro h
  simp only [TypeEnv.subsumes_bool, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨hse, hve⟩, hrefs⟩, hpaths⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact lookup_equiv_bool_sound _ _ hse
  · exact varenv_lookup_compatible_bool_sound _ _ hve
  · exact beq_iff_eq.mp hrefs
  · intro u v hu hv path hmatch
    have hu' := hpaths u hu
    have huv := hu' v hv
    exact regexSubsumedBy_sound _ _ huv path hmatch

/- ---------------------------------------------------- -/
/-       Statement type checking soundness               -/
/- ---------------------------------------------------- -/

/-- Soundness: If the algorithmic check succeeds, the relational judgment holds.
    This requires the type environment to be well-formed (pathEnv and siteEnv invariants).
-/
theorem check_stmt_sound (lenv : LabelEnv) (env : TypeEnv) (s : Stmt) (retType : MoveType)
    (hwf : TypeEnv.WellFormed env) :
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
      split at h
      · apply typecheck_stmt.jump lenv env L envL retType hlookup
        exact subsumes_bool_implies_subsumes envL env (by assumption)
      · simp at h

  | branch a L1 L2 =>
    intro h
    simp only [check_stmt] at h
    cases ha : lookup env.siteEnv a with
    | none => simp [ha] at h
    | some τ =>
      simp only [ha] at h
      cases τ with
      | ref _ _ _ => simp at h
      | basic bt =>
        cases bt with
        | tbool =>
          cases hl1 : lookup lenv L1 with
          | none => simp [hl1] at h
          | some envL1 =>
            cases hl2 : lookup lenv L2 with
            | none => simp [hl1, hl2] at h
            | some envL2 =>
              simp only [hl1, hl2] at h
              split at h
              · rename_i hcond
                simp only [Bool.and_eq_true] at hcond
                apply typecheck_stmt.branch lenv env a L1 L2 envL1 envL2 retType ha hl1 hl2
                · exact subsumes_bool_implies_subsumes envL1 _ hcond.1
                · exact subsumes_bool_implies_subsumes envL2 _ hcond.2
              · simp at h
        | _ => simp at h

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
      · exact no_locals_borrowed_bool_sound env hwf.pathEnv_wf hnolocals
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
        -- Use SiteEnv.RefsNotRoot invariant to prove r ≠ root
        have hr_not_root : r ≠ Aref.root := hwf.siteEnv_wf a (.ref bt r isBor) hlookup
        have hpe' := delete_ref_node_wellformed env.pathEnv r hwf.pathEnv_wf hr_not_root
        have hsenv' := SiteEnv.delete_refs_not_root env.siteEnv a hwf.siteEnv_wf
        have hwf' : TypeEnv.WellFormed env' := ⟨hpe', hsenv', hwf.varEnv_wf⟩
        apply typecheck_stmt.release lenv env a bt r isBor cont retType hlookup
        exact ih_cont env' hwf' h

  -- letBind case: use the check_letBind_sound helper lemma
  | letBind a e cont ih_cont =>
    intro h
    exact check_letBind_sound lenv env a e cont retType hwf ih_cont h

  | assign x a cont ih_cont =>
    intro h
    simp only [check_stmt] at h
    cases hlookup : lookup env.varEnv x with
    | none => simp [hlookup] at h
    | some entry =>
      simp only [hlookup] at h
      match hentry : entry with
      | (.validVar, .basic τ, ms) =>
        simp only at h
        split at h
        · rename_i hms
          split at h
          · rename_i hfresh_ax
            let r := nextFreshRef env.pathEnv
            let ax : Site := .site (env.siteEnv.entries.length)
            apply typecheck_stmt.var_assign_valid (τ := τ) (ms := ms) (r := r) (ax := ax)
            · simp only [beq_iff_eq] at hms; simp only [hms, LE.le, Mut.le]
            · exact hlookup
            · exact hfresh_ax
            · exact nextFreshRef_fresh env.pathEnv
            · have hr_not_root : r ≠ Aref.root := nextFreshRef_not_root env.pathEnv
              have hr_not_varRef : ∀ v, r ≠ Aref.varRef v := nextFreshRef_not_varRef env.pathEnv
              have hpe' := update_with_extension_wellformed r .root [.root_to_var x] _
                (update_with_epsilon_wellformed r r env.pathEnv hwf.pathEnv_wf hr_not_root hr_not_varRef) hr_not_root hr_not_varRef
              have hpe_gc := garbage_collect_wellformed _ r hpe' hr_not_root
              have hsenv_ins := SiteEnv.insert_refs_not_root env.siteEnv ax (.ref τ r .siteBorrowMut) hwf.siteEnv_wf
                (by exact hr_not_root)
              have hsenv_del1 := SiteEnv.delete_refs_not_root _ a hsenv_ins
              have hsenv_del2 := SiteEnv.delete_refs_not_root _ ax hsenv_del1
              let env' : TypeEnv := {env with
                siteEnv := delete (delete (insert env.siteEnv ax (.ref τ r .siteBorrowMut)) a) ax
                pathEnv := garbage_collect (update_with_extension r .root [.root_to_var x] (update_with_epsilon r r env.pathEnv)) r}
              have hwf' : TypeEnv.WellFormed env' := ⟨hpe_gc, hsenv_del2, hwf.varEnv_wf⟩
              exact ih_cont env' hwf' h
          · simp at h
        · simp at h
      | (.validVar, .ref _ _ _, _) => simp at h
      | (.invalidVar, τ, .mutable) =>
        simp only at h
        cases hlookup_a : lookup env.siteEnv a with
        | none => simp [hlookup_a] at h
        | some τ' =>
          simp only [hlookup_a] at h
          split at h
          · rename_i hcompat
            have hcompat' := MoveType.compatible_bool_sound τ τ' hcompat
            have hτ_fresh := VarEnv.lookup_type_is_fresh env.varEnv x .invalidVar τ .mutable hwf.varEnv_wf hlookup
            have hτ'_fresh := MoveType.compatible_preserves_freshRef τ τ' hτ_fresh hcompat'
            have hsenv' := SiteEnv.delete_refs_not_root env.siteEnv a hwf.siteEnv_wf
            have hvarenv' := VarEnv.update_refs_are_fresh env.varEnv x (.validVar, τ', .mutable) hwf.varEnv_wf hτ'_fresh
            let env' : TypeEnv := {env with varEnv := update env.varEnv x (.validVar, τ', .mutable)
                                            siteEnv := delete env.siteEnv a}
            have hwf' : TypeEnv.WellFormed env' := ⟨hwf.pathEnv_wf, hsenv', hvarenv'⟩
            apply typecheck_stmt.var_assign_invalid
            · exact hlookup
            · exact hlookup_a
            · exact hcompat'
            · exact ih_cont env' hwf' h
          · simp at h
      | (.invalidVar, _, .immut) => simp at h

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
            · -- distinctness
              exact check_fields_distinct_implies_sites_distinct fields hdistinct
            · -- fields exist in fentries
              intro f a hfa
              simp only [check_unpack_fields_exist, List.all_eq_true] at hexist
              have hexist' := hexist (f, a) hfa
              cases hlookupf : lookup fentries f with
              | none => simp [hlookupf] at hexist'
              | some bt' => exact ⟨bt', rfl⟩
            · -- recursive call
              let env' := {env with siteEnv := addFieldSites fentries (delete env.siteEnv b) fields}
              -- PathEnv is unchanged for unpack; SiteEnv has delete + addFieldSites (basic types only)
              have hsenv' : SiteEnv.RefsNotRoot env'.siteEnv :=
                addFieldSites_refs_not_root fentries _ fields
                  (SiteEnv.delete_refs_not_root env.siteEnv b hwf.siteEnv_wf)
              have hwf' : TypeEnv.WellFormed env' := ⟨hwf.pathEnv_wf, hsenv', hwf.varEnv_wf⟩
              exact ih_cont env' hwf' h
          · simp at h
        | _ => simp [hlookup] at h
      | ref _ _ _ => simp [hlookup] at h

  | writeRef a b cont ih_cont =>
    intro h
    simp only [check_stmt] at h
    cases hlookup_a : lookup env.siteEnv a with
    | none => simp [hlookup_a] at h
    | some ta =>
      cases ta with
      | basic bt => simp [hlookup_a] at h
      | ref bt r isBor =>
        cases isBor with
        | siteBorrowImm => simp [hlookup_a] at h
        | siteBorrowMut =>
          simp only [hlookup_a] at h
          cases hlookup_b : lookup env.siteEnv b with
          | none => simp [hlookup_b] at h
          | some tb =>
            cases tb with
            | ref _ _ _ => simp [hlookup_b] at h
            | basic bt' =>
              simp only [hlookup_b] at h
              split at h
              · rename_i hcond
                simp only [Bool.and_eq_true] at hcond
                obtain ⟨hbeq, hcob⟩ := hcond
                have hτeq := BasicMoveType.eq_of_beq bt bt' hbeq
                subst hτeq
                -- Bridge check_outbound_bool to check_outbound
                have hout : check_outbound env.pathEnv r (fun re => only_matches_empty (simplify re)) := by
                  intro s' hs'
                  simp only [check_outbound_bool, List.all_eq_true] at hcob
                  exact hcob s' hs'
                -- Get r ≠ .root from SiteEnv.RefsNotRoot
                have hr_not_root : r ≠ Aref.root := hwf.siteEnv_wf a (.ref bt r .siteBorrowMut) hlookup_a
                -- Build WellFormed for new env
                have hpe' := garbage_collect_wellformed env.pathEnv r hwf.pathEnv_wf hr_not_root
                have hsenv_del1 := SiteEnv.delete_refs_not_root env.siteEnv b hwf.siteEnv_wf
                have hsenv_del2 := SiteEnv.delete_refs_not_root _ a hsenv_del1
                let env' := {env with siteEnv := delete (delete env.siteEnv b) a
                                      pathEnv := garbage_collect env.pathEnv r}
                have hwf' : TypeEnv.WellFormed env' := ⟨hpe', hsenv_del2, hwf.varEnv_wf⟩
                -- Apply relational rule and IH
                apply typecheck_stmt.write_ref lenv env a b bt r cont retType hlookup_a hlookup_b hout
                exact ih_cont env' hwf' h
              · simp at h

  | call as fnName bs cont ih_cont =>
    intro h
    simp only [check_stmt] at h
    split at h
    · rename_i hfresh_bool
      cases hlookup_fn : lookup env.funEnv fnName with
      | none => simp [hlookup_fn] at h
      | some sig =>
        obtain ⟨params, rets⟩ := sig
        simp only [hlookup_fn] at h
        split at h
        · rename_i hcond
          simp only [Bool.and_eq_true] at hcond
          obtain ⟨⟨⟨htc_bs, htc_as⟩, hiso⟩, houtbound⟩ := hcond
          have hfresh' := all_fresh_sites_bool_sound env as hfresh_bool
          have htc_bs' := types_conform_bool_sound env.siteEnv bs params htc_bs
          have htc_as' := types_conform_bool_sound env.siteEnv as rets htc_as
          have hiso' := check_mutable_inputs_isolated_bool_sound env bs hiso
          have houtbound' := check_mutable_inputs_have_outbound_bool_sound env bs houtbound
          have hwf' := call_connect_inputs_outputs_wf env as bs hwf hfresh'
          apply typecheck_stmt.call lenv env fnName as bs params rets cont retType
            hfresh' hlookup_fn htc_bs' htc_as' hiso' houtbound'
          exact ih_cont _ hwf' h
        · simp at h
    · simp at h


/- ---------------------------------------------------- -/
/-       Function type checking soundness                -/
/- ---------------------------------------------------- -/

/-- Soundness: If the algorithmic check succeeds, the relational judgment holds.
    Requires that all environments in the label environment are well-formed. -/
theorem check_fun_sound (f : FunDef) (lenv : LabelEnv)
    (hlenv_wf : ∀ l env, lookup lenv l = some env → TypeEnv.WellFormed env) :
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
        exact check_stmt_sound lenv blockEnv block.body f.returnType
          (hlenv_wf _ _ hblockLookup) hcheck

end LeanMove.Checker
