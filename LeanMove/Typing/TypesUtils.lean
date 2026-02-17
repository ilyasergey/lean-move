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
/-       freshRefInEnv / nextFreshRefInEnv lemmas        -/
/- ---------------------------------------------------- -/

-- Helper: List.lookup gives membership in the list
private lemma list_lookup_pair_mem [BEq α] [LawfulBEq α]
    {l : List (α × β)} {k : α} {v : β}
    (h : l.lookup k = some v) : (k, v) ∈ l := by
  induction l with
  | nil => simp [List.lookup] at h
  | cons hd tl ih =>
    simp only [List.lookup] at h
    split at h
    · rename_i heq
      have hk : k = hd.1 := beq_iff_eq.mp heq
      have hv : hd.2 = v := by injection h
      subst hk; subst hv; exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (ih h)

-- freshRefInEnvBool implies freshRefBool on pathEnv
lemma freshRefInEnvBool_implies_freshRefBool (r : Aref) (env : TypeEnv)
    (h : freshRefInEnvBool r env = true) : freshRefBool r env.pathEnv = true := by
  simp only [freshRefInEnvBool, Bool.and_eq_true] at h
  exact h.1.1

-- freshRefInEnv implies freshRef on pathEnv
lemma freshRefInEnv_implies_freshRef (r : Aref) (env : TypeEnv)
    (h : freshRefInEnv r env) : freshRef r env.pathEnv := h.1

-- freshRefInEnv ↔ freshRefInEnvBool
theorem freshRefInEnv_iff_freshRefInEnvBool (r : Aref) (env : TypeEnv) :
    freshRefInEnv r env ↔ freshRefInEnvBool r env = true := by
  constructor
  · intro ⟨hpath, hvar, hsite⟩
    simp only [freshRefInEnvBool, Bool.and_eq_true, Bool.not_eq_true',
               List.contains_eq_any_beq]
    refine ⟨⟨(freshRef_iff_freshRefBool r env.pathEnv).mp hpath, ?_⟩, ?_⟩
    · rw [List.any_eq_false]; intro x hx
      simp only [beq_iff_eq]; exact fun heq => hvar (heq ▸ hx)
    · rw [List.any_eq_false]; intro x hx
      simp only [beq_iff_eq]; exact fun heq => hsite (heq ▸ hx)
  · intro h
    simp only [freshRefInEnvBool, Bool.and_eq_true, Bool.not_eq_true',
               List.contains_eq_any_beq] at h
    obtain ⟨⟨hpath, hvar⟩, hsite⟩ := h
    refine ⟨(freshRef_iff_freshRefBool r env.pathEnv).mpr hpath, ?_, ?_⟩
    · intro hmem
      rw [List.any_eq_false] at hvar
      exact absurd (beq_self_eq_true r) (hvar r hmem)
    · intro hmem
      rw [List.any_eq_false] at hsite
      exact absurd (beq_self_eq_true r) (hsite r hmem)

-- nextFreshRefInEnv is fresh in the entire TypeEnv (Bool version)
theorem nextFreshRefInEnv_fresh (env : TypeEnv) :
    freshRefInEnvBool (nextFreshRefInEnv env) env = true := by
  unfold nextFreshRefInEnv freshRefInEnvBool freshRefBool
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_any_beq]
  -- Abbreviation for the full refs list
  let AR := env.pathEnv.refs ++ collectVarEnvRefs env.varEnv ++ collectSiteEnvRefs env.siteEnv
  -- Helper: any ref in AR can't equal the fresh refid
  have hnotIn : ∀ r, r ∈ AR → ∀ (n : Nat),
      n = AR.foldl (fun acc r => max acc (getRefId r)) 0 + 1 → r ≠ Aref.refid n := by
    intro r hr n hn heq
    have hmax := foldl_max_ge_elem AR 0 r hr
    subst heq; subst hn; simp only [getRefId] at hmax; omega
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [List.any_eq_false]; intro r hr; simp only [beq_iff_eq]
    exact (hnotIn r (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hr)))) _ rfl).symm
  · rw [List.any_eq_false]; intro r hr; simp only [beq_iff_eq]
    exact (hnotIn r (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hr)))) _ rfl).symm
  · rw [List.any_eq_false]; intro r hr; simp only [beq_iff_eq]
    exact (hnotIn r (List.mem_append.mpr (Or.inr hr)) _ rfl).symm

-- nextFreshRefInEnv is fresh (Prop version)
theorem nextFreshRefInEnv_fresh_prop (env : TypeEnv) :
    freshRefInEnv (nextFreshRefInEnv env) env :=
  (freshRefInEnv_iff_freshRefInEnvBool _ env).mpr (nextFreshRefInEnv_fresh env)

-- nextFreshRefInEnv is never root
lemma nextFreshRefInEnv_not_root (env : TypeEnv) : nextFreshRefInEnv env ≠ Aref.root := by
  simp only [nextFreshRefInEnv]; intro h; cases h

-- nextFreshRefInEnv is never varRef
lemma nextFreshRefInEnv_not_varRef (env : TypeEnv) (x : Var) :
    nextFreshRefInEnv env ≠ Aref.varRef x := by
  simp only [nextFreshRefInEnv]; intro h; cases h

-- nextFreshRefInEnv is not in pathEnv.refs
lemma nextFreshRefInEnv_not_in_pathEnv (env : TypeEnv) :
    nextFreshRefInEnv env ∉ env.pathEnv.refs :=
  (nextFreshRefInEnv_fresh_prop env).1

-- Any .refid n with n ≥ getRefId(nextFreshRefInEnv env) is fresh in the env
lemma refid_ge_start_fresh (env : TypeEnv) (n : Nat)
    (hge : n ≥ getRefId (nextFreshRefInEnv env)) :
    freshRefInEnvBool (.refid n) env = true := by
  unfold nextFreshRefInEnv at hge
  simp only [getRefId] at hge
  unfold freshRefInEnvBool freshRefBool
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_any_beq]
  have hnotIn : ∀ r ∈ env.pathEnv.refs ++ collectVarEnvRefs env.varEnv ++
      collectSiteEnvRefs env.siteEnv, r ≠ .refid n := by
    intro r hr heq
    have hmax := foldl_max_ge_elem _ 0 r hr
    subst heq; simp only [getRefId] at hmax; omega
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [List.any_eq_false]; intro r hr; simp only [beq_iff_eq]
    exact (hnotIn r (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hr))))).symm
  · rw [List.any_eq_false]; intro r hr; simp only [beq_iff_eq]
    exact (hnotIn r (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hr))))).symm
  · rw [List.any_eq_false]; intro r hr; simp only [beq_iff_eq]
    exact (hnotIn r (List.mem_append.mpr (Or.inr hr))).symm

-- Key lemma: freshRefInEnvBool means the ref doesn't appear in any VarEnv entry
lemma freshRefInEnvBool_ne_varEnv_ref (t : Aref) (env : TypeEnv) (x : Var)
    (isv : IsValid) (τ : BasicMoveType) (s : Aref) (isBor : BorrowingKind) (ms : Mut)
    (hfresh : freshRefInEnvBool t env = true)
    (hlookup : lookup env.varEnv x = some (isv, .ref τ s isBor, ms)) :
    t ≠ s := by
  intro heq; subst heq
  have ⟨_, hvar, _⟩ := (freshRefInEnv_iff_freshRefInEnvBool t env).mpr hfresh
  apply hvar
  simp only [collectVarEnvRefs, List.mem_filterMap]
  exact ⟨(x, (isv, .ref τ t isBor, ms)), list_lookup_pair_mem hlookup, rfl⟩

-- Key lemma: freshRefInEnvBool means the ref doesn't appear in any SiteEnv entry
lemma freshRefInEnvBool_ne_siteEnv_ref (t : Aref) (env : TypeEnv) (s : Site)
    (τ : BasicMoveType) (s_ref : Aref) (isBor : BorrowingKind)
    (hfresh : freshRefInEnvBool t env = true)
    (hlookup : lookup env.siteEnv s = some (.ref τ s_ref isBor)) :
    t ≠ s_ref := by
  intro heq; subst heq
  have ⟨_, _, hsite⟩ := (freshRefInEnv_iff_freshRefInEnvBool t env).mpr hfresh
  apply hsite
  simp only [collectSiteEnvRefs, List.mem_filterMap]
  exact ⟨(s, .ref τ t isBor), list_lookup_pair_mem hlookup, rfl⟩

-- Prop versions of the above
lemma freshRefInEnv_ne_varEnv_ref (t : Aref) (env : TypeEnv) (x : Var)
    (isv : IsValid) (τ : BasicMoveType) (s : Aref) (isBor : BorrowingKind) (ms : Mut)
    (hfresh : freshRefInEnv t env)
    (hlookup : lookup env.varEnv x = some (isv, .ref τ s isBor, ms)) :
    t ≠ s := by
  exact freshRefInEnvBool_ne_varEnv_ref t env x isv τ s isBor ms
    ((freshRefInEnv_iff_freshRefInEnvBool t env).mp hfresh) hlookup

lemma freshRefInEnv_ne_siteEnv_ref (t : Aref) (env : TypeEnv) (s : Site)
    (τ : BasicMoveType) (s_ref : Aref) (isBor : BorrowingKind)
    (hfresh : freshRefInEnv t env)
    (hlookup : lookup env.siteEnv s = some (.ref τ s_ref isBor)) :
    t ≠ s_ref := by
  exact freshRefInEnvBool_ne_siteEnv_ref t env s τ s_ref isBor
    ((freshRefInEnv_iff_freshRefInEnvBool t env).mp hfresh) hlookup

/- ---------------------------------------------------- -/
/-       PathEnv lemmas                                  -/
/- ---------------------------------------------------- -/

lemma delete_ref_node_refs (pe : PathEnv) (r : Aref) :
    (delete_ref_node pe r).refs = List.filter (fun r' => r' ≠ r) pe.refs := by
  rfl

lemma delete_ref_node_paths_involving_r (pe : PathEnv) (r : Aref) (u v : Aref)
    (huv : u ≠ v) (h : u = r ∨ v = r) : (delete_ref_node pe r).paths (u, v) = Regex.empty := by
  simp only [delete_ref_node]
  rcases h with rfl | rfl
  · rw [if_neg (fun ⟨_, h⟩ => huv h.symm), if_pos (Or.inl rfl)]
  · rw [if_neg (fun ⟨h, _⟩ => huv h), if_pos (Or.inr rfl)]

lemma delete_ref_node_paths_self (pe : PathEnv) (r : Aref) :
    (delete_ref_node pe r).paths (r, r) = Regex.ε := by
  simp [delete_ref_node]

lemma delete_ref_node_paths_not_involving_r (pe : PathEnv) (r : Aref) (u v : Aref)
    (hu : u ≠ r) (hv : v ≠ r) : (delete_ref_node pe r).paths (u, v) = pe.paths (u, v) := by
  simp only [delete_ref_node]
  rw [if_neg (fun ⟨h, _⟩ => hu h), if_neg (not_or.mpr ⟨hu, hv⟩)]

/-- A path from root is a "borrow path" for variable x if it accepts [.root_to_var x].
    This happens when the path is char (.root_to_var x) or concat ε (char (.root_to_var x)). -/
def isBorrowPath (x : Var) (regex : Regex PathElement) : Prop :=
  match regex with
  | .char c => c = .root_to_var x
  | .concat .ε (.char c) => c = .root_to_var x
  | _ => False

/-- A path environment is well-formed if:
    1. Refs not in the refs list have empty paths from root
    2. The root reference is always in the refs list
    3. Untracked refs have empty paths to root -/
structure PathEnv.WellFormed (pe : PathEnv) : Prop where
  refs_complete : ∀ r, r ∉ pe.refs → pe.paths (.root, r) = .empty
  root_in_refs : Aref.root ∈ pe.refs
  from_untracked_to_root_empty : ∀ u, u ∉ pe.refs → u ≠ Aref.root → pe.paths (u, .root) = .empty
  self_loop_accepts_nil : ∀ u, interpret_regex (pe.paths (u, u)) []

lemma PathEnv.init_wellformed : PathEnv.WellFormed PathEnv.init := by
  constructor
  · intro r hr
    simp only [PathEnv.init, List.mem_singleton] at hr
    simp only [PathEnv.init]
    by_cases heq : Aref.root = r
    · exact absurd heq.symm hr
    · simp [heq]
  · -- root_in_refs: .root ∈ [.root]
    simp only [PathEnv.init, List.mem_singleton]
  · -- from_untracked_to_root_empty: u ∉ [.root] → u ≠ .root → paths(u, .root) = .empty
    intro u _hu huroot
    simp only [PathEnv.init]
    simp [huroot]
  · -- self_loop_accepts_nil
    intro u; simp only [PathEnv.init, ↓reduceIte, interpret_regex]

/-- delete_ref_node preserves WellFormed when r ≠ root.
    In practice, we never delete root - it's only used for borrow references. -/
lemma delete_ref_node_wellformed (pe : PathEnv) (r : Aref) (hwf : PathEnv.WellFormed pe)
    (hr_not_root : r ≠ Aref.root) :
    PathEnv.WellFormed (delete_ref_node pe r) := by
  constructor
  · -- refs_complete preservation
    intro r' hr'
    by_cases hr : Aref.root = r
    · -- root = r: contradicts hr_not_root
      exact absurd hr.symm hr_not_root
    · by_cases hr'' : r' = r
      · -- r' = r
        have hne : Aref.root ≠ r' := fun h => hr (h.trans hr'')
        have := delete_ref_node_paths_involving_r pe r .root r' hne (Or.inr hr'')
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
  · -- root_in_refs: .root survives filter since r ≠ .root
    simp only [delete_ref_node_refs, List.mem_filter, decide_eq_true_eq]
    exact ⟨hwf.root_in_refs, fun h => hr_not_root h.symm⟩
  · -- from_untracked_to_root_empty
    intro u hu huroot
    simp only [delete_ref_node_refs, List.mem_filter, decide_eq_true_eq, not_and] at hu
    by_cases hur : u = r
    · -- u = r: paths from r are .empty after delete
      rw [hur]
      exact delete_ref_node_paths_involving_r pe r r .root hr_not_root (Or.inl rfl)
    · -- u ≠ r: u ∉ pe.refs
      have hu_not_in : u ∉ pe.refs := by
        intro hcontra
        exact hur (Decidable.not_not.mp (hu hcontra))
      -- root ≠ r by hr_not_root, u ≠ r by hur: paths unchanged
      have hroot_ne_r : Aref.root ≠ r := fun h => hr_not_root h.symm
      rw [delete_ref_node_paths_not_involving_r pe r u .root hur (Ne.symm hr_not_root)]
      exact hwf.from_untracked_to_root_empty u hu_not_in huroot
  · -- self_loop_accepts_nil
    intro u
    by_cases hur : u = r
    · subst hur; simp only [delete_ref_node, and_self, ↓reduceIte, interpret_regex]
    · simp only [delete_ref_node]
      rw [if_neg (fun ⟨h, _⟩ => hur h), if_neg (not_or.mpr ⟨hur, hur⟩)]
      exact hwf.self_loop_accepts_nil u

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

lemma nextFreshRefInEnv_isFreshRef (env : TypeEnv) :
    Aref.isFreshRef (nextFreshRefInEnv env) := by
  simp only [nextFreshRefInEnv]; exact ⟨_, rfl⟩

/-- If r1 is not root and Aref-compatible with r2, then r2 is also not root. -/
lemma Aref.Compatible_preserves_not_root (r1 r2 : Aref)
    (hnotroot : r1 ≠ .root) (hcompat : Aref.Compatible r1 r2) : r2 ≠ .root := by
  intro heq; subst heq
  cases r1 with
  | root => exact hnotroot rfl
  | refid _ => exact absurd hcompat (by simp [Aref.Compatible])
  | varRef _ => exact absurd hcompat (by simp [Aref.Compatible])

/-- Helper function: predicate that a MoveType's ref is a fresh ref (refid) -/
def moveTypeIsFreshRef (τ : MoveType) : Prop :=
  match τ with | .ref _ r _ => Aref.isFreshRef r | .basic _ => True

/-- Helper: predicate that a MoveType's ref is not root -/
def moveTypeRefNotRoot (τ : MoveType) : Prop :=
  match τ with | .ref _ r _ => r ≠ .root | .basic _ => True

/-- If τ's ref is not root and τ' is compatible with τ, then τ' ref is also not root. -/
lemma MoveType.compatible_preserves_not_root (τ τ' : MoveType)
    (hnotroot : moveTypeRefNotRoot τ) (hcompat : MoveType.compatible τ τ') : moveTypeRefNotRoot τ' := by
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
      simp only [moveTypeRefNotRoot] at hnotroot ⊢
      exact Aref.Compatible_preserves_not_root r r' hnotroot hr

/-- Fresh ref implies not root (bridge lemma). -/
lemma moveTypeIsFreshRef_implies_notRoot (τ : MoveType)
    (hfresh : moveTypeIsFreshRef τ) : moveTypeRefNotRoot τ := by
  cases τ with
  | basic _ => trivial
  | ref bt r bk =>
    simp only [moveTypeIsFreshRef] at hfresh
    simp only [moveTypeRefNotRoot]
    exact Aref.isFreshRef_not_root r hfresh

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
    3. All references in varEnv are not root -/
structure TypeEnv.WellFormed (env : TypeEnv) : Prop where
  pathEnv_wf : PathEnv.WellFormed env.pathEnv
  siteEnv_wf : SiteEnv.RefsNotRoot env.siteEnv
  varEnv_wf : VarEnv.RefsNotRoot env.varEnv

/-- Helper: get RefsNotRoot from WellFormed (now trivial alias) -/
lemma TypeEnv.WellFormed.varEnv_refs_not_root (hwf : TypeEnv.WellFormed env) :
    VarEnv.RefsNotRoot env.varEnv :=
  hwf.varEnv_wf

/-- init_fun_pathEnv is well-formed for any function definition. -/
lemma PathEnv.init_fun_wellformed (f : FunDef) :
    PathEnv.WellFormed (init_fun_pathEnv f) := by
  constructor
  · -- refs_complete: r ∉ refs → paths(.root, r) = .empty
    intro r hr
    unfold init_fun_pathEnv at hr ⊢
    dsimp only at hr
    by_cases heq : Aref.root = r
    · subst heq; simp at hr
    · cases r with
      | root => exact absurd rfl heq
      | refid n => simp [heq]
      | varRef x =>
        have hni : Aref.varRef x ∉ _ := fun h => hr (List.mem_cons_of_mem _ h)
        simp [heq]
  · -- root_in_refs
    unfold init_fun_pathEnv
    exact List.Mem.head _
  · -- from_untracked_to_root_empty
    intro u _hu huroot
    unfold init_fun_pathEnv
    cases u with
    | root => exact absurd rfl huroot
    | refid _ => simp [huroot]
    | varRef _ => simp [huroot]
  · -- self_loop_accepts_nil
    intro u; simp only [init_fun_pathEnv, ↓reduceIte, interpret_regex]

/-- Initial TypeEnv with empty siteEnv and PathEnv.init is well-formed
    when the provided varEnv satisfies RefsNotRoot -/
lemma TypeEnv.init_wellformed (varEnv : VarEnv) (funEnv : FunEnv)
    (hvarEnv : VarEnv.RefsNotRoot varEnv) :
    TypeEnv.WellFormed { siteEnv := AssocMap.empty, varEnv := varEnv, pathEnv := PathEnv.init, funEnv := funEnv } := by
  constructor
  · exact PathEnv.init_wellformed
  · exact SiteEnv.empty_refs_not_root
  · exact hvarEnv

/-- Initial TypeEnv with empty siteEnv and init_fun_pathEnv is well-formed
    when the provided varEnv satisfies RefsNotRoot. -/
lemma TypeEnv.init_fun_wellformed (f : FunDef) (varEnv : VarEnv) (funEnv : FunEnv)
    (hvarEnv : VarEnv.RefsNotRoot varEnv) :
    TypeEnv.WellFormed { siteEnv := AssocMap.empty, varEnv := varEnv, pathEnv := init_fun_pathEnv f, funEnv := funEnv } := by
  constructor
  · exact PathEnv.init_fun_wellformed f
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

/-- Updating varEnv preserves TypeEnv.WellFormed if the new entry has a not-root ref -/
lemma TypeEnv.update_varEnv_wf (env : TypeEnv) (x : Var) (v : IsValid × MoveType × Mut)
    (hwf : TypeEnv.WellFormed env)
    (hv : moveTypeRefNotRoot v.2.1) :
    TypeEnv.WellFormed {env with varEnv := update env.varEnv x v} := by
  constructor
  · exact hwf.pathEnv_wf
  · exact hwf.siteEnv_wf
  · exact VarEnv.update_refs_not_root env.varEnv x v hwf.varEnv_wf hv

/-- Combined update: insert site and update varEnv preserves WellFormed -/
lemma TypeEnv.insert_update_wf (env : TypeEnv) (s : Site) (τ : MoveType) (x : Var) (v : IsValid × MoveType × Mut)
    (hwf : TypeEnv.WellFormed env)
    (hτ : match τ with | .ref _ r _ => r ≠ Aref.root | .basic _ => True)
    (hv : moveTypeRefNotRoot v.2.1) :
    TypeEnv.WellFormed {env with siteEnv := insert env.siteEnv s τ, varEnv := update env.varEnv x v} := by
  constructor
  · exact hwf.pathEnv_wf
  · exact SiteEnv.insert_refs_not_root env.siteEnv s τ hwf.siteEnv_wf hτ
  · exact VarEnv.update_refs_not_root env.varEnv x v hwf.varEnv_wf hv

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

/-- If a regex matches nothing, its derivative by any character also matches nothing. -/
lemma no_match_deriv [DecidableEq α] {re : Regex α} {a : α}
    (h : ∀ q, ¬interpret_regex re q) :
    ∀ q, ¬interpret_regex (Regex.deriv re a) q := by
  intro q hcontra
  simp only [interpret_regex] at hcontra
  exact h (a :: q) hcontra

/-- If a regex matches nothing, `der re p` also matches nothing. -/
lemma no_match_der [DecidableEq α] {re : Regex α} (p : List α)
    (h : ∀ q, ¬interpret_regex re q) :
    ∀ q, ¬interpret_regex (der re p) q := by
  induction p generalizing re with
  | nil => exact h
  | cons a rest ih =>
    simp only [der, List.foldl]
    apply ih
    exact no_match_deriv h

/-- If a regex matches nothing, `extend re p` also matches nothing. -/
lemma no_match_extend [DecidableEq α] {re : Regex α} (p : List α)
    (h : ∀ q, ¬interpret_regex re q) :
    ∀ q, ¬interpret_regex (extend re p) q := by
  induction p generalizing re with
  | nil => exact h
  | cons a rest ih =>
    simp only [extend, List.foldl]
    apply ih
    intro q hcontra
    simp only [interpret_regex] at hcontra
    obtain ⟨q1, _, _, hq1, _⟩ := hcontra
    exact h q1 hq1

/-- If both regexes match nothing, their union also matches nothing. -/
lemma no_match_union [DecidableEq α] {r1 r2 : Regex α}
    (h1 : ∀ q, ¬interpret_regex r1 q) (h2 : ∀ q, ¬interpret_regex r2 q) :
    ∀ q, ¬interpret_regex (Regex.union r1 r2) q := by
  intro q hcontra
  simp only [interpret_regex] at hcontra
  cases hcontra with
  | inl h => exact h1 q h
  | inr h => exact h2 q h

/-- update_with_extension preserves WellFormed when z ≠ root and z is not a varRef.
    In practice, z is always a fresh ref from nextFreshRef (never .root or varRef). -/
lemma update_with_extension_wellformed (z x : Aref) (path : List PathElement) (pe : PathEnv)
    (hwf : PathEnv.WellFormed pe) (hz_not_root : z ≠ Aref.root)
    (_ : ∀ v, z ≠ Aref.varRef v) :
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
  · -- root_in_refs: .root stays in refs (z ≠ .root so root was already there)
    simp only [update_with_extension]
    by_cases hzin : z ∈ pe.refs
    · simp only [hzin, not_true_eq_false, ↓reduceIte]
      exact hwf.root_in_refs
    · simp only [hzin, not_false_eq_true, ↓reduceIte, List.mem_cons]
      exact Or.inr hwf.root_in_refs
  · -- from_untracked_to_root_empty
    intro u hu huroot
    simp only [update_with_extension] at hu ⊢
    -- u ∉ refs' implies u ≠ z and u ∉ pe.refs
    have hu_ne_z : u ≠ z := by
      intro heq
      apply hu
      rw [heq]
      by_cases hzin : z ∈ pe.refs
      · simp only [hzin, not_true_eq_false, ↓reduceIte]
      · simp only [hzin, not_false_eq_true, ↓reduceIte, List.mem_cons]; exact Or.inl trivial
    have hu_notin : u ∉ pe.refs := by
      intro hcontra
      apply hu
      by_cases hzin : z ∈ pe.refs
      · simp only [hzin, not_true_eq_false, ↓reduceIte]; exact hcontra
      · simp only [hzin, not_false_eq_true, ↓reduceIte, List.mem_cons]; exact Or.inr hcontra
    -- v = .root ≠ z, so neither u=z∧v=z nor v=z applies; u ≠ z so u=z doesn't apply
    have hnotboth : ¬(u = z ∧ Aref.root = z) := fun ⟨_, h⟩ => hz_not_root h.symm
    have hroot_ne_z : ¬(Aref.root = z) := fun h => hz_not_root h.symm
    rw [if_neg hnotboth, if_neg hroot_ne_z, if_neg hu_ne_z]
    exact hwf.from_untracked_to_root_empty u hu_notin huroot
  · -- self_loop_accepts_nil
    intro u
    by_cases huz : u = z
    · rw [huz]; simp only [update_with_extension, and_self, ↓reduceIte, interpret_regex]
    · simp only [update_with_extension]
      rw [if_neg (fun ⟨h, _⟩ => huz h), if_neg huz, if_neg huz]
      exact hwf.self_loop_accepts_nil u

/-- update_with_epsilon preserves WellFormed -/
lemma update_with_epsilon_wellformed (s t : Aref) (pe : PathEnv) (hwf : PathEnv.WellFormed pe)
    (hs_not_root : s ≠ Aref.root) (hs_not_varRef : ∀ v, s ≠ Aref.varRef v) :
    PathEnv.WellFormed (update_with_epsilon s t pe) := by
  unfold update_with_epsilon
  exact update_with_extension_wellformed s t [] pe hwf hs_not_root hs_not_varRef

/-- extend_with_star preserves WellFormed when target ≠ .root -/
lemma extend_with_star_wellformed (target source : Aref) (pe : PathEnv)
    (hwf : PathEnv.WellFormed pe) (htarget_ne_root : target ≠ Aref.root) :
    PathEnv.WellFormed (extend_with_star target source pe) := by
  have hnotz : Aref.root ≠ target := fun h => htarget_ne_root h.symm
  -- target is always in the extended refs
  have htarget_mem : target ∈ (extend_with_star target source pe).refs := by
    simp only [extend_with_star]
    by_cases htin : target ∈ pe.refs
    · simp only [htin, not_true_eq_false, ↓reduceIte]
    · simp only [htin, not_false_eq_true, ↓reduceIte, List.mem_cons, true_or]
  -- For any u ∉ extended refs: u ≠ target and u ∉ pe.refs
  have hmem_ext : ∀ u, u ∉ (extend_with_star target source pe).refs →
      u ≠ target ∧ u ∉ pe.refs := by
    intro u hu
    refine ⟨fun heq => hu (heq ▸ htarget_mem), fun hc => hu ?_⟩
    simp only [extend_with_star]
    by_cases htin : target ∈ pe.refs
    · simp only [htin, not_true_eq_false, ↓reduceIte]; exact hc
    · simp only [htin, not_false_eq_true, ↓reduceIte, List.mem_cons]; exact Or.inr hc
  constructor
  · -- refs_complete
    intro r hr
    obtain ⟨hr_ne, hr_notin⟩ := hmem_ext r hr
    simp only [extend_with_star]
    rw [if_neg (fun ⟨h, _⟩ => hnotz h), if_neg hr_ne, if_neg hnotz]
    exact hwf.refs_complete r hr_notin
  · -- root_in_refs
    simp only [extend_with_star]
    by_cases htin : target ∈ pe.refs
    · simp only [htin, not_true_eq_false, ↓reduceIte]; exact hwf.root_in_refs
    · simp only [htin, not_false_eq_true, ↓reduceIte, List.mem_cons]; exact Or.inr hwf.root_in_refs
  · -- from_untracked_to_root_empty
    intro u hu huroot
    obtain ⟨hu_ne, hu_notin⟩ := hmem_ext u hu
    simp only [extend_with_star]
    rw [if_neg (fun ⟨_, h⟩ => hnotz h), if_neg hnotz, if_neg hu_ne]
    exact hwf.from_untracked_to_root_empty u hu_notin huroot
  · -- self_loop_accepts_nil
    intro u
    by_cases hut : u = target
    · rw [hut]; simp only [extend_with_star, and_self, ↓reduceIte, interpret_regex]
    · simp only [extend_with_star]
      rw [if_neg (fun ⟨h, _⟩ => hut h), if_neg hut, if_neg hut]
      exact hwf.self_loop_accepts_nil u

/-- List.foldl preserves a property when each step preserves it for list elements -/
private lemma foldl_preserves_wf_mem {α β : Type} {P : α → Prop} (f : α → β → α) (init : α)
    (l : List β) (hinit : P init)
    (hstep : ∀ acc b, b ∈ l → P acc → P (f acc b)) : P (l.foldl f init) := by
  induction l generalizing init with
  | nil => exact hinit
  | cons x xs ih =>
    simp only [List.foldl_cons]
    apply ih
    · exact hstep init x (List.mem_cons.mpr (Or.inl rfl)) hinit
    · intro acc b hb hacc
      exact hstep acc b (List.mem_cons.mpr (Or.inr hb)) hacc

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
    · -- v = r: path from root to r is empty (first ∧-condition fails since .root ≠ r)
      subst hvr
      simp only [and_true, show ¬(Aref.root = v) from (fun h => hr_not_root h.symm),
        ↓reduceIte, or_true]
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
      simp only [show ¬(Aref.root = r ∧ v = r) from (fun ⟨h, _⟩ => hr_not_root h.symm),
        ↓reduceIte, hcond]
      exact horiginal
  · -- root_in_refs: .root survives filter since r ≠ .root
    simp only [garbage_collect, List.mem_filter, decide_eq_true_eq]
    exact ⟨hwf.root_in_refs, fun h => hr_not_root h.symm⟩
  · -- from_untracked_to_root_empty
    intro u hu huroot
    simp only [garbage_collect] at hu ⊢
    simp only [List.mem_filter, decide_eq_true_eq, not_and] at hu
    by_cases hur : u = r
    · -- u = r: ∧-condition (r = r ∧ .root = r) fails since .root ≠ r, but ∨-condition holds
      subst hur
      simp only [show ¬(Aref.root = u) from (fun h => hr_not_root h.symm),
        and_false, ↓reduceIte, true_or]
    · -- u ≠ r: both conditions false, paths unchanged
      have hu_notin : u ∉ pe.refs := by
        intro hcontra; exact hur (Decidable.not_not.mp (hu hcontra))
      have hcond : ¬(u = r ∨ Aref.root = r) := by
        intro h; cases h with
        | inl h => exact hur h
        | inr h => exact hr_not_root h.symm
      simp only [show ¬(u = r ∧ Aref.root = r) from (fun ⟨h, _⟩ => hur h),
        ↓reduceIte, hcond]
      exact hwf.from_untracked_to_root_empty u hu_notin huroot
  · -- self_loop_accepts_nil
    intro u
    by_cases hur : u = r
    · rw [hur]; simp only [garbage_collect, and_self, ↓reduceIte, interpret_regex]
    · simp only [garbage_collect]
      rw [if_neg (fun ⟨h, _⟩ => hur h), if_neg (not_or.mpr ⟨hur, hur⟩)]
      exact hwf.self_loop_accepts_nil u

/-- consume_ref_transfer preserves WellFormed.
    Transfers edges from r to r' and removes r. -/
lemma consume_ref_transfer_wellformed (pe : PathEnv) (r r' : Aref) (hwf : PathEnv.WellFormed pe)
    (hr_not_root : r ≠ Aref.root)
    (hr'_fresh : r' ∉ pe.refs) (_ : ∀ v, r' ≠ Aref.varRef v) :
    PathEnv.WellFormed (consume_ref_transfer pe r r') := by
  constructor
  · -- refs_complete: refs not in new list have empty paths from root
    intro v hv
    have hroot_ne_and : ¬(Aref.root = r ∧ v = r) := fun ⟨h, _⟩ => hr_not_root h.symm
    simp only [consume_ref_transfer, hroot_ne_and, ↓reduceIte] at hv ⊢
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
  · -- root_in_refs: .root survives filter since r ≠ .root
    simp only [consume_ref_transfer]
    have hroot_ne_r : Aref.root ≠ r := fun h => hr_not_root h.symm
    by_cases hr'in : r' ∈ pe.refs
    · simp only [hr'in, not_true_eq_false, ↓reduceIte, List.mem_filter, decide_eq_true_eq]
      exact ⟨hwf.root_in_refs, hroot_ne_r⟩
    · simp only [hr'in, not_false_eq_true, ↓reduceIte, List.mem_filter, decide_eq_true_eq,
                  List.mem_cons]
      exact ⟨Or.inr hwf.root_in_refs, hroot_ne_r⟩
  · -- from_untracked_to_root_empty
    intro u hu huroot
    -- .root ≠ r' (since .root ∈ pe.refs and r' ∉ pe.refs)
    have hroot_ne_r' : Aref.root ≠ r' := by
      intro h; exact hr'_fresh (h ▸ hwf.root_in_refs)
    have hu_and : ¬(u = r ∧ Aref.root = r) := fun ⟨_, h⟩ => hr_not_root h.symm
    simp only [consume_ref_transfer, hu_and, ↓reduceIte] at hu ⊢
    by_cases hur : u = r ∨ Aref.root = r
    · -- condition true → .empty
      simp only [hur, ↓reduceIte]
    · -- u ≠ r and .root ≠ r
      have hu_ne_r : u ≠ r := fun h => hur (Or.inl h)
      simp only [hur, ↓reduceIte]
      -- .root ≠ r', so if .root = r' is false
      simp only [hroot_ne_r', ↓reduceIte]
      -- paths = G(u, .root), need u ∉ pe.refs
      have hu_notin : u ∉ pe.refs := by
        intro hcontra; apply hu
        by_cases hr'in : r' ∈ pe.refs
        · simp only [hr'in, not_true_eq_false, ↓reduceIte, List.mem_filter, decide_eq_true_eq]
          exact ⟨hcontra, hu_ne_r⟩
        · simp only [hr'in, not_false_eq_true, ↓reduceIte, List.mem_filter, decide_eq_true_eq,
                      List.mem_cons]
          exact ⟨Or.inr hcontra, hu_ne_r⟩
      exact hwf.from_untracked_to_root_empty u hu_notin huroot
  · -- self_loop_accepts_nil
    intro u
    by_cases hur : u = r
    · subst hur; simp only [consume_ref_transfer, and_self, ↓reduceIte, interpret_regex]
    · simp only [consume_ref_transfer, ↓reduceIte, hur, false_or]
      by_cases hur' : u = r'
      · -- u = r': crt paths(r', r') = union(pe.paths(r', r'), pe.paths(r', r))
        rw [hur']; simp only [↓reduceIte]
        exact Or.inl (hwf.self_loop_accepts_nil r')
      · -- u ≠ r, u ≠ r': crt paths(u, u) = pe.paths(u, u)
        simp only [hur', ↓reduceIte]
        exact hwf.self_loop_accepts_nil u

/- ---------------------------------------------------- -/
/-  Standalone paths_from/to_non_member propagation      -/
/- ---------------------------------------------------- -/

/-- delete_ref_node preserves paths_from_non_member_empty -/
lemma delete_ref_node_paths_from_non_member (pe : PathEnv) (r : Aref)
    (h_from : ∀ u v p, u ∉ pe.refs → u ≠ .root → u ≠ v → ¬interpret_regex (pe.paths (u, v)) p) :
    ∀ u v p, u ∉ (delete_ref_node pe r).refs → u ≠ .root → u ≠ v →
    ¬interpret_regex ((delete_ref_node pe r).paths (u, v)) p := by
  intro u v p hu huroot huv
  simp only [delete_ref_node_refs, List.mem_filter, decide_eq_true_eq, not_and] at hu
  by_cases hur : u = r
  · have hvr : v ≠ r := fun h => huv (hur.trans h.symm)
    simp only [delete_ref_node]; rw [hur]
    rw [if_neg (fun ⟨_, h⟩ => hvr h), if_pos (Or.inl rfl)]
    exact not_false
  · have hu_not_in : u ∉ pe.refs := fun hc => hur (Decidable.not_not.mp (hu hc))
    simp only [delete_ref_node]
    by_cases hvr : v = r
    · rw [hvr, if_neg (fun ⟨h, _⟩ => hur h), if_pos (Or.inr rfl)]
      exact not_false
    · rw [if_neg (fun ⟨h, _⟩ => hur h), if_neg (not_or.mpr ⟨hur, hvr⟩)]
      exact h_from u v p hu_not_in huroot huv

/-- delete_ref_node preserves paths_to_non_member_empty -/
lemma delete_ref_node_paths_to_non_member (pe : PathEnv) (r : Aref)
    (h_to : ∀ u v p, v ∉ pe.refs → v ≠ .root → u ≠ v → ¬interpret_regex (pe.paths (u, v)) p) :
    ∀ u v p, v ∉ (delete_ref_node pe r).refs → v ≠ .root → u ≠ v →
    ¬interpret_regex ((delete_ref_node pe r).paths (u, v)) p := by
  intro u v p hv hvroot huv
  simp only [delete_ref_node_refs, List.mem_filter, decide_eq_true_eq, not_and] at hv
  by_cases hvr : v = r
  · have hur : u ≠ r := fun h => huv (h.trans hvr.symm)
    simp only [delete_ref_node]; rw [hvr]
    rw [if_neg (fun ⟨h, _⟩ => hur h), if_pos (Or.inr rfl)]
    exact not_false
  · have hv_not_in : v ∉ pe.refs := fun hc => hvr (Decidable.not_not.mp (hv hc))
    simp only [delete_ref_node]
    by_cases hur : u = r
    · rw [hur, if_neg (fun ⟨_, h⟩ => hvr h), if_pos (Or.inl rfl)]
      exact not_false
    · rw [if_neg (fun ⟨h, _⟩ => hur h), if_neg (not_or.mpr ⟨hur, hvr⟩)]
      exact h_to u v p hv_not_in hvroot huv

/-- update_with_extension preserves paths_from_non_member_empty (requires hx_tracked). -/
lemma update_with_extension_paths_from_non_member (z x : Aref) (path : List PathElement) (pe : PathEnv)
    (h_from : ∀ u v p, u ∉ pe.refs → u ≠ .root → u ≠ v → ¬interpret_regex (pe.paths (u, v)) p)
    (hx_tracked : x ∈ pe.refs ∨ x = z) :
    ∀ u v p, u ∉ (update_with_extension z x path pe).refs → u ≠ .root → u ≠ v →
    ¬interpret_regex ((update_with_extension z x path pe).paths (u, v)) p := by
  intro u v p' hu huroot huv
  simp only [update_with_extension] at hu ⊢
  have hu_ne_z : u ≠ z := by
    intro heq
    apply hu
    rw [heq]
    by_cases hzin : z ∈ pe.refs
    · simp only [hzin, not_true_eq_false, ↓reduceIte]
    · simp only [hzin, not_false_eq_true, ↓reduceIte, List.mem_cons]
      exact Or.inl trivial
  have hu_notin : u ∉ pe.refs := by
    intro hcontra
    apply hu
    by_cases hzin : z ∈ pe.refs
    · simp only [hzin, not_true_eq_false, ↓reduceIte]
      exact hcontra
    · simp only [hzin, not_false_eq_true, ↓reduceIte, List.mem_cons]
      exact Or.inr hcontra
  have hu_ne_x : u ≠ x := by
    cases hx_tracked with
    | inl hx_in => intro heq; exact hu_notin (heq ▸ hx_in)
    | inr hx_z => intro heq; exact hu_ne_z (heq ▸ hx_z)
  have hnotboth : ¬(u = z ∧ v = z) := by intro ⟨h, _⟩; exact hu_ne_z h
  rw [if_neg hnotboth]
  by_cases hvz : v = z
  · rw [if_pos hvz]
    exact no_match_extend path (fun q => h_from u x q hu_notin huroot hu_ne_x) p'
  · rw [if_neg hvz, if_neg hu_ne_z]
    exact h_from u v p' hu_notin huroot huv

/-- update_with_extension preserves paths_to_non_member_empty (requires hx_tracked). -/
lemma update_with_extension_paths_to_non_member (z x : Aref) (path : List PathElement) (pe : PathEnv)
    (h_to : ∀ u v p, v ∉ pe.refs → v ≠ .root → u ≠ v → ¬interpret_regex (pe.paths (u, v)) p)
    (hx_tracked : x ∈ pe.refs ∨ x = z) :
    ∀ u v p, v ∉ (update_with_extension z x path pe).refs → v ≠ .root → u ≠ v →
    ¬interpret_regex ((update_with_extension z x path pe).paths (u, v)) p := by
  intro u v p' hv hvroot huv
  simp only [update_with_extension] at hv ⊢
  have hv_ne_z : v ≠ z := by
    intro heq
    apply hv
    rw [heq]
    by_cases hzin : z ∈ pe.refs
    · simp only [hzin, not_true_eq_false, ↓reduceIte]
    · simp only [hzin, not_false_eq_true, ↓reduceIte, List.mem_cons]
      exact Or.inl trivial
  have hv_notin : v ∉ pe.refs := by
    intro hcontra
    apply hv
    by_cases hzin : z ∈ pe.refs
    · simp only [hzin, not_true_eq_false, ↓reduceIte]
      exact hcontra
    · simp only [hzin, not_false_eq_true, ↓reduceIte, List.mem_cons]
      exact Or.inr hcontra
  have hv_ne_x : v ≠ x := by
    cases hx_tracked with
    | inl hx_in => intro heq; exact hv_notin (heq ▸ hx_in)
    | inr hx_z => intro heq; exact hv_ne_z (heq ▸ hx_z)
  have hnotboth : ¬(u = z ∧ v = z) := by intro ⟨_, h⟩; exact hv_ne_z h
  rw [if_neg hnotboth, if_neg hv_ne_z]
  by_cases huz : u = z
  · rw [if_pos huz]
    exact no_match_der path (fun q => h_to x v q hv_notin hvroot hv_ne_x.symm) p'
  · rw [if_neg huz]
    exact h_to u v p' hv_notin hvroot huv

/-- consume_ref_transfer preserves paths_from_non_member_empty -/
lemma consume_ref_transfer_paths_from_non_member (pe : PathEnv) (r r' : Aref)
    (h_from : ∀ u v p, u ∉ pe.refs → u ≠ .root → u ≠ v → ¬interpret_regex (pe.paths (u, v)) p) :
    ∀ u v p, u ∉ (consume_ref_transfer pe r r').refs → u ≠ .root → u ≠ v →
    ¬interpret_regex ((consume_ref_transfer pe r r').paths (u, v)) p := by
  intro u v p hu huroot huv
  have huv_and : ¬(u = r ∧ v = r) := fun ⟨h1, h2⟩ => huv (h1.trans h2.symm)
  simp only [consume_ref_transfer, huv_and, ↓reduceIte] at hu ⊢
  by_cases hur : u = r
  · simp only [hur, true_or, ↓reduceIte, interpret_regex, not_false_eq_true]
  · have hu_notin : u ∉ pe.refs := by
      intro hcontra; apply hu
      by_cases hr'in : r' ∈ pe.refs
      · simp only [hr'in, not_true_eq_false, ↓reduceIte, List.mem_filter, decide_eq_true_eq]
        exact ⟨hcontra, hur⟩
      · simp only [hr'in, not_false_eq_true, ↓reduceIte, List.mem_filter, decide_eq_true_eq,
                    List.mem_cons]
        exact ⟨Or.inr hcontra, hur⟩
    have hu_ne_r' : u ≠ r' := by
      intro heq; apply hu
      by_cases hr'in : r' ∈ pe.refs
      · exact absurd (heq ▸ hu_notin) (not_not.mpr hr'in)
      · simp only [hr'in, not_false_eq_true, ↓reduceIte, List.mem_filter, decide_eq_true_eq,
                    List.mem_cons]
        exact ⟨Or.inl heq, hur⟩
    by_cases hvr : v = r
    · simp only [hur, hvr, or_true, ↓reduceIte, interpret_regex, not_false_eq_true]
    · have hcond : ¬(u = r ∨ v = r) := by intro h; cases h with
        | inl h => exact hur h
        | inr h => exact hvr h
      simp only [hcond, ↓reduceIte]
      by_cases hvr' : v = r'
      · simp only [hvr', ↓reduceIte]
        -- u ∉ pe.refs, r ∈ pe.refs → u ≠ r
        exact no_match_union
          (fun q => h_from u r' q hu_notin huroot hu_ne_r')
          (fun q => h_from u r q hu_notin huroot (fun h => hur h)) p
      · simp only [hvr', ↓reduceIte]
        exact h_from u v p hu_notin huroot huv

/-- consume_ref_transfer preserves paths_to_non_member_empty -/
lemma consume_ref_transfer_paths_to_non_member (pe : PathEnv) (r r' : Aref)
    (h_to : ∀ u v p, v ∉ pe.refs → v ≠ .root → u ≠ v → ¬interpret_regex (pe.paths (u, v)) p) :
    ∀ u v p, v ∉ (consume_ref_transfer pe r r').refs → v ≠ .root → u ≠ v →
    ¬interpret_regex ((consume_ref_transfer pe r r').paths (u, v)) p := by
  intro u v p hv hvroot huv
  have huv_and : ¬(u = r ∧ v = r) := fun ⟨h1, h2⟩ => huv (h1.trans h2.symm)
  simp only [consume_ref_transfer, huv_and, ↓reduceIte] at hv ⊢
  by_cases hvr : v = r
  · simp only [hvr, or_true, ↓reduceIte, interpret_regex, not_false_eq_true]
  · have hv_notin : v ∉ pe.refs := by
      intro hcontra; apply hv
      by_cases hr'in : r' ∈ pe.refs
      · simp only [hr'in, not_true_eq_false, ↓reduceIte, List.mem_filter, decide_eq_true_eq]
        exact ⟨hcontra, hvr⟩
      · simp only [hr'in, not_false_eq_true, ↓reduceIte, List.mem_filter, decide_eq_true_eq,
                    List.mem_cons]
        exact ⟨Or.inr hcontra, hvr⟩
    have hv_ne_r' : v ≠ r' := by
      intro heq; apply hv
      by_cases hr'in : r' ∈ pe.refs
      · exact absurd (heq ▸ hv_notin) (not_not.mpr hr'in)
      · simp only [hr'in, not_false_eq_true, ↓reduceIte, List.mem_filter, decide_eq_true_eq,
                    List.mem_cons]
        exact ⟨Or.inl heq, hvr⟩
    by_cases hur : u = r
    · simp only [hur, true_or, ↓reduceIte, interpret_regex, not_false_eq_true]
    · have hcond : ¬(u = r ∨ v = r) := by intro h; cases h with
        | inl h => exact hur h
        | inr h => exact hvr h
      simp only [hcond, ↓reduceIte, hv_ne_r', ↓reduceIte]
      exact h_to u v p hv_notin hvroot huv

/-- garbage_collect preserves paths_from_non_member_empty -/
lemma garbage_collect_paths_from_non_member (pe : PathEnv) (r : Aref)
    (h_from : ∀ u v p, u ∉ pe.refs → u ≠ .root → u ≠ v → ¬interpret_regex (pe.paths (u, v)) p) :
    ∀ u v p, u ∉ (garbage_collect pe r).refs → u ≠ .root → u ≠ v →
    ¬interpret_regex ((garbage_collect pe r).paths (u, v)) p := by
  intro u v p hu huroot huv
  simp only [garbage_collect, List.mem_filter, decide_eq_true_eq, not_and] at hu
  by_cases hur : u = r
  · -- u = r: ∧-cond is (True ∧ v = r) = (v = r), which is False since u ≠ v
    have hv_ne_r : ¬(v = r) := fun h => huv (hur ▸ h ▸ rfl)
    rw [hur]; simp only [garbage_collect, hv_ne_r, and_false, ↓reduceIte,
      true_or, interpret_regex, not_false_eq_true]
  · have hu_not_in : u ∉ pe.refs := fun hc => hur (Decidable.not_not.mp (hu hc))
    simp only [garbage_collect]
    by_cases hvr : v = r
    · simp only [hur, hvr, and_true, ↓reduceIte, or_true, interpret_regex, not_false_eq_true]
    · simp only [↓reduceIte, hur, hvr, or_self]
      exact h_from u v p hu_not_in huroot huv

/-- garbage_collect preserves paths_to_non_member_empty -/
lemma garbage_collect_paths_to_non_member (pe : PathEnv) (r : Aref)
    (h_to : ∀ u v p, v ∉ pe.refs → v ≠ .root → u ≠ v → ¬interpret_regex (pe.paths (u, v)) p) :
    ∀ u v p, v ∉ (garbage_collect pe r).refs → v ≠ .root → u ≠ v →
    ¬interpret_regex ((garbage_collect pe r).paths (u, v)) p := by
  intro u v p hv hvroot huv
  simp only [garbage_collect, List.mem_filter, decide_eq_true_eq, not_and] at hv
  by_cases hvr : v = r
  · -- v = r: ∧-cond is (u = r ∧ True) = (u = r), which is False since u ≠ v
    have hu_ne_r : ¬(u = r) := fun h => huv (h ▸ hvr ▸ rfl)
    rw [hvr]; simp only [garbage_collect, hu_ne_r, false_and, ↓reduceIte,
      or_true, interpret_regex, not_false_eq_true]
  · have hv_not_in : v ∉ pe.refs := fun hc => hvr (Decidable.not_not.mp (hv hc))
    simp only [garbage_collect]
    by_cases hur : u = r
    · simp only [hur, hvr, and_false, ↓reduceIte, true_or, interpret_regex, not_false_eq_true]
    · simp only [↓reduceIte, hur, hvr, or_self]
      exact h_to u v p hv_not_in hvroot huv

/- ---------------------------------------------------- -/
/-       TypeEnv.equiv lemmas                            -/
/- ---------------------------------------------------- -/

lemma TypeEnv.equiv_refl (env : TypeEnv) : TypeEnv.equiv env env := by
  exact ⟨LookupEquiv.refl _, VarEnvLookupCompatible.refl _, rfl, fun _ _ _ _ => rfl⟩

/- ---------------------------------------------------- -/
/-       call_connect_inputs_outputs WellFormed          -/
/- ---------------------------------------------------- -/

/-- Inner foldl of extend_with_star preserves PathEnv.WellFormed -/
private lemma extend_star_inner_foldl_wf (targets : List Aref) (source : Aref) (pe : PathEnv)
    (hwf : PathEnv.WellFormed pe) (h : ∀ t ∈ targets, t ≠ Aref.root) :
    PathEnv.WellFormed (targets.foldl (fun acc t => extend_with_star t source acc) pe) :=
  foldl_preserves_wf_mem _ pe targets hwf fun acc t ht hacc =>
    extend_with_star_wellformed t source acc hacc (h t ht)

/-- Refs extracted from SiteEnv by any-ref filterMap are not root -/
private lemma siteEnv_filterMap_ref_not_root (senv : SiteEnv) (sites : List Site)
    (hwf : SiteEnv.RefsNotRoot senv) :
    ∀ r ∈ List.filterMap (fun a => match lookup senv a with
      | some (.ref _ r _) => some r | _ => none) sites, r ≠ Aref.root := by
  intro r hr
  rw [List.mem_filterMap] at hr
  obtain ⟨s, _, hs⟩ := hr
  revert hs
  cases hlookup : lookup senv s with
  | none => simp
  | some τ =>
    cases τ with
    | basic _ => simp
    | ref bt r' bk => simp only [Option.some.injEq]; intro heq; subst heq; exact hwf s _ hlookup

/-- Refs extracted from SiteEnv by mut-only filterMap are not root -/
private lemma siteEnv_filterMap_mut_not_root (senv : SiteEnv) (sites : List Site)
    (hwf : SiteEnv.RefsNotRoot senv) :
    ∀ r ∈ List.filterMap (fun a => match lookup senv a with
      | some (.ref _ r .siteBorrowMut) => some r | _ => none) sites, r ≠ Aref.root := by
  intro r hr
  rw [List.mem_filterMap] at hr
  obtain ⟨s, _, hs⟩ := hr
  revert hs
  cases hlookup : lookup senv s with
  | none => simp
  | some τ =>
    cases τ with
    | basic _ => simp
    | ref bt r' bk =>
      cases bk
      · simp  -- siteBorrowImm: none = some r
      · simp only [Option.some.injEq]
        intro heq; subst heq; exact hwf s _ hlookup

/-- Refs extracted from SiteEnv by imm-only filterMap are not root -/
private lemma siteEnv_filterMap_imm_not_root (senv : SiteEnv) (sites : List Site)
    (hwf : SiteEnv.RefsNotRoot senv) :
    ∀ r ∈ List.filterMap (fun a => match lookup senv a with
      | some (.ref _ r .siteBorrowImm) => some r | _ => none) sites, r ≠ Aref.root := by
  intro r hr
  rw [List.mem_filterMap] at hr
  obtain ⟨s, _, hs⟩ := hr
  revert hs
  cases hlookup : lookup senv s with
  | none => simp
  | some τ =>
    cases τ with
    | basic _ => simp
    | ref bt r' bk =>
      cases bk
      · simp only [Option.some.injEq]
        intro heq; subst heq; exact hwf s _ hlookup
      · simp  -- siteBorrowMut: none = some r

lemma call_connect_inputs_outputs_wf (env : TypeEnv) (as bs : List Site)
    (hwf : TypeEnv.WellFormed env) :
    TypeEnv.WellFormed (call_connect_inputs_outputs env as bs) := by
  constructor
  · -- pathEnv_wf: only pathEnv changes
    show PathEnv.WellFormed (call_connect_inputs_outputs env as bs).pathEnv
    simp only [call_connect_inputs_outputs]
    -- Not-root facts for the ref lists
    have h_inputs := siteEnv_filterMap_ref_not_root env.siteEnv bs hwf.siteEnv_wf
    have h_mi := siteEnv_filterMap_mut_not_root env.siteEnv bs hwf.siteEnv_wf
    have h_io := siteEnv_filterMap_imm_not_root env.siteEnv as hwf.siteEnv_wf
    -- Rule 3 (outermost foldl over io)
    apply foldl_preserves_wf_mem
    · -- Rule 2 (middle foldl over mo)
      apply foldl_preserves_wf_mem
      · -- Rule 1 (innermost foldl over io)
        apply foldl_preserves_wf_mem
        · exact hwf.pathEnv_wf
        · intro acc iout _ hacc
          exact extend_star_inner_foldl_wf _ iout acc hacc h_inputs
      · intro acc mout _ hacc
        exact extend_star_inner_foldl_wf _ mout acc hacc h_mi
    · intro acc io1 hio1 hacc
      -- Rule 3 inner foldl: conditional extend_with_star
      apply foldl_preserves_wf_mem
      · exact hacc
      · intro acc' io2 _ hacc'
        simp only [ne_eq]
        split
        · exact extend_with_star_wellformed io1 io2 acc' hacc' (h_io io1 hio1)
        · exact hacc'
  · -- siteEnv_wf: unchanged
    exact hwf.siteEnv_wf
  · -- varEnv_wf: unchanged
    exact hwf.varEnv_wf

/-- populate_call_outputs preserves WellFormed -/
lemma populate_call_outputs_wf (env env' : TypeEnv) (as : List Site) (rets : List ParamType)
    (outRefs : List Aref)
    (hwf : TypeEnv.WellFormed env)
    (hout_not_root : ∀ r ∈ outRefs, r ≠ Aref.root)
    (hout_not_varRef : ∀ r ∈ outRefs, ∀ v, r ≠ Aref.varRef v)
    (hpop : populate_call_outputs env as rets outRefs = some env') :
    TypeEnv.WellFormed env' := by
  induction as generalizing env rets outRefs with
  | nil =>
    cases rets with
    | nil =>
      simp only [populate_call_outputs] at hpop
      split at hpop
      · simp only [Option.some.injEq] at hpop; subst hpop; exact hwf
      · simp at hpop
    | cons _ _ => simp [populate_call_outputs] at hpop
  | cons site as' ih =>
    cases rets with
    | nil => simp [populate_call_outputs] at hpop
    | cons pt rets' =>
      obtain ⟨bt, isRefMut⟩ := pt
      cases isRefMut with
      | none =>
        -- Basic return: only siteEnv changes
        simp only [populate_call_outputs] at hpop
        have hwf_mid : TypeEnv.WellFormed
            { env with siteEnv := insert env.siteEnv site (.basic bt) } :=
          ⟨hwf.pathEnv_wf,
           SiteEnv.insert_refs_not_root env.siteEnv site (.basic bt) hwf.siteEnv_wf trivial,
           hwf.varEnv_wf⟩
        exact ih _ _ _ hwf_mid hout_not_root hout_not_varRef hpop
      | some b =>
        cases b with
        | true =>
          -- Mutable ref return: siteEnv + pathEnv change
          cases outRefs with
          | nil => simp [populate_call_outputs] at hpop
          | cons r outRefs' =>
            simp only [populate_call_outputs] at hpop
            have hr_mem := List.mem_cons.mpr (Or.inl rfl : r = r ∨ r ∈ outRefs')
            have hwf_mid : TypeEnv.WellFormed
                { env with
                  siteEnv := insert env.siteEnv site (.ref bt r .siteBorrowMut)
                  pathEnv := update_with_epsilon r r env.pathEnv } :=
              ⟨update_with_epsilon_wellformed r r env.pathEnv hwf.pathEnv_wf
                (hout_not_root r hr_mem) (hout_not_varRef r hr_mem),
               SiteEnv.insert_refs_not_root env.siteEnv site (.ref bt r .siteBorrowMut)
                hwf.siteEnv_wf (hout_not_root r hr_mem),
               hwf.varEnv_wf⟩
            exact ih _ _ _ hwf_mid
              (fun r' hr' => hout_not_root r' (List.mem_cons.mpr (Or.inr hr')))
              (fun r' hr' => hout_not_varRef r' (List.mem_cons.mpr (Or.inr hr')))
              hpop
        | false =>
          -- Immutable ref return: siteEnv + pathEnv change
          cases outRefs with
          | nil => simp [populate_call_outputs] at hpop
          | cons r outRefs' =>
            simp only [populate_call_outputs] at hpop
            have hr_mem := List.mem_cons.mpr (Or.inl rfl : r = r ∨ r ∈ outRefs')
            have hwf_mid : TypeEnv.WellFormed
                { env with
                  siteEnv := insert env.siteEnv site (.ref bt r .siteBorrowImm)
                  pathEnv := update_with_epsilon r r env.pathEnv } :=
              ⟨update_with_epsilon_wellformed r r env.pathEnv hwf.pathEnv_wf
                (hout_not_root r hr_mem) (hout_not_varRef r hr_mem),
               SiteEnv.insert_refs_not_root env.siteEnv site (.ref bt r .siteBorrowImm)
                hwf.siteEnv_wf (hout_not_root r hr_mem),
               hwf.varEnv_wf⟩
            exact ih _ _ _ hwf_mid
              (fun r' hr' => hout_not_root r' (List.mem_cons.mpr (Or.inr hr')))
              (fun r' hr' => hout_not_varRef r' (List.mem_cons.mpr (Or.inr hr')))
              hpop

end LeanMove.Typing
