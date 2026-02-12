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

import LeanMove.Typing.Algorithmic.TypeCheckingAlgorithmic
import LeanMove.Typing.TypesUtils

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

Bridge lemmas connect boolean checker functions to their relational specifications.
Type environment invariant definitions and preservation lemmas are in `TypesUtils.lean`.
-/
namespace LeanMove.Typing

open Lang
open Lang.MoveLight
open AssocMap
open Regex

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


/-- Looking up a different key after insert returns the original value -/
private lemma lookup_insert_ne {K V : Type} [DecidableEq K]
    (m : AssocMap K V) (k k' : K) (v : V) (hne : k' ≠ k) :
    AssocMap.lookup (AssocMap.insert m k v) k' = AssocMap.lookup m k' := by
  simp only [AssocMap.lookup, AssocMap.insert]
  simp only [List.lookup]
  split
  · rename_i h; exact absurd (beq_iff_eq.mp h) hne
  · exact List.lookup_filter_ne m.entries k' k hne

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
  exact List.nodup_snd_pair_absurd fields (List.nodup_of_length_eraseDups _ hsites) hf₁ hf₂ hfne

/-- If check_fields_distinct returns true, field names are Nodup -/
private lemma check_fields_distinct_implies_fnames_nodup (fields : List (Field × Site)) :
    check_fields_distinct fields = true → (fields.map Prod.fst).Nodup := by
  intro h
  simp only [check_fields_distinct, beq_iff_eq, Bool.and_eq_true] at h
  exact List.nodup_of_length_eraseDups _ h.2

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

end LeanMove.Typing
