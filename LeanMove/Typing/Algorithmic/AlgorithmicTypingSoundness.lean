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

import LeanMove.Typing.Algorithmic.AlgorithmicTypeChecking
import LeanMove.Typing.TypesUtils

/-!
# Algorithmic Typing Soundness for MoveLight

This file contains soundness proofs for the algorithmic type
checker defined in `AlgorithmicTypeChecking.lean` with respect to the relational
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

private lemma band_left {a b : Bool} (h : (a && b) = true) : a = true := by cases a <;> simp_all
private lemma band_right {a b : Bool} (h : (a && b) = true) : b = true := by cases a <;> simp_all

lemma TypeEnv.equiv_bool_implies_equiv (env1 env2 : TypeEnv) :
    TypeEnv.equiv_bool env1 env2 = true → TypeEnv.equiv env1 env2 := by
  intro h
  -- equiv_bool = site && var && refs && paths && enum
  unfold TypeEnv.equiv_bool at h
  have henum := band_right h
  have h4 := band_left h
  have hpaths_raw := band_right h4
  have h3 := band_left h4
  have hrefs_raw := band_right h3
  have h2 := band_left h3
  have hvar := band_right h2
  have hsite := band_left h2
  have hrefs := beq_iff_eq.mp hrefs_raw
  simp only [List.all_eq_true] at hpaths_raw
  refine ⟨lookup_equiv_bool_sound _ _ hsite, varenv_lookup_compatible_bool_sound _ _ hvar, hrefs, ?_, lookup_equiv_bool_sound _ _ henum⟩
  intro u v hu hv
  have hu' := hpaths_raw u hu
  exact regexBeq_eq _ _ (hu' v hv)

/- ---------------------------------------------------- -/
/-       not_borrowed soundness (WellFormed → Bool → Prop)   -/
/- ---------------------------------------------------- -/

/-- Soundness: if boolean check passes, semantic property holds.
    not_borrowed now only quantifies over r ∈ refs, matching the algorithmic check. -/
lemma not_borrowed_bool_sound (x : Var) (env : TypeEnv)
    (_ : PathEnv.WellFormed env.pathEnv) :
    not_borrowed_bool x env = true → not_borrowed x env := by
  intro hbool
  simp only [not_borrowed_bool, List.all_eq_true] at hbool
  intro r hr
  show ¬ interpret_regex (env.pathEnv.paths (.root, r)) [.root_to_var x]
  have h := hbool r hr
  simp only [Bool.not_eq_true'] at h
  intro haccept
  have hmatch := @Regex.match_bool_complete _ _ _ _ haccept
  simp [hmatch] at h

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
/-       Return checking boolean soundness               -/
/- ---------------------------------------------------- -/

lemma ret_refs_not_from_locals_bool_sound (env : TypeEnv) (as : List Site) :
    ret_refs_not_from_locals_bool env as = true →
    (∀ a ∈ as, ∀ bt r bk, lookup env.siteEnv a = some (.ref bt r bk) →
      ∀ p, ¬interpret_regex (env.pathEnv.paths (.root, r)) p) := by
  intro h a ha bt r bk hlook p hp
  simp only [ret_refs_not_from_locals_bool, List.all_eq_true] at h
  have ha' := h a ha
  simp only [hlook] at ha'
  have := is_empty_sound _ ha' p
  rw [simplify_preserves_semantics] at this
  exact this hp

private lemma list_lookup_mem {K V : Type} [DecidableEq K]
    (l : List (K × V)) (k : K) (v : V) (h : List.lookup k l = some v) :
    (k, v) ∈ l := by
  induction l with
  | nil => cases h
  | cons hd tl ih =>
    unfold List.lookup at h
    split at h
    · rename_i heq
      have hk : k = hd.1 := beq_iff_eq.mp heq
      have hv : hd.2 = v := by injection h
      subst hk; subst hv; exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (ih h)

private lemma lookup_mem_entries {K V : Type} [DecidableEq K]
    (m : AssocMap K V) (k : K) (v : V) (h : lookup m k = some v) :
    (k, v) ∈ m.entries :=
  list_lookup_mem m.entries k v h

lemma ret_mutable_writable_bool_sound (env : TypeEnv) (as : List Site) :
    ret_mutable_writable_bool env as = true →
    (∀ a ∈ as, ∀ bt r, lookup env.siteEnv a = some (.ref bt r .siteBorrowMut) →
      ∀ b, b ∉ as →
        ∀ bt' r' bk', lookup env.siteEnv b = some (.ref bt' r' bk') →
          ∀ p, interpret_regex (env.pathEnv.paths (r, r')) p → p = []) := by
  intro h a ha bt r hlook b hb bt' r' bk' hlook_b p hp
  simp only [ret_mutable_writable_bool, List.all_eq_true] at h
  have ha' := h a ha
  simp only [hlook] at ha'
  have hall := List.all_eq_true.mp ha'
  have hmem := lookup_mem_entries env.siteEnv b (.ref bt' r' bk') hlook_b
  have hentry := hall (b, .ref bt' r' bk') hmem
  simp only at hentry
  rw [if_neg (by exact fun hmem => hb hmem)] at hentry
  have := only_matches_empty_sound _ hentry p
  rw [simplify_preserves_semantics] at this
  exact this hp

lemma ret_mutable_no_aliases_bool_sound (env : TypeEnv) (as : List Site) :
    ret_mutable_no_aliases_bool env as = true →
    (∀ a₁ ∈ as, ∀ bt₁ r₁, lookup env.siteEnv a₁ = some (.ref bt₁ r₁ .siteBorrowMut) →
      ∀ a₂ ∈ as, a₁ ≠ a₂ →
        ∀ bt₂ r₂ bk₂, lookup env.siteEnv a₂ = some (.ref bt₂ r₂ bk₂) →
          ∀ p, ¬interpret_regex (env.pathEnv.paths (r₂, r₁)) p) := by
  intro h a₁ ha₁ bt₁ r₁ hlook₁ a₂ ha₂ hne bt₂ r₂ bk₂ hlook₂ p hp
  simp only [ret_mutable_no_aliases_bool, List.all_eq_true] at h
  have ha₁' := h a₁ ha₁
  simp only [hlook₁] at ha₁'
  have hall := List.all_eq_true.mp ha₁'
  have ha₂' := hall a₂ ha₂
  simp only [bne_iff_ne] at ha₂'
  rw [if_pos hne] at ha₂'
  simp only [hlook₂] at ha₂'
  have := is_empty_sound _ ha₂' p
  rw [simplify_preserves_semantics] at this
  exact this hp

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
  exact only_matches_empty_sound _ h2

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

/-- If the pack fold succeeds from empty init, every key in the result comes from some field -/
private lemma foldlM_pack_complete
    (siteEnv : SiteEnv) (fields : List (Field × Site))
    (init fentries : AssocMap Field BasicMoveType)
    (hfold : fields.foldlM (fun acc (p : Field × Site) =>
      match AssocMap.lookup siteEnv p.2 with
      | some (.basic bt) => some (AssocMap.insert acc p.1 bt)
      | _ => none) init = some fentries)
    (f : Field) (hne : lookup fentries f ≠ none)
    (hinit : lookup init f = none) :
    ∃ a, (f, a) ∈ fields := by
  induction fields generalizing init with
  | nil =>
    simp only [List.foldlM, pure, Option.some.injEq] at hfold
    subst hfold; exact absurd hinit hne
  | cons hd tl ih =>
    obtain ⟨f', s'⟩ := hd
    simp only [List.foldlM, bind, Option.bind] at hfold
    cases hlk : lookup siteEnv s' with
    | none => simp [hlk] at hfold
    | some mt =>
      cases mt with
      | basic bt =>
        simp [hlk] at hfold
        by_cases heq : f = f'
        · exact ⟨s', by subst heq; exact List.mem_cons_self⟩
        · have hinit' : lookup (insert init f' bt) f = none := by
            rw [lookup_insert_ne _ f' f bt heq]; exact hinit
          obtain ⟨a, ha⟩ := ih _ hfold hinit'
          exact ⟨a, List.mem_cons_of_mem _ ha⟩
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
lemma check_letBind_sound (lenv : LabelEnv) (env : TypeEnv) (a : Site) (e : Expr) (cont : Stmt) (retTypes : List ParamType)
    (hwf : TypeEnv.WellFormed env)
    (ih_cont : ∀ env', TypeEnv.WellFormed env' →
        (check_stmt lenv env' cont retTypes).isSome = true → typecheck_stmt lenv env' cont retTypes)
    (h : (check_stmt lenv env (.letBind a e cont) retTypes).isSome = true) :
    typecheck_stmt lenv env (.letBind a e cont) retTypes := by
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
            · -- τ comes from varEnv, so it satisfies RefsNotRoot by hwf.varEnv_wf
              have hτ_not_root := VarEnv.lookup_type_refs_not_root env.varEnv x .validVar τ ms hwf.varEnv_wf hlookup
              rw [moveTypeRefsNotRoot_eq] at hτ_not_root
              have hwf' := TypeEnv.insert_update_wf env a τ x (.invalidVar, τ, ms) hwf hτ_not_root hτ_not_root
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
            let t := nextFreshRefInEnv env
            apply typecheck_stmt.let_bind_copy_ref (τ := τ) (s := s) (t := t) (isBor := isBor) (ms := ms)
            · simp only [hlookup]
            · exact hfresh
            · exact nextFreshRefInEnv_fresh_prop env
            · have ht_not_root : t ≠ Aref.root := nextFreshRefInEnv_not_root env
              have hpe' := update_with_epsilon_wellformed t s env.pathEnv hwf.pathEnv_wf ht_not_root
              have hτ : match (MoveType.ref τ t isBor) with | .ref _ r _ => r ≠ Aref.root | .basic _ => True :=
                nextFreshRefInEnv_not_root env
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
            let r := nextFreshRefInEnv env
            apply typecheck_stmt.let_bind_borrowImm (τ := τ) (ms := ms) (r := r)
            · simp only [hlookup]
            · exact hfresh
            · exact nextFreshRefInEnv_fresh_prop env
            · have hr_not_root : r ≠ Aref.root := nextFreshRefInEnv_not_root env
              have hpe' := update_with_extension_wellformed r .root [.root_to_var x] _
                (update_with_epsilon_wellformed r r env.pathEnv hwf.pathEnv_wf hr_not_root) hr_not_root
              have hτ : match (MoveType.ref τ r .siteBorrowImm) with | .ref _ r' _ => r' ≠ Aref.root | .basic _ => True :=
                nextFreshRefInEnv_not_root env
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
            obtain ⟨hms, hnotIn⟩ := hcond
            let r := nextFreshRefInEnv env
            apply typecheck_stmt.let_bind_borrowMut (τ := τ) (ms := ms) (r := r)
            · simp only [hms, LE.le, Mut.le]
            · simp only [hlookup]
            · exact hnotIn
            · exact nextFreshRefInEnv_fresh_prop env
            · have hr_not_root : r ≠ Aref.root := nextFreshRefInEnv_not_root env
              have hpe' := update_with_extension_wellformed r .root [.root_to_var x] _
                (update_with_epsilon_wellformed r r env.pathEnv hwf.pathEnv_wf hr_not_root) hr_not_root
              have hwf' : TypeEnv.WellFormed
                  {env with siteEnv := insert env.siteEnv a (.ref τ r .siteBorrowMut)
                            pathEnv := update_with_epsilon r r env.pathEnv |>
                                       update_with_extension r .root [.root_to_var x]} :=
                ⟨hpe', SiteEnv.insert_refs_not_root env.siteEnv a _ hwf.siteEnv_wf hr_not_root, hwf.varEnv_wf⟩
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

  -- Unary operation
  | unop uop src =>
    simp only [check_stmt] at h
    cases hlookup : lookup env.siteEnv src with
    | none => simp [hlookup] at h
    | some τ =>
      simp only [hlookup] at h
      cases τ with
      | basic bt1 =>
        cases hunop : unop_type uop bt1 with
        | none => simp [hunop] at h
        | some bt2 =>
          simp only [hunop] at h
          split at h
          · rename_i hfresh
            apply typecheck_stmt.let_bind_unop
            · exact hlookup
            · exact hunop
            · exact hfresh
            · have hwf' := TypeEnv.delete_insert_wf env src a (.basic bt2) hwf trivial
              exact ih_cont _ hwf' h
          · simp at h
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
          let r' := nextFreshRefInEnv env
          apply typecheck_stmt.let_bind_freeze (r' := r')
          · exact hlookup
          · exact hfresh
          · exact nextFreshRefInEnv_fresh_prop env
          · have hr_not_root : r ≠ Aref.root := hwf.siteEnv_wf src (.ref bt r isBor) hlookup
            have hr'_fresh : r' ∉ env.pathEnv.refs := nextFreshRefInEnv_not_in_pathEnv env
            have hr'_not_paramRef : ∀ v, r' ≠ Aref.paramRef v := nextFreshRefInEnv_not_paramRef env
            have hpe' := consume_ref_transfer_wellformed env.pathEnv r r' hwf.pathEnv_wf
              hr_not_root hr'_fresh hr'_not_paramRef
            have hτ : match (MoveType.ref bt r' .siteBorrowImm) with | .ref _ r'' _ => r'' ≠ Aref.root | .basic _ => True :=
              nextFreshRefInEnv_not_root env
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
                let rf := nextFreshRefInEnv env
                have hbt_eq : BasicMoveType.trecord fentries = bt' :=
                  BasicMoveType.eq_of_beq _ _ hbeq
                apply typecheck_stmt.let_bind_borrowField (bt := .trecord fentries)
                    (bt' := btf) (isBor := isBor) (fentries := fentries) (s := s) (rf := rf)
                · simp only [hlookup, hbt_eq]
                · rfl
                · exact hlookupf
                · exact hfresh
                · exact nextFreshRefInEnv_fresh_prop env
                · have hrf_not_root : rf ≠ Aref.root := nextFreshRefInEnv_not_root env
                  have hpe' := update_with_extension_wellformed rf s [.field f] env.pathEnv hwf.pathEnv_wf hrf_not_root
                  have hτ : match (MoveType.ref btf rf isBor) with | .ref _ r _ => r ≠ Aref.root | .basic _ => True :=
                    nextFreshRefInEnv_not_root env
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
                  let rf := nextFreshRefInEnv env
                  have hbt_eq : BasicMoveType.trecord fentries = bt' :=
                    BasicMoveType.eq_of_beq _ _ hbeq
                  apply typecheck_stmt.let_bind_borrowMutField (bt := .trecord fentries)
                      (btf := btf) (fentries := fentries) (s := s) (rf := rf)
                  · simp only [hlookup, hbt_eq]
                  · rfl
                  · exact hlookupf
                  · exact hfresh
                  · exact nextFreshRefInEnv_fresh_prop env
                  · have hrf_not_root : rf ≠ Aref.root := nextFreshRefInEnv_not_root env
                    have hpe' := update_with_extension_wellformed rf s [.field f] env.pathEnv hwf.pathEnv_wf hrf_not_root
                    have hτ : match (MoveType.ref btf rf .siteBorrowMut) with | .ref _ r _ => r ≠ Aref.root | .basic _ => True :=
                      nextFreshRefInEnv_not_root env
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
        · -- Every fentries key comes from fields
          intro f hne
          exact foldlM_pack_complete env.siteEnv fields AssocMap.empty fentries hfold f hne
            (by simp [AssocMap.lookup, AssocMap.empty])
        · exact check_fields_distinct_implies_sites_distinct fields hdistinct
        · have hwf' := TypeEnv.deleteAll_insert_wf env (fields.map Prod.snd) a (.basic (.trecord fentries)) hwf trivial
          exact ih_cont _ hwf' h
      · simp at h
    · simp at h

  -- Variant pack
  | packVariant enumName variantName fields =>
    simp only [check_stmt] at h
    -- Split on freshness and distinctness check
    split at h
    · rename_i hcond
      simp only [Bool.and_eq_true] at hcond
      obtain ⟨hfresh, hdistinct⟩ := hcond
      -- Split on foldlM result (collecting field types)
      split at h
      · rename_i fentries hfold
        -- Split on enum lookup in enumEnv
        split at h
        · rename_i enumDef hlookup_enum
          -- Split on variant lookup in enumDef.variants
          split at h
          · rename_i variantDef hlookup_variant
            -- Split on equality check (fentries == variantDef.fields)
            split at h
            · rename_i heq_fentries
              -- Apply the typing rule
              apply typecheck_stmt.let_bind_packVariant
              · exact hfresh
              · exact hlookup_enum
              · exact hlookup_variant
              · -- Prove field types match
                intro f a hmem
                rw [beq_iff_eq] at heq_fentries
                have := foldlM_pack_sound env.siteEnv fields AssocMap.empty fentries hfold
                  (check_fields_distinct_implies_fnames_nodup fields hdistinct) hmem
                rw [heq_fentries] at this; exact this
              · -- Prove all required fields are present
                intro f hne
                rw [beq_iff_eq] at heq_fentries
                exact foldlM_pack_complete env.siteEnv fields AssocMap.empty fentries hfold f
                  (heq_fentries ▸ hne) (by simp [AssocMap.lookup, AssocMap.empty])
              · -- Prove sites are distinct
                exact check_fields_distinct_implies_sites_distinct fields hdistinct
              · -- Continue with updated environment
                have hwf' := TypeEnv.deleteAll_insert_wf env (fields.map Prod.snd) a
                  (.basic (.tenum enumName)) hwf trivial
                exact ih_cont _ hwf' h
            · simp at h
          · simp at h
        · simp at h
      · simp at h
    · simp at h

  -- Vector pack
  | vecPack T elems =>
    simp only [check_stmt] at h
    split at h
    · rename_i hcond
      simp only [Bool.and_eq_true] at hcond
      obtain ⟨⟨hfresh, hnodup_bool⟩, hall⟩ := hcond
      apply typecheck_stmt.let_bind_vecPack
      · exact hfresh
      · intro s hs
        simp only [List.all_eq_true] at hall
        have hs' := hall s hs
        cases hlookup_s : lookup env.siteEnv s with
        | none => simp [hlookup_s] at hs'
        | some τ =>
          cases τ with
          | ref _ _ _ => simp [hlookup_s] at hs'
          | basic bt =>
            simp only [hlookup_s] at hs'
            have hteq := BasicMoveType.eq_of_beq T bt hs'
            rw [hteq]
      · exact List.nodup_of_length_eraseDups elems (beq_iff_eq.mp hnodup_bool).symm
      · have hwf' := TypeEnv.deleteAll_insert_wf env elems a (.basic (.tvec T)) hwf trivial
        exact ih_cont _ hwf' h
    · simp at h

  -- Vector length
  | vecLen src =>
    simp only [check_stmt] at h
    cases hlookup : lookup env.siteEnv src with
    | none => simp [hlookup] at h
    | some τ =>
      cases τ with
      | basic _ => simp [hlookup] at h
      | ref bt r isBor =>
        cases bt with
        | tvec T =>
          simp only [hlookup] at h
          split at h
          · rename_i hfresh
            apply typecheck_stmt.let_bind_vecLen (T := T) (r := r) (isBor := isBor)
            · exact hlookup
            · exact hfresh
            · have hr_not_root : r ≠ Aref.root := hwf.siteEnv_wf src (.ref (.tvec T) r isBor) hlookup
              have hpe' := delete_ref_node_wellformed env.pathEnv r hwf.pathEnv_wf hr_not_root
              have hwf' := TypeEnv.delete_insert_pathEnv_wf env src a (.basic .u64) _ hwf hpe' trivial
              exact ih_cont _ hwf' h
          · simp at h
        | _ => simp [hlookup] at h

  -- Vector immutable borrow
  | vecImmBorrow src idx =>
    simp only [check_stmt] at h
    cases hlookup_src : lookup env.siteEnv src with
    | none => simp [hlookup_src] at h
    | some τ_src =>
      cases hlookup_idx : lookup env.siteEnv idx with
      | none => simp [hlookup_src, hlookup_idx] at h
      | some τ_idx =>
        cases τ_src with
        | basic _ => simp [hlookup_src, hlookup_idx] at h
        | ref bt s isBor =>
          cases τ_idx with
          | ref _ _ _ => simp [hlookup_src, hlookup_idx] at h
          | basic bt_idx =>
            cases bt with
            | tvec T =>
              cases bt_idx with
              | u64 =>
                cases isBor with
                | siteBorrowImm =>
                  -- Source is &vector<T>: no check_outbound needed
                  simp only [hlookup_src, hlookup_idx] at h
                  split at h
                  · rename_i hfresh
                    let rf := nextFreshRefInEnv env
                    apply typecheck_stmt.let_bind_vecImmBorrow (T := T) (s := s) (rf := rf) (isBor := .siteBorrowImm)
                    · exact hlookup_src
                    · exact hlookup_idx
                    · exact hfresh
                    · intro habs; exact absurd habs (by decide)
                    · exact nextFreshRefInEnv_fresh_prop env
                    · have hrf_not_root : rf ≠ Aref.root := nextFreshRefInEnv_not_root env
                      have hpe' := update_with_extension_wellformed rf s [.vecElem] env.pathEnv hwf.pathEnv_wf hrf_not_root
                      have hτ : match (MoveType.ref T rf .siteBorrowImm) with | .ref _ r _ => r ≠ Aref.root | .basic _ => True :=
                        nextFreshRefInEnv_not_root env
                      have hsenv_del1 := SiteEnv.delete_refs_not_root env.siteEnv src hwf.siteEnv_wf
                      have hsenv_del2 := SiteEnv.delete_refs_not_root _ idx hsenv_del1
                      have hsenv_ins := SiteEnv.insert_refs_not_root _ a (.ref T rf .siteBorrowImm) hsenv_del2 hτ
                      have hwf' : TypeEnv.WellFormed
                        {env with siteEnv := insert (delete (delete env.siteEnv src) idx) a (.ref T rf .siteBorrowImm)
                                  pathEnv := update_with_extension rf s [.vecElem] env.pathEnv} :=
                        ⟨hpe', hsenv_ins, hwf.varEnv_wf⟩
                      exact ih_cont _ hwf' h
                  · simp at h
                | siteBorrowMut =>
                  -- Source is &mut vector<T>: check_outbound required
                  simp only [hlookup_src, hlookup_idx] at h
                  split at h
                  · rename_i hcond
                    have hfresh : notIn env.siteEnv a = true := by
                      cases h : notIn env.siteEnv a
                      · simp [h] at hcond
                      · rfl
                    have hcob : check_outbound_bool env.pathEnv s = true := by
                      cases h : check_outbound_bool env.pathEnv s
                      · simp [h] at hcond
                      · rfl
                    have hout : check_outbound env.pathEnv s (fun re => only_matches_empty (simplify re)) := by
                      intro s' hs'
                      simp only [check_outbound_bool, List.all_eq_true] at hcob
                      exact hcob s' hs'
                    let rf := nextFreshRefInEnv env
                    apply typecheck_stmt.let_bind_vecImmBorrow (T := T) (s := s) (rf := rf) (isBor := .siteBorrowMut)
                    · exact hlookup_src
                    · exact hlookup_idx
                    · exact hfresh
                    · intro _; exact hout
                    · exact nextFreshRefInEnv_fresh_prop env
                    · have hrf_not_root : rf ≠ Aref.root := nextFreshRefInEnv_not_root env
                      have hpe' := update_with_extension_wellformed rf s [.vecElem] env.pathEnv hwf.pathEnv_wf hrf_not_root
                      have hτ : match (MoveType.ref T rf .siteBorrowImm) with | .ref _ r _ => r ≠ Aref.root | .basic _ => True :=
                        nextFreshRefInEnv_not_root env
                      have hsenv_del1 := SiteEnv.delete_refs_not_root env.siteEnv src hwf.siteEnv_wf
                      have hsenv_del2 := SiteEnv.delete_refs_not_root _ idx hsenv_del1
                      have hsenv_ins := SiteEnv.insert_refs_not_root _ a (.ref T rf .siteBorrowImm) hsenv_del2 hτ
                      have hwf' : TypeEnv.WellFormed
                        {env with siteEnv := insert (delete (delete env.siteEnv src) idx) a (.ref T rf .siteBorrowImm)
                                  pathEnv := update_with_extension rf s [.vecElem] env.pathEnv} :=
                        ⟨hpe', hsenv_ins, hwf.varEnv_wf⟩
                      exact ih_cont _ hwf' h
                  · simp at h
              | _ => simp [hlookup_src, hlookup_idx] at h
            | _ => simp [hlookup_src, hlookup_idx] at h

  -- Vector mutable borrow
  | vecMutBorrow src idx =>
    simp only [check_stmt] at h
    cases hlookup_src : lookup env.siteEnv src with
    | none => simp [hlookup_src] at h
    | some τ_src =>
      cases hlookup_idx : lookup env.siteEnv idx with
      | none => simp [hlookup_src, hlookup_idx] at h
      | some τ_idx =>
        cases τ_src with
        | basic _ => simp [hlookup_src, hlookup_idx] at h
        | ref bt s isBor =>
          cases isBor with
          | siteBorrowImm => simp [hlookup_src, hlookup_idx] at h
          | siteBorrowMut =>
            cases τ_idx with
            | ref _ _ _ => simp [hlookup_src, hlookup_idx] at h
            | basic bt_idx =>
              cases bt with
              | tvec T =>
                cases bt_idx with
                | u64 =>
                  simp only [hlookup_src, hlookup_idx] at h
                  split at h
                  · rename_i hcond
                    have hfresh : notIn env.siteEnv a = true := by
                      cases h : notIn env.siteEnv a
                      · simp [h] at hcond
                      · rfl
                    have hcob : check_outbound_bool env.pathEnv s = true := by
                      cases h : check_outbound_bool env.pathEnv s
                      · simp [h] at hcond
                      · rfl
                    have hout : check_outbound env.pathEnv s (fun re => only_matches_empty (simplify re)) := by
                      intro s' hs'
                      simp only [check_outbound_bool, List.all_eq_true] at hcob
                      exact hcob s' hs'
                    let rf := nextFreshRefInEnv env
                    apply typecheck_stmt.let_bind_vecMutBorrow (T := T) (s := s) (rf := rf)
                    · exact hlookup_src
                    · exact hlookup_idx
                    · exact hfresh
                    · exact hout
                    · exact nextFreshRefInEnv_fresh_prop env
                    · have hrf_not_root : rf ≠ Aref.root := nextFreshRefInEnv_not_root env
                      have hpe' := update_with_extension_wellformed rf s [.vecElem] env.pathEnv hwf.pathEnv_wf hrf_not_root
                      have hτ : match (MoveType.ref T rf .siteBorrowMut) with | .ref _ r _ => r ≠ Aref.root | .basic _ => True :=
                        nextFreshRefInEnv_not_root env
                      have hsenv_del1 := SiteEnv.delete_refs_not_root env.siteEnv src hwf.siteEnv_wf
                      have hsenv_del2 := SiteEnv.delete_refs_not_root _ idx hsenv_del1
                      have hsenv_ins := SiteEnv.insert_refs_not_root _ a (.ref T rf .siteBorrowMut) hsenv_del2 hτ
                      have hwf' : TypeEnv.WellFormed
                        {env with siteEnv := insert (delete (delete env.siteEnv src) idx) a (.ref T rf .siteBorrowMut)
                                  pathEnv := update_with_extension rf s [.vecElem] env.pathEnv} :=
                        ⟨hpe', hsenv_ins, hwf.varEnv_wf⟩
                      exact ih_cont _ hwf' h
                  · simp at h
                | _ => simp [hlookup_src, hlookup_idx] at h
              | _ => simp [hlookup_src, hlookup_idx] at h

  -- Vector pop back
  | vecPopBack src =>
    simp only [check_stmt] at h
    cases hlookup : lookup env.siteEnv src with
    | none => simp [hlookup] at h
    | some τ =>
      cases τ with
      | basic _ => simp [hlookup] at h
      | ref bt r isBor =>
        cases isBor with
        | siteBorrowImm => simp [hlookup] at h
        | siteBorrowMut =>
          cases bt with
          | tvec T =>
            simp only [hlookup] at h
            split at h
            · rename_i hcond
              simp only [Bool.and_eq_true] at hcond
              obtain ⟨hfresh, hcob⟩ := hcond
              have hout : check_outbound env.pathEnv r (fun re => only_matches_empty (simplify re)) := by
                intro s' hs'
                simp only [check_outbound_bool, List.all_eq_true] at hcob
                exact hcob s' hs'
              have hr_not_root : r ≠ Aref.root := hwf.siteEnv_wf src (.ref (.tvec T) r .siteBorrowMut) hlookup
              have hpe' := garbage_collect_wellformed env.pathEnv r hwf.pathEnv_wf hr_not_root
              have hsenv_del := SiteEnv.delete_refs_not_root env.siteEnv src hwf.siteEnv_wf
              have hsenv_ins := SiteEnv.insert_refs_not_root _ a (.basic T) hsenv_del trivial
              have hwf' : TypeEnv.WellFormed
                {env with siteEnv := insert (delete env.siteEnv src) a (.basic T)
                          pathEnv := garbage_collect env.pathEnv r} :=
                ⟨hpe', hsenv_ins, hwf.varEnv_wf⟩
              apply typecheck_stmt.let_bind_vecPopBack (T := T) (r := r)
              · exact hlookup
              · exact hout
              · exact hfresh
              · exact ih_cont _ hwf' h
            · simp at h
          | _ => simp [hlookup] at h

/- ---------------------------------------------------- -/
/-       Substitution soundness helpers                  -/
/- ---------------------------------------------------- -/

/-- Helper: the foldl step function used in computeRefSubst -/
private def refSubstStep (a : Option (List (Aref × Aref))) (pair : Aref × Aref) :
    Option (List (Aref × Aref)) :=
  match a with
  | none => none
  | some pairs =>
    let (r1, r2) := pair
    match pairs.lookup r1 with
    | some r2' => if r2 == r2' then some pairs else none
    | none =>
      if pairs.any (fun (_, t) => t == r2) then none
      else some (pair :: pairs)

/-- foldl of refSubstStep starting from none always gives none -/
private lemma refSubstStep_foldl_none (input : List (Aref × Aref)) :
    input.foldl refSubstStep none = none := by
  induction input with
  | nil => rfl
  | cons _ _ ih => simp only [List.foldl_cons, refSubstStep]; exact ih

/-- The foldl in computeRefSubst preserves the property that all keys are refids,
    given that the input pairs all have refid keys. -/
private lemma computeRefSubst_foldl_keys_refid
    (input : List (Aref × Aref))
    (hinput : ∀ k v, (k, v) ∈ input → ∃ n, k = .refid n)
    (acc : List (Aref × Aref))
    (hacc : ∀ k v, (k, v) ∈ acc → ∃ n, k = .refid n)
    (result : List (Aref × Aref))
    (hresult : input.foldl refSubstStep (some acc) = some result) :
    ∀ k v, (k, v) ∈ result → ∃ n, k = .refid n := by
  induction input generalizing acc with
  | nil =>
    simp only [List.foldl_nil] at hresult
    injection hresult with hresult
    rw [← hresult]; exact hacc
  | cons pair rest ih =>
    simp only [List.foldl_cons] at hresult
    obtain ⟨r1, r2⟩ := pair
    simp only [refSubstStep] at hresult
    have hinput_rest : ∀ k v, (k, v) ∈ rest → ∃ n, k = .refid n :=
      fun k v hm => hinput k v (List.mem_cons_of_mem _ hm)
    -- Case split on List.lookup r1 acc
    cases hlk : List.lookup r1 acc with
    | none =>
      simp only [hlk] at hresult
      -- New key: check injectivity condition
      cases hinj : (acc.any fun x => x.2 == r2) with
      | false =>
        simp only [hinj, Bool.false_eq_true, ite_false] at hresult
        -- pair :: acc case
        have hacc' : ∀ k v, (k, v) ∈ (r1, r2) :: acc → ∃ n, k = .refid n := by
          intro k v hm
          cases List.mem_cons.mp hm with
          | inl heq =>
            have hk : k = r1 := (Prod.mk.inj heq).1
            subst hk
            exact hinput k r2 (List.mem_cons.mpr (Or.inl rfl))
          | inr htail => exact hacc k v htail
        exact ih hinput_rest ((r1, r2) :: acc) hacc' hresult
      | true =>
        simp only [hinj, ite_true] at hresult
        -- foldl starting from none — impossible
        rw [refSubstStep_foldl_none] at hresult; simp at hresult
    | some r2' =>
      simp only [hlk] at hresult
      -- Existing key: check consistency
      by_cases hr2eq : r2 = r2'
      · simp only [beq_iff_eq, hr2eq, ite_true] at hresult
        exact ih hinput_rest acc hacc hresult
      · have hne_beq : (r2 == r2') = false := beq_false_of_ne hr2eq
        simp only [hne_beq, Bool.false_eq_true, ite_false] at hresult
        rw [refSubstStep_foldl_none] at hresult; simp at hresult

/-- All keys in the substitution computed by computeRefSubst are refids. -/
private lemma computeRefSubst_keys_refid (ve1 ve2 : VarEnv) (pairs : List (Aref × Aref))
    (h : computeRefSubst ve1 ve2 = some pairs) :
    ∀ k v, (k, v) ∈ pairs → ∃ n, k = .refid n := by
  simp only [computeRefSubst] at h
  -- The foldl lambda is definitionally equal to refSubstStep
  change (ve1.entries.filterMap _).foldl refSubstStep (some []) = some pairs at h
  apply computeRefSubst_foldl_keys_refid _ _ [] (fun _ _ hm => nomatch hm) _ h
  -- Show that filterMap only produces refid keys
  intro k v hm
  simp only [List.mem_filterMap] at hm
  obtain ⟨⟨x, isv, τ, ms⟩, _, hfm⟩ := hm
  simp only at hfm
  split at hfm <;> simp at hfm
  split at hfm <;> simp at hfm
  exact ⟨_, hfm.2.1.symm⟩

/-- The foldl in computeRefSubst preserves the property that all values are not root,
    given that the input pairs all have non-root values. -/
private lemma computeRefSubst_foldl_values_not_root
    (input : List (Aref × Aref))
    (hinput : ∀ k v, (k, v) ∈ input → v ≠ .root)
    (acc : List (Aref × Aref))
    (hacc : ∀ k v, (k, v) ∈ acc → v ≠ .root)
    (result : List (Aref × Aref))
    (hresult : input.foldl refSubstStep (some acc) = some result) :
    ∀ k v, (k, v) ∈ result → v ≠ .root := by
  induction input generalizing acc with
  | nil =>
    simp only [List.foldl_nil] at hresult
    injection hresult with hresult
    rw [← hresult]; exact hacc
  | cons pair rest ih =>
    simp only [List.foldl_cons] at hresult
    obtain ⟨r1, r2⟩ := pair
    simp only [refSubstStep] at hresult
    have hinput_rest : ∀ k v, (k, v) ∈ rest → v ≠ .root :=
      fun k v hm => hinput k v (List.mem_cons_of_mem _ hm)
    cases hlk : List.lookup r1 acc with
    | none =>
      simp only [hlk] at hresult
      cases hinj : (acc.any fun x => x.2 == r2) with
      | false =>
        simp only [hinj, Bool.false_eq_true, ite_false] at hresult
        have hacc' : ∀ k v, (k, v) ∈ (r1, r2) :: acc → v ≠ .root := by
          intro k v hm
          cases List.mem_cons.mp hm with
          | inl heq =>
            rw [(Prod.mk.inj heq).2]
            exact hinput r1 r2 (List.mem_cons.mpr (Or.inl rfl))
          | inr htail => exact hacc k v htail
        exact ih hinput_rest ((r1, r2) :: acc) hacc' hresult
      | true =>
        simp only [hinj, ite_true] at hresult
        rw [refSubstStep_foldl_none] at hresult; simp at hresult
    | some r2' =>
      simp only [hlk] at hresult
      by_cases hr2eq : r2 = r2'
      · simp only [beq_iff_eq, hr2eq, ite_true] at hresult
        exact ih hinput_rest acc hacc hresult
      · have hne_beq : (r2 == r2') = false := beq_false_of_ne hr2eq
        simp only [hne_beq, Bool.false_eq_true, ite_false] at hresult
        rw [refSubstStep_foldl_none] at hresult; simp at hresult

/-- All values in the substitution computed by computeRefSubst are not root,
    given that the source VarEnv has no root refs. -/
private lemma computeRefSubst_values_not_root (ve1 ve2 : VarEnv) (pairs : List (Aref × Aref))
    (h : computeRefSubst ve1 ve2 = some pairs)
    (hno_root : VarEnv.RefsNotRoot ve2) :
    ∀ k v, (k, v) ∈ pairs → v ≠ .root := by
  simp only [computeRefSubst] at h
  change (ve1.entries.filterMap _).foldl refSubstStep (some []) = some pairs at h
  apply computeRefSubst_foldl_values_not_root _ _ [] (fun _ _ hm => nomatch hm) _ h
  -- Show that filterMap only produces non-root values
  intro k v hm
  simp only [List.mem_filterMap] at hm
  obtain ⟨⟨x, ⟨isv, τ, ms⟩⟩, _, hfm⟩ := hm
  -- Manual case analysis on isv and τ (the first match in the filterMap)
  cases isv with
  | invalidVar => simp at hfm
  | validVar =>
    cases τ with
    | basic _ => simp at hfm
    | ref bt ar bk =>
      cases ar with
      | root => simp at hfm
      | paramRef _ => simp at hfm
      | refid n =>
        -- Now: .validVar, .ref bt (.refid n) bk
        -- hfm is about: match lookup ve2 x with | some (.validVar, .ref _ r2 _, _) => ...
        simp only at hfm
        cases hlookup_ve2 : lookup ve2 x with
        | none => simp [hlookup_ve2] at hfm
        | some val =>
          rw [hlookup_ve2] at hfm
          obtain ⟨isv2, τ2, ms2⟩ := val
          cases isv2 with
          | invalidVar => simp at hfm
          | validVar =>
            cases τ2 with
            | basic _ => simp at hfm
            | ref bt2 r2 bk2 =>
              simp at hfm
              obtain ⟨_, _, hv⟩ := hfm
              subst hv
              exact hno_root x (.validVar, .ref bt2 r2 bk2, ms2) hlookup_ve2

/-- All keys in the extended σ produced by findRefExtension are refids.
    Follows from: input σ has refid keys + the `.refid _` match guard in findRefExtension.
    Every pair added by findRefExtension has a `.refid n` key (from the match guard),
    and all original pairs are preserved. -/
private lemma findRefExtension_keys_refid
    {σ σ' : List (Aref × Aref)}
    {unmapped unmatched refsL : List Aref}
    {envL env : TypeEnv}
    (hσ : ∀ k v, (k, v) ∈ σ → ∃ n, k = .refid n)
    (h : findRefExtension σ unmapped unmatched refsL envL env = some σ') :
    ∀ k v, (k, v) ∈ σ' → ∃ n, k = .refid n := by
  induction unmapped generalizing σ unmatched with
  | nil =>
    simp only [findRefExtension] at h
    split at h <;> simp at h
    subst h; exact hσ
  | cons u us ih =>
    simp only [findRefExtension] at h
    split at h
    · rename_i n -- u = .refid n
      obtain ⟨a, _, ha_eq⟩ := List.exists_of_findSome?_eq_some h
      cases a with
      | root => simp at ha_eq
      | paramRef v =>
        dsimp only at ha_eq
        split at ha_eq
        · simp at ha_eq
        · exact ih (fun k w hkw => by
            simp only [List.mem_cons, Prod.mk.injEq] at hkw
            rcases hkw with ⟨rfl, _⟩ | hm
            · exact ⟨n, rfl⟩
            · exact hσ k w hm) ha_eq
      | refid m =>
        dsimp only at ha_eq
        split at ha_eq
        · simp at ha_eq
        · exact ih (fun k w hkw => by
            simp only [List.mem_cons, Prod.mk.injEq] at hkw
            rcases hkw with ⟨rfl, _⟩ | hm
            · exact ⟨n, rfl⟩
            · exact hσ k w hm) ha_eq
    · simp at h -- non-refid case, contradiction

/-- All values in the extended σ produced by findRefExtension are not root.
    Follows from: input σ has non-root values + the `.root => none` guard in findRefExtension.
    Every pair added by findRefExtension has a non-root value (from the match guard),
    and all original pairs are preserved. -/
private lemma findRefExtension_values_not_root
    {σ σ' : List (Aref × Aref)}
    {unmapped unmatched refsL : List Aref}
    {envL env : TypeEnv}
    (hσ : ∀ k v, (k, v) ∈ σ → v ≠ .root)
    (h : findRefExtension σ unmapped unmatched refsL envL env = some σ') :
    ∀ k v, (k, v) ∈ σ' → v ≠ .root := by
  induction unmapped generalizing σ unmatched with
  | nil =>
    simp only [findRefExtension] at h
    split at h <;> simp at h
    subst h; exact hσ
  | cons u us ih =>
    simp only [findRefExtension] at h
    split at h
    · rename_i n -- u = .refid n
      obtain ⟨a, _, ha_eq⟩ := List.exists_of_findSome?_eq_some h
      cases a with
      | root => simp at ha_eq
      | paramRef v =>
        dsimp only at ha_eq
        split at ha_eq
        · simp at ha_eq
        · exact ih (fun k w hkw => by
            simp only [List.mem_cons, Prod.mk.injEq] at hkw
            rcases hkw with ⟨_, rfl⟩ | hm
            · exact nofun
            · exact hσ k w hm) ha_eq
      | refid m =>
        dsimp only at ha_eq
        split at ha_eq
        · simp at ha_eq
        · exact ih (fun k w hkw => by
            simp only [List.mem_cons, Prod.mk.injEq] at hkw
            rcases hkw with ⟨_, rfl⟩ | hm
            · exact nofun
            · exact hσ k w hm) ha_eq
    · simp at h -- non-refid case, contradiction

/-- All keys in σ from extendRefSubst are refids. -/
private lemma extendRefSubst_keys_refid
    {σ_var σ : List (Aref × Aref)}
    {refsL refsE : List Aref}
    {envL env : TypeEnv}
    (hσ_var : ∀ k v, (k, v) ∈ σ_var → ∃ n, k = .refid n)
    (h : extendRefSubst σ_var refsL refsE envL env = some σ) :
    ∀ k v, (k, v) ∈ σ → ∃ n, k = .refid n := by
  simp only [extendRefSubst] at h
  split at h
  · simp at h -- length mismatch
  · split at h
    · -- no extension needed: σ = σ_var
      simp at h; subst h; exact hσ_var
    · exact findRefExtension_keys_refid hσ_var h

/-- All values in σ from extendRefSubst are not root. -/
private lemma extendRefSubst_values_not_root
    {σ_var σ : List (Aref × Aref)}
    {refsL refsE : List Aref}
    {envL env : TypeEnv}
    (hσ_var : ∀ k v, (k, v) ∈ σ_var → v ≠ .root)
    (h : extendRefSubst σ_var refsL refsE envL env = some σ) :
    ∀ k v, (k, v) ∈ σ → v ≠ .root := by
  simp only [extendRefSubst] at h
  split at h
  · simp at h
  · split at h
    · simp at h; subst h; exact hσ_var
    · exact findRefExtension_values_not_root hσ_var h

/-- Helper: List.lookup returning some implies the pair is in the list -/
private lemma List_lookup_mem {α β : Type} [BEq α] [LawfulBEq α]
    (l : List (α × β)) (k : α) (v : β)
    (h : l.lookup k = some v) : (k, v) ∈ l := by
  induction l with
  | nil => simp [List.lookup] at h
  | cons p rest ih =>
    obtain ⟨k', v'⟩ := p
    simp only [List.lookup] at h
    split at h
    · rename_i hk
      rw [beq_iff_eq] at hk; subst hk
      injection h with h; subst h
      exact .head _
    · exact List.mem_cons_of_mem _ (ih h)

/-- applySubstArefList is identity on arefs that are not refids,
    when the substitution comes from computeRefSubst. -/
private lemma applySubstArefList_non_refid (pairs : List (Aref × Aref))
    (hkeys : ∀ k v, (k, v) ∈ pairs → ∃ n, k = .refid n)
    (r : Aref) (hr : ∀ n, r ≠ .refid n) :
    applySubstArefList pairs r = r := by
  simp only [applySubstArefList]
  -- Show pairs.lookup r = none since r is not a refid but all keys are
  have hlk : pairs.lookup r = none := by
    induction pairs with
    | nil => simp [List.lookup]
    | cons p rest ih =>
      obtain ⟨k, v⟩ := p
      have ⟨n, hk⟩ := hkeys k v (List.mem_cons.mpr (Or.inl rfl))
      subst hk
      have hne : (r == Aref.refid n) = false := by
        apply beq_false_of_ne
        exact hr n
      simp only [List.lookup, hne]
      exact ih (fun k v hm => hkeys k v (List.mem_cons.mpr (Or.inr hm)))
  simp [hlk]

/-- applySubstMoveTypeList agrees with applySubstMoveType using applySubstArefList. -/
private lemma applySubstMoveTypeList_eq (σ : List (Aref × Aref)) (τ : MoveType) :
    applySubstMoveTypeList σ τ = applySubstMoveType (applySubstArefList σ) τ := by
  cases τ with
  | basic bt => rfl
  | ref bt r bk => rfl

/-- Boolean base type compatibility implies the relational version. -/
private lemma MoveType_base_compatible_bool_sound (τ1 τ2 : MoveType) :
    MoveType.base_compatible_bool τ1 τ2 = true → MoveType.baseCompatible τ1 τ2 := by
  cases τ1 with
  | basic bt1 =>
    cases τ2 with
    | basic bt2 =>
      simp only [MoveType.base_compatible_bool, MoveType.baseCompatible]
      exact fun h => BasicMoveType.eq_of_beq bt1 bt2 h
    | ref _ _ _ => simp [MoveType.base_compatible_bool]
  | ref bt1 r1 bk1 =>
    cases τ2 with
    | basic _ => simp [MoveType.base_compatible_bool]
    | ref bt2 r2 bk2 =>
      simp only [MoveType.base_compatible_bool, Bool.and_eq_true, MoveType.baseCompatible]
      intro ⟨hbt, hbk⟩
      exact ⟨BasicMoveType.eq_of_beq bt1 bt2 hbt, beq_iff_eq.mp hbk⟩

/-- Soundness of varenv_subst_equiv_bool: if it returns true, VarEnvSubstEquiv holds. -/
private lemma varenv_subst_equiv_bool_sound (σ : List (Aref × Aref)) (ve1 ve2 : VarEnv) :
    varenv_subst_equiv_bool σ ve1 ve2 = true →
    VarEnvSubstEquiv (applySubstArefList σ) ve1 ve2 := by
  intro h
  simp only [varenv_subst_equiv_bool, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨hall1, hall2⟩ := h
  intro k
  -- Case split on lookup ve1 k
  cases hk1 : AssocMap.lookup ve1 k with
  | none =>
    -- If ve1 has no entry for k, ve2 must also have none
    cases hk2 : AssocMap.lookup ve2 k with
    | none => simp
    | some val2 =>
      -- ve2 has entry for k but ve1 doesn't — contradicts hall2
      exfalso
      obtain ⟨isv2, τ2, ms2⟩ := val2
      have hmem2 : (k, (isv2, τ2, ms2)) ∈ ve2.entries :=
        AssocMap.lookup_some ve2 k (isv2, τ2, ms2) hk2
      have := hall2 (k, (isv2, τ2, ms2)) hmem2
      simp only [Option.isSome] at this
      rw [hk1] at this
      simp at this
  | some val1 =>
    obtain ⟨isv1, τ1, ms1⟩ := val1
    -- ve1 has entry (isv1, τ1, ms1) for k
    cases hk2 : AssocMap.lookup ve2 k with
    | none =>
      -- ve1 has entry but ve2 doesn't — contradicts hall1
      exfalso
      have hmem1 : (k, (isv1, τ1, ms1)) ∈ ve1.entries :=
        AssocMap.lookup_some ve1 k (isv1, τ1, ms1) hk1
      have hcond := hall1 (k, (isv1, τ1, ms1)) hmem1
      simp only [hk2] at hcond
      simp at hcond
    | some val2 =>
      obtain ⟨isv2, τ2, ms2⟩ := val2
      -- Extract conditions from hall1
      have hmem1 : (k, (isv1, τ1, ms1)) ∈ ve1.entries :=
        AssocMap.lookup_some ve1 k (isv1, τ1, ms1) hk1
      have hcond := hall1 (k, (isv1, τ1, ms1)) hmem1
      simp only [hk2, Bool.and_eq_true] at hcond
      obtain ⟨hms_eq, htype_cond⟩ := hcond
      have hms : ms1 = ms2 := beq_iff_eq.mp hms_eq
      subst hms
      cases isv1 with
      | validVar =>
        cases isv2 with
        | validVar =>
          simp only at htype_cond
          have htype : applySubstMoveTypeList σ τ1 = τ2 := MoveType.eq_of_beq _ _ htype_cond
          rw [applySubstMoveTypeList_eq] at htype
          exact ⟨htype, rfl⟩
        | invalidVar =>
          simp at htype_cond
      | invalidVar =>
        cases isv2 with
        | invalidVar =>
          simp only at htype_cond
          exact ⟨MoveType_base_compatible_bool_sound τ1 τ2 htype_cond, rfl⟩
        | validVar =>
          -- (invalidVar, validVar) case: restricted to basic types
          cases τ1 with
          | basic bt1 =>
            cases τ2 with
            | basic bt2 =>
              simp only at htype_cond
              have hbt := BasicMoveType.eq_of_beq bt1 bt2 htype_cond
              exact ⟨⟨bt1, rfl, hbt ▸ rfl⟩, rfl⟩
            | ref => simp at htype_cond
          | ref => simp at htype_cond

/-- Soundness of siteenv_subst_equiv_bool: if it returns true, SiteEnvSubstEquiv holds. -/
private lemma siteenv_subst_equiv_bool_sound (σ : List (Aref × Aref)) (se1 se2 : SiteEnv) :
    siteenv_subst_equiv_bool σ se1 se2 = true →
    SiteEnvSubstEquiv (applySubstArefList σ) se1 se2 := by
  intro h
  simp only [siteenv_subst_equiv_bool, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨hfwd, hbwd⟩ := h
  unfold SiteEnvSubstEquiv
  intro k
  cases hk1 : AssocMap.lookup se1 k with
  | none =>
    cases hk2 : AssocMap.lookup se2 k with
    | none => simp
    | some τ2 =>
      have hmem2 : (k, τ2) ∈ se2.entries := AssocMap.lookup_some se2 k τ2 hk2
      have habs := hbwd (k, τ2) hmem2
      simp only [hk1, Option.isSome] at habs
      exact absurd habs (by decide)
  | some τ1 =>
    have hmem1 : (k, τ1) ∈ se1.entries := AssocMap.lookup_some se1 k τ1 hk1
    have hcond := hfwd (k, τ1) hmem1
    simp only at hcond
    cases hk2 : AssocMap.lookup se2 k with
    | none =>
      simp only [hk2] at hcond
      exact absurd hcond (by decide)
    | some τ2 =>
      simp only [hk2] at hcond
      simp
      rw [applySubstMoveTypeList_eq] at hcond
      exact MoveType.eq_of_beq _ _ hcond

/-- Helper: two nodup lists of the same length where one is a subset of the other are permutations. -/
private lemma perm_of_nodup_nodup_subset_length_eq [DecidableEq α] (l₁ l₂ : List α)
    (hnd₁ : l₁.Nodup) (hnd₂ : l₂.Nodup)
    (hlen : l₁.length = l₂.length)
    (hsub : ∀ x ∈ l₁, x ∈ l₂) : l₁.Perm l₂ := by
  induction l₁ generalizing l₂ with
  | nil =>
    cases l₂ with
    | nil => exact List.Perm.nil
    | cons _ _ => simp at hlen
  | cons a t ih =>
    have ha₂ : a ∈ l₂ := hsub a List.mem_cons_self
    -- l₂ can be split as l₂_pre ++ a :: l₂_suf
    obtain ⟨l₂_pre, l₂_suf, rfl⟩ := List.append_of_mem ha₂
    -- (l₂_pre ++ a :: l₂_suf) ~ (a :: (l₂_pre ++ l₂_suf))
    have hperm_mid : (l₂_pre ++ a :: l₂_suf).Perm (a :: (l₂_pre ++ l₂_suf)) :=
      List.perm_middle
    -- Suffices to show: (a :: t) ~ (a :: (l₂_pre ++ l₂_suf))
    apply List.Perm.trans _ hperm_mid.symm
    apply List.Perm.cons
    -- Now show: t ~ l₂_pre ++ l₂_suf
    have hnd_a : a ∉ t := (List.nodup_cons.mp hnd₁).1
    have hnd_t : t.Nodup := (List.nodup_cons.mp hnd₁).2
    have hnd_mid : (a :: (l₂_pre ++ l₂_suf)).Nodup := hperm_mid.nodup_iff.mp hnd₂
    have hnd_rest : (l₂_pre ++ l₂_suf).Nodup := (List.nodup_cons.mp hnd_mid).2
    apply ih (l₂_pre ++ l₂_suf) hnd_t hnd_rest
    · simp [List.length_append] at hlen ⊢; omega
    · intro x hx
      have hx₂ := hsub x (List.mem_cons_of_mem a hx)
      have hx_ne_a : x ≠ a := fun heq => hnd_a (heq ▸ hx)
      -- x ∈ l₂_pre ++ a :: l₂_suf and x ≠ a, so x ∈ l₂_pre ++ l₂_suf
      simp [List.mem_append, List.mem_cons] at hx₂ ⊢
      rcases hx₂ with h | rfl | h
      · left; exact h
      · exact absurd rfl hx_ne_a
      · right; exact h

/-- Soundness of subsumes_bool: if it returns true, the semantic subsumption holds.
    Requires that env.varEnv has no root refs (always satisfied by TypeEnv.WellFormed). -/
theorem subsumes_bool_implies_subsumes (envL env : TypeEnv)
    (hno_root : VarEnv.RefsNotRoot env.varEnv) :
    TypeEnv.subsumes_bool envL env = true → TypeEnv.subsumes envL env := by
  intro h
  unfold TypeEnv.subsumes_bool at h
  -- Case split on computeRefSubst result
  split at h
  · simp at h  -- none case: contradiction
  · rename_i σ_var heq_subst
    -- Case split on extendRefSubst result
    split at h
    · simp at h  -- none case: contradiction
    · rename_i pairs heq_ext
      -- The && chain structure is: se && ve && refs_combined && nodup && paths && enum
      -- Extract each conjunct using band_left/band_right
      have henum_raw := band_right h
      have h := band_left h
      have hpaths_raw := band_right h
      have h := band_left h
      have hnodup_raw := band_right h
      have h := band_left h
      have hrefs_combined_raw := band_right h
      have h := band_left h
      have hve := band_right h
      have hse := band_left h
      -- Decompose the refs check sub-chain: (len && mapped_nd && containment)
      have hcontains_raw := band_right hrefs_combined_raw
      have hrefs_combined_left := band_left hrefs_combined_raw
      have hmapped_nd_raw := band_right hrefs_combined_left
      have hlen_raw := band_left hrefs_combined_left
      simp only [List.all_eq_true] at hpaths_raw
      -- Derive key properties of the extended σ
      have hkeys_var := computeRefSubst_keys_refid envL.varEnv env.varEnv σ_var heq_subst
      have hkeys := extendRefSubst_keys_refid hkeys_var heq_ext
      have hvals_var := computeRefSubst_values_not_root envL.varEnv env.varEnv σ_var heq_subst hno_root
      have hvals := extendRefSubst_values_not_root hvals_var heq_ext
      -- Define σ as the function version of the substitution
      let σ : Aref → Aref := fun r => applySubstArefList pairs r
      -- Extract the perm-related facts
      have hlen : (envL.pathEnv.refs.map σ).length = env.pathEnv.refs.length :=
        beq_iff_eq.mp hlen_raw
      have hnodup_len : env.pathEnv.refs.length = env.pathEnv.refs.eraseDups.length :=
        (beq_iff_eq.mp hnodup_raw).symm
      have hnd : env.pathEnv.refs.Nodup :=
        List.nodup_of_length_eraseDups env.pathEnv.refs hnodup_len
      have hmapped_nd_len : (envL.pathEnv.refs.map σ).length =
          (envL.pathEnv.refs.map σ).eraseDups.length :=
        (beq_iff_eq.mp hmapped_nd_raw).symm
      have hnd_map : (envL.pathEnv.refs.map σ).Nodup :=
        List.nodup_of_length_eraseDups _ hmapped_nd_len
      have hcontains : ∀ r ∈ envL.pathEnv.refs.map σ, r ∈ env.pathEnv.refs := by
        simp only [List.all_eq_true, List.contains_eq_any_beq, List.any_eq_true,
                   beq_iff_eq] at hcontains_raw
        intro r hr
        obtain ⟨r', hr'_mem, rfl⟩ := hcontains_raw r hr
        exact hr'_mem
      -- Derive Perm
      have hrefs_perm : (envL.pathEnv.refs.map σ).Perm env.pathEnv.refs :=
        perm_of_nodup_nodup_subset_length_eq _ _ hnd_map hnd hlen hcontains
      refine ⟨σ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · -- σ is identity on non-refid arefs
        intro r hr
        exact applySubstArefList_non_refid pairs hkeys r hr
      · -- VarEnvSubstEquiv σ envL.varEnv env.varEnv
        exact varenv_subst_equiv_bool_sound pairs envL.varEnv env.varEnv hve
      · -- SiteEnvSubstEquiv σ envL.siteEnv env.siteEnv
        exact siteenv_subst_equiv_bool_sound pairs envL.siteEnv env.siteEnv hse
      · -- (envL.pathEnv.refs.map σ).Perm env.pathEnv.refs
        exact hrefs_perm
      · -- σ is injective on envL.pathEnv.refs
        intro u v hu hv huv
        exact List.inj_on_of_nodup_map hnd_map u hu v hv huv
      · -- σ doesn't create roots: applySubstArefList never maps non-root to root
        intro r hr
        simp only [σ]
        cases r with
        | root => exact absurd rfl hr
        | paramRef v =>
          have := applySubstArefList_non_refid pairs hkeys (.paramRef v) (fun n h => by cases h)
          rw [this]; intro h; cases h
        | refid n =>
          simp only [applySubstArefList]
          cases hlook : pairs.lookup (.refid n) with
          | none => intro h; cases h  -- identity: .refid n ≠ .root
          | some r' =>
            exact hvals (.refid n) r' (List_lookup_mem pairs (.refid n) r' hlook)
      · -- Path inclusion: env ⊆ envL after σ
        intro u v hu hv path hinterp
        have hu' := hpaths_raw u hu
        have huv := hu' v hv
        exact regexSubsumedBy_sound _ _ huv path hinterp
      · -- EnumEnv equivalence
        exact lookup_equiv_bool_sound _ _ henum_raw

/- ---------------------------------------------------- -/
/-       Statement type checking soundness               -/
/- ---------------------------------------------------- -/

-- generateFreshRefs produces refs that are all fresh in env
private lemma generateFreshRefs_fresh (env : TypeEnv) (rets : List ParamType) :
    all_refs_fresh_in_env env (generateFreshRefs env rets) := by
  unfold all_refs_fresh_in_env generateFreshRefs
  intro r hr
  simp only [List.mem_map, List.mem_range] at hr
  obtain ⟨i, _, rfl⟩ := hr
  exact freshRefInEnvBool_implies_freshRefInEnv _ env (refid_ge_start_fresh env _ (Nat.le_add_right _ _))

-- generateFreshRefs produces a list with no duplicates
private lemma generateFreshRefs_nodup (env : TypeEnv) (rets : List ParamType) :
    List.Nodup (generateFreshRefs env rets) := by
  unfold generateFreshRefs
  rw [List.nodup_iff_pairwise_ne, List.pairwise_map]
  exact List.nodup_range.imp fun h => by simp only [Ne, Aref.refid.injEq]; omega

-- generateFreshRefs produces only .refid refs (not root)
private lemma generateFreshRefs_not_root (env : TypeEnv) (rets : List ParamType) :
    ∀ r ∈ generateFreshRefs env rets, r ≠ Aref.root := by
  unfold generateFreshRefs
  intro r hr
  simp only [List.mem_map, List.mem_range] at hr
  obtain ⟨_, _, rfl⟩ := hr
  exact Aref.noConfusion

-- generateFreshRefs produces only .refid refs (not paramRef)
private lemma generateFreshRefs_not_paramRef (env : TypeEnv) (rets : List ParamType) :
    ∀ r ∈ generateFreshRefs env rets, ∀ v, r ≠ Aref.paramRef v := by
  unfold generateFreshRefs
  intro r hr v
  simp only [List.mem_map, List.mem_range] at hr
  obtain ⟨_, _, rfl⟩ := hr
  exact Aref.noConfusion

/-- The foldlM in the ref variant unpack case preserves TypeEnv.WellFormed.
    Each step inserts a fresh ref site and extends pathEnv, both preserving WellFormed. -/
private lemma ref_unpack_foldlM_wellformed
    (fields : List (Field × Site))
    (fentries : AssocMap Field BasicMoveType)
    (r : Aref) (bk : BorrowingKind) (envInit env' : TypeEnv)
    (qualify : Field → Field)
    (hwf : TypeEnv.WellFormed envInit)
    (hfold : fields.foldlM (fun env_acc (f, site) =>
      match lookup fentries f with
      | some bt =>
        if notIn env_acc.siteEnv site then
          let rf := nextFreshRefInEnv env_acc
          some {env_acc with
            siteEnv := insert env_acc.siteEnv site (.ref bt rf bk)
            pathEnv := update_with_extension rf r [.field (qualify f)] env_acc.pathEnv}
        else none
      | none => none
    ) envInit = some env') :
    TypeEnv.WellFormed env' := by
  induction fields generalizing envInit with
  | nil => simp [List.foldlM] at hfold; subst hfold; exact hwf
  | cons hd tl ih =>
    simp only [List.foldlM] at hfold
    obtain ⟨f, site⟩ := hd
    cases hlf : lookup fentries f with
    | none => simp [hlf] at hfold
    | some bt =>
      simp only [hlf] at hfold
      by_cases hnotin : notIn envInit.siteEnv site
      · simp only [hnotin, ↓reduceIte] at hfold
        apply ih _ _ hfold
        exact ⟨
          update_with_extension_wellformed _ r _ _ hwf.pathEnv_wf
            (nextFreshRefInEnv_not_root envInit),
          SiteEnv.insert_refs_not_root _ _ _ hwf.siteEnv_wf
            (nextFreshRefInEnv_not_root envInit),
          hwf.varEnv_wf⟩
      · simp [hnotin] at hfold

/-- Soundness: If the algorithmic check succeeds, the relational judgment holds.
    This requires the type environment to be well-formed (pathEnv and siteEnv invariants).
-/
-- TODO: Complete soundness proof after enum architectural changes are stable
theorem check_stmt_sound (lenv : LabelEnv) (env : TypeEnv) (s : Stmt) (retTypes : List ParamType)
    (hwf : TypeEnv.WellFormed env) :
    (check_stmt lenv env s retTypes).isSome = true → typecheck_stmt lenv env s retTypes := by
  -- Use induction on the statement structure to get IH for recursive cases
  induction s generalizing env with
  | skip => intro _; exact typecheck_stmt.skip lenv env retTypes

  | jump L =>
    intro h
    simp only [check_stmt] at h
    cases hlookup : lookup lenv L with
    | none => simp [hlookup] at h
    | some envL =>
      simp only [hlookup] at h
      split at h
      · apply typecheck_stmt.jump lenv env L envL retTypes hlookup
        exact subsumes_bool_implies_subsumes envL env hwf.varEnv_wf (by assumption)
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
                apply typecheck_stmt.branch lenv env a L1 L2 envL1 envL2 retTypes ha hl1 hl2
                · exact subsumes_bool_implies_subsumes envL1 _ hwf.varEnv_wf hcond.1
                · exact subsumes_bool_implies_subsumes envL2 _ hwf.varEnv_wf hcond.2
              · simp at h
        | _ => simp at h

  | ret as =>
    intro h
    simp only [check_stmt] at h
    -- The check_stmt for ret tests four conditions via &&
    split at h
    · rename_i hcond
      have h1 : types_conform_bool env.siteEnv as retTypes = true := by
        simp only [Bool.and_eq_true] at hcond; exact hcond.1.1.1
      have h2 : ret_refs_not_from_locals_bool env as = true := by
        simp only [Bool.and_eq_true] at hcond; exact hcond.1.1.2
      have h3 : ret_mutable_writable_bool env as = true := by
        simp only [Bool.and_eq_true] at hcond; exact hcond.1.2
      have h4 : ret_mutable_no_aliases_bool env as = true := by
        simp only [Bool.and_eq_true] at hcond; exact hcond.2
      exact typecheck_stmt.ret lenv env as retTypes
        (types_conform_bool_sound env.siteEnv as retTypes h1)
        (ret_refs_not_from_locals_bool_sound env as h2)
        (ret_mutable_writable_bool_sound env as h3)
        (ret_mutable_no_aliases_bool_sound env as h4)
    · simp at h

  | abort a =>
    intro h
    simp only [check_stmt] at h
    cases hlookup : lookup env.siteEnv a with
    | none => simp [hlookup] at h
    | some τ => exact typecheck_stmt.abort lenv env a τ retTypes hlookup

  | release a cont ih_cont =>
    intro h
    simp only [check_stmt] at h
    cases hlookup : lookup env.siteEnv a with
    | none => simp [hlookup] at h
    | some τ =>
      cases τ with
      | basic bt =>
        simp only [hlookup] at h
        let env' : TypeEnv := {env with siteEnv := delete env.siteEnv a}
        have hsenv' := SiteEnv.delete_refs_not_root env.siteEnv a hwf.siteEnv_wf
        have hwf' : TypeEnv.WellFormed env' := ⟨hwf.pathEnv_wf, hsenv', hwf.varEnv_wf⟩
        apply typecheck_stmt.release_basic lenv env a bt cont retTypes hlookup
        exact ih_cont env' hwf' h
      | ref bt r isBor =>
        simp only [hlookup] at h
        -- h : (check_stmt lenv env' cont retTypes).isSome = true
        -- where env' = {env with siteEnv := delete env.siteEnv a, pathEnv := delete_ref_node env.pathEnv r}
        let env' : TypeEnv := {env with siteEnv := delete env.siteEnv a,
                                         pathEnv := delete_ref_node env.pathEnv r}
        -- Use SiteEnv.RefsNotRoot invariant to prove r ≠ root
        have hr_not_root : r ≠ Aref.root := hwf.siteEnv_wf a (.ref bt r isBor) hlookup
        have hpe' := delete_ref_node_wellformed env.pathEnv r hwf.pathEnv_wf hr_not_root
        have hsenv' := SiteEnv.delete_refs_not_root env.siteEnv a hwf.siteEnv_wf
        have hwf' : TypeEnv.WellFormed env' := ⟨hpe', hsenv', hwf.varEnv_wf⟩
        apply typecheck_stmt.release lenv env a bt r isBor cont retTypes hlookup
        exact ih_cont env' hwf' h

  -- letBind case: use the check_letBind_sound helper lemma
  | letBind a e cont ih_cont =>
    intro h
    exact check_letBind_sound lenv env a e cont retTypes hwf ih_cont h

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
          cases hlookup_a : lookup env.siteEnv a with
          | none => simp [hlookup_a] at h
          | some mt_a =>
            cases mt_a with
            | basic τ' =>
              simp only [hlookup_a] at h
              split at h
              · rename_i hτ_beq
                split at h
                · rename_i hfresh_ax
                  let r := nextFreshRefInEnv env
                  let ax : Site := .site (env.siteEnv.entries.length)
                  have hτ_eq : τ = τ' := BasicMoveType.eq_of_beq _ _ hτ_beq
                  have ha_type : lookup env.siteEnv a = some (.basic τ) := by
                    rw [hτ_eq]; exact hlookup_a
                  apply typecheck_stmt.var_assign_valid (τ := τ) (ms := ms) (r := r) (ax := ax)
                  · simp only [beq_iff_eq] at hms
                    simp only [hms, LE.le, Mut.le]
                  · exact hlookup
                  · exact ha_type
                  · exact hfresh_ax
                  · exact nextFreshRefInEnv_fresh_prop env
                  · have hr_not_root : r ≠ Aref.root := nextFreshRefInEnv_not_root env
                    have hpe' := update_with_extension_wellformed r .root [.root_to_var x] _
                      (update_with_epsilon_wellformed r r env.pathEnv hwf.pathEnv_wf hr_not_root) hr_not_root
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
            | ref _ _ _ => simp [hlookup_a] at h
        · simp at h
      | (.validVar, .ref τ_old r_old bk_old, ms) =>
        simp only at h
        split at h
        · rename_i hms
          cases hlookup_a : lookup env.siteEnv a with
          | none => simp [hlookup_a] at h
          | some τ' =>
            simp only [hlookup_a] at h
            have hr_not_root : r_old ≠ Aref.root :=
              VarEnv.lookup_type_refs_not_root env.varEnv x .validVar (.ref τ_old r_old bk_old) ms hwf.varEnv_wf hlookup
            have hpe' := delete_ref_node_wellformed env.pathEnv r_old hwf.pathEnv_wf hr_not_root
            have hsenv' := SiteEnv.delete_refs_not_root env.siteEnv a hwf.siteEnv_wf
            have hτ'_notroot := hwf.siteEnv_wf a τ' hlookup_a
            have hvarenv' := VarEnv.update_refs_not_root env.varEnv x (.validVar, τ', ms) hwf.varEnv_wf hτ'_notroot
            let env' : TypeEnv := {env with
              varEnv := update env.varEnv x (.validVar, τ', ms)
              siteEnv := delete env.siteEnv a
              pathEnv := delete_ref_node env.pathEnv r_old}
            have hwf' : TypeEnv.WellFormed env' := ⟨hpe', hsenv', hvarenv'⟩
            apply typecheck_stmt.var_assign_valid_ref lenv env x a τ_old r_old bk_old τ' ms
            · simp only [beq_iff_eq] at hms; simp only [hms, LE.le, Mut.le]
            · exact hlookup
            · exact hlookup_a
            · exact ih_cont env' hwf' h
        · simp at h
      | (.invalidVar, τ, .mutable) =>
        simp only at h
        cases hlookup_a : lookup env.siteEnv a with
        | none => simp [hlookup_a] at h
        | some τ' =>
          simp only [hlookup_a] at h
          split at h
          · rename_i hcompat
            have hcompat' := MoveType.compatible_bool_sound τ τ' hcompat
            have hτ_notroot := VarEnv.lookup_type_refs_not_root env.varEnv x .invalidVar τ .mutable hwf.varEnv_wf hlookup
            have hτ'_notroot := MoveType.compatible_preserves_not_root τ τ' hτ_notroot hcompat'
            have hsenv' := SiteEnv.delete_refs_not_root env.siteEnv a hwf.siteEnv_wf
            have hvarenv' := VarEnv.update_refs_not_root env.varEnv x (.validVar, τ', .mutable) hwf.varEnv_wf hτ'_notroot
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
            apply typecheck_stmt.unpack lenv env fields b fentries cont retTypes hlookup
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

  | unpackVariant variantName fields b cont ih_cont =>
    intro h
    simp only [check_stmt] at h
    cases hlookup : lookup env.siteEnv b with
    | none => simp [hlookup] at h
    | some τ =>
      cases τ with
      | basic bt =>
        cases bt with
        | tenum ename =>
          simp only [hlookup] at h
          -- Owned unpack case: look up enum and variant from enumEnv
          cases hlookup_enum : lookup env.enumEnv ename with
          | none => simp [hlookup_enum] at h
          | some enumDef =>
            simp only [hlookup_enum] at h
            cases hlookup_var : lookup enumDef.variants variantName with
            | none => simp [hlookup_var] at h
            | some variantDef =>
              simp only [hlookup_var] at h
              let fentries := variantDef.fields
              split at h
              · rename_i hcond
                simp only [Bool.and_eq_true] at hcond
                obtain ⟨⟨hfresh, hdistinct⟩, hexist⟩ := hcond
                apply typecheck_stmt.unpackVariant_rule lenv env variantName fields b ename enumDef
                  variantDef cont retTypes hlookup hlookup_enum hlookup_var
                · -- freshness
                  intro f a hfa
                  simp only [check_unpack_fields_fresh, List.all_eq_true] at hfresh
                  exact hfresh (f, a) hfa
                · -- distinctness
                  exact check_fields_distinct_implies_sites_distinct fields hdistinct
                · -- fields exist in fentries
                  intro f a hfa
                  simp only [check_unpack_fields_exist, List.all_eq_true] at hexist
                  have hexist' := hexist (f, a) hfa
                  cases hlookupf : lookup variantDef.fields f with
                  | none => simp [hlookupf] at hexist'
                  | some bt' => exact ⟨bt', rfl⟩
                · -- recursive call
                  let env' := {env with siteEnv := addFieldSites variantDef.fields (delete env.siteEnv b) fields}
                  have hsenv' : SiteEnv.RefsNotRoot env'.siteEnv :=
                    addFieldSites_refs_not_root variantDef.fields _ fields
                      (SiteEnv.delete_refs_not_root env.siteEnv b hwf.siteEnv_wf)
                  have hwf' : TypeEnv.WellFormed env' := ⟨hwf.pathEnv_wf, hsenv', hwf.varEnv_wf⟩
                  exact ih_cont env' hwf' h
              · simp at h
        | _ => simp [hlookup] at h
      | ref bt r bk =>
        cases bt with
        | tenum ename =>
          simp only [hlookup] at h
          -- Ref unpack case: look up enum and variant from enumEnv
          cases hlookup_enum : lookup env.enumEnv ename with
          | none => simp [hlookup_enum] at h
          | some enumDef =>
            simp only [hlookup_enum] at h
            cases hlookup_var : lookup enumDef.variants variantName with
            | none => simp [hlookup_var] at h
            | some variantDef =>
              simp only [hlookup_var] at h
              split at h
              · rename_i hcond
                simp only [Bool.and_eq_true] at hcond
                obtain ⟨⟨hfresh, hdistinct⟩, hexist⟩ := hcond
                -- The foldlM creates the ref env
                split at h
                · rename_i env' hfold
                  have hfresh_prop : ∀ f a, (f, a) ∈ fields → AssocMap.notIn env.siteEnv a := by
                    intro f a hfa
                    simp only [check_unpack_fields_fresh, List.all_eq_true] at hfresh
                    exact hfresh (f, a) hfa
                  have hdist_prop := check_fields_distinct_implies_sites_distinct fields hdistinct
                  have hexist_prop : ∀ f a, (f, a) ∈ fields → ∃ bt, lookup variantDef.fields f = some bt := by
                    intro f a hfa
                    simp only [check_unpack_fields_exist, List.all_eq_true] at hexist
                    have hexist' := hexist (f, a) hfa
                    cases hlookupf : lookup variantDef.fields f with
                    | none => simp [hlookupf] at hexist'
                    | some bt' => exact ⟨bt', rfl⟩
                  -- Prove: env' = addRefFieldSites (foldlM succeeds = foldl)
                  have henv_eq : env' = addRefFieldSites r bk variantDef.fields fields {env with siteEnv := delete env.siteEnv b} (qualify := MoveLight.qualifyField variantName) := by
                    -- foldlM = some env' implies env' = foldl result
                    -- Because at each step, lookup variantDef.fields f succeeds (from hexist)
                    -- and notIn env_acc.siteEnv site holds (from hfresh + distinct + accum)
                    suffices h : ∀ (fs : List (Field × Site)) (envI envR : TypeEnv),
                      fs.foldlM (fun env_acc (f, site) =>
                        match lookup variantDef.fields f with
                        | some bt =>
                          if notIn env_acc.siteEnv site then
                            some {env_acc with
                              siteEnv := insert env_acc.siteEnv site (.ref bt (nextFreshRefInEnv env_acc) bk)
                              pathEnv := update_with_extension (nextFreshRefInEnv env_acc) r [.field (MoveLight.qualifyField variantName f)] env_acc.pathEnv}
                          else none
                        | none => none) envI = some envR →
                      envR = addRefFieldSites r bk variantDef.fields (MoveLight.qualifyField variantName) fs envI by
                      exact h fields _ _ hfold
                    intro fs
                    induction fs with
                    | nil =>
                      intro envI envR hfm
                      simp [List.foldlM] at hfm; subst hfm; rfl
                    | cons hd tl ih =>
                      intro envI envR hfm
                      obtain ⟨f, site⟩ := hd
                      simp only [List.foldlM, bind, Option.bind] at hfm
                      cases hlf : lookup variantDef.fields f with
                      | none => simp [hlf] at hfm
                      | some bt =>
                        simp only [hlf] at hfm
                        by_cases hnotin : notIn envI.siteEnv site
                        · simp only [hnotin, ↓reduceIte] at hfm
                          have ih_result := ih _ _ hfm
                          simp [addRefFieldSites, List.foldl, hlf]
                          exact ih_result
                        · simp [hnotin] at hfm
                  have hwf_init : TypeEnv.WellFormed {env with siteEnv := delete env.siteEnv b} :=
                    ⟨hwf.pathEnv_wf,
                     SiteEnv.delete_refs_not_root env.siteEnv b hwf.siteEnv_wf,
                     hwf.varEnv_wf⟩
                  have hwf' := ref_unpack_foldlM_wellformed fields variantDef.fields r bk _ env' (MoveLight.qualifyField variantName) hwf_init hfold
                  have hcont_typed := ih_cont env' hwf' h
                  apply typecheck_stmt.unpackVariant_ref_rule
                  · exact hlookup
                  · exact hlookup_enum
                  · exact hlookup_var
                  · exact hfresh_prop
                  · exact hdist_prop
                  · exact hexist_prop
                  · exact henv_eq ▸ hcont_typed
                · simp at h
              · simp at h
        | _ => simp [hlookup] at h

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
                apply typecheck_stmt.write_ref lenv env a b bt r cont retTypes hlookup_a hlookup_b hout
                exact ih_cont env' hwf' h
              · simp at h

  | call as fnName bs cont ih_cont =>
    intro h
    simp only [check_stmt] at h
    split at h
    · rename_i hfresh_cond
      simp only [Bool.and_eq_true] at hfresh_cond
      obtain ⟨hfresh_bool, hnodup_as_bool⟩ := hfresh_cond
      cases hlookup_fn : lookup env.funEnv fnName with
      | none => simp [hlookup_fn] at h
      | some sig =>
        obtain ⟨params, rets⟩ := sig
        simp only [hlookup_fn] at h
        split at h
        · rename_i hcond
          simp only [Bool.and_eq_true] at hcond
          obtain ⟨htc_bs, hiso⟩ := hcond
          -- Handle match on populate_call_outputs inside the hypothesis
          split at h
          · rename_i env' hpop
            have hfresh' := all_fresh_sites_bool_sound env as hfresh_bool
            have hnodup_as := List.nodup_of_length_eraseDups as
              (beq_iff_eq.mp hnodup_as_bool).symm
            have htc_bs' := types_conform_bool_sound env.siteEnv bs params htc_bs
            have hiso' := check_mutable_inputs_isolated_bool_sound env bs hiso
            have hfresh_refs := generateFreshRefs_fresh env rets
            have hnodup := generateFreshRefs_nodup env rets
            have hwf_env' := populate_call_outputs_wf env env' as rets (generateFreshRefs env rets)
              hwf (generateFreshRefs_not_root env rets) hpop
            have hwf' := call_connect_inputs_outputs_wf env' as bs hwf_env'
            apply typecheck_stmt.call lenv env fnName as bs params rets
              (generateFreshRefs env rets) env' cont retTypes
              hlookup_fn htc_bs' hfresh' hnodup_as hfresh_refs hnodup
              hpop hiso'
            let env'' := call_connect_inputs_outputs env' as bs
            have hwf_del : ({env'' with siteEnv := AssocMap.deleteAll env''.siteEnv bs}).WellFormed :=
              ⟨hwf'.pathEnv_wf, SiteEnv.deleteAll_refs_not_root _ _ hwf'.siteEnv_wf, hwf'.varEnv_wf⟩
            exact ih_cont _ hwf_del h
          · simp at h
        · simp at h
    · simp at h

  -- Vector unpack
  | vecUnpack T results src cont ih_cont =>
    intro h
    simp only [check_stmt] at h
    cases hlookup : lookup env.siteEnv src with
    | none => simp [hlookup] at h
    | some τ =>
      cases τ with
      | basic bt =>
        cases bt with
        | tvec T' =>
          simp only [hlookup] at h
          split at h
          · rename_i hcond
            simp only [Bool.and_eq_true] at hcond
            obtain ⟨⟨hbeq, hnodup_bool⟩, hall⟩ := hcond
            have hteq := BasicMoveType.eq_of_beq T T' hbeq
            subst hteq
            apply typecheck_stmt.vecUnpack_rule lenv env T results src cont retTypes hlookup
            · intro s hs
              simp only [List.all_eq_true] at hall
              exact hall s hs
            · exact List.nodup_of_length_eraseDups results (beq_iff_eq.mp hnodup_bool).symm
            · let env' := {env with siteEnv := addVecSites T (delete env.siteEnv src) results}
              have hsenv' : SiteEnv.RefsNotRoot env'.siteEnv :=
                addVecSites_refs_not_root T _ results
                  (SiteEnv.delete_refs_not_root env.siteEnv src hwf.siteEnv_wf)
              have hwf' : TypeEnv.WellFormed env' := ⟨hwf.pathEnv_wf, hsenv', hwf.varEnv_wf⟩
              exact ih_cont env' hwf' h
          · simp at h
        | _ => simp [hlookup] at h
      | ref _ _ _ => simp [hlookup] at h

  -- Vector push back
  | vecPushBack refSite val cont ih_cont =>
    intro h
    simp only [check_stmt] at h
    cases hlookup_ref : lookup env.siteEnv refSite with
    | none => simp [hlookup_ref] at h
    | some τ_ref =>
      cases hlookup_val : lookup env.siteEnv val with
      | none => simp [hlookup_ref, hlookup_val] at h
      | some τ_val =>
        cases τ_ref with
        | basic _ => simp [hlookup_ref, hlookup_val] at h
        | ref bt r isBor =>
          cases isBor with
          | siteBorrowImm => simp [hlookup_ref, hlookup_val] at h
          | siteBorrowMut =>
            cases τ_val with
            | ref _ _ _ => simp [hlookup_ref, hlookup_val] at h
            | basic bt_val =>
              cases bt with
              | tvec T =>
                simp only [hlookup_ref, hlookup_val] at h
                split at h
                · rename_i hcond
                  simp only [Bool.and_eq_true] at hcond
                  obtain ⟨hbeq, hcob⟩ := hcond
                  have hteq := BasicMoveType.eq_of_beq T bt_val hbeq
                  subst hteq
                  have hout : check_outbound env.pathEnv r (fun re => only_matches_empty (simplify re)) := by
                    intro s' hs'
                    simp only [check_outbound_bool, List.all_eq_true] at hcob
                    exact hcob s' hs'
                  have hr_not_root : r ≠ Aref.root := hwf.siteEnv_wf refSite (.ref (.tvec T) r .siteBorrowMut) hlookup_ref
                  have hpe' := garbage_collect_wellformed env.pathEnv r hwf.pathEnv_wf hr_not_root
                  have hsenv_del1 := SiteEnv.delete_refs_not_root env.siteEnv val hwf.siteEnv_wf
                  have hsenv_del2 := SiteEnv.delete_refs_not_root _ refSite hsenv_del1
                  let env' := {env with siteEnv := delete (delete env.siteEnv val) refSite
                                        pathEnv := garbage_collect env.pathEnv r}
                  have hwf' : TypeEnv.WellFormed env' := ⟨hpe', hsenv_del2, hwf.varEnv_wf⟩
                  apply typecheck_stmt.vecPushBack_rule lenv env refSite val T r cont retTypes
                    hlookup_ref hlookup_val hout
                  exact ih_cont env' hwf' h
                · simp at h
              | _ => simp [hlookup_ref, hlookup_val] at h

  -- Vector swap
  | vecSwap refSite idx1 idx2 cont ih_cont =>
    intro h
    simp only [check_stmt] at h
    cases hlookup_ref : lookup env.siteEnv refSite with
    | none => simp [hlookup_ref] at h
    | some τ_ref =>
      cases hlookup_idx1 : lookup env.siteEnv idx1 with
      | none => simp [hlookup_ref, hlookup_idx1] at h
      | some τ_idx1 =>
        cases hlookup_idx2 : lookup env.siteEnv idx2 with
        | none => simp [hlookup_ref, hlookup_idx1, hlookup_idx2] at h
        | some τ_idx2 =>
          cases τ_ref with
          | basic _ => simp [hlookup_ref, hlookup_idx1, hlookup_idx2] at h
          | ref bt r isBor =>
            cases isBor with
            | siteBorrowImm => simp [hlookup_ref, hlookup_idx1, hlookup_idx2] at h
            | siteBorrowMut =>
              cases τ_idx1 with
              | ref _ _ _ => simp [hlookup_ref, hlookup_idx1, hlookup_idx2] at h
              | basic bt_idx1 =>
                cases τ_idx2 with
                | ref _ _ _ => simp [hlookup_ref, hlookup_idx1, hlookup_idx2] at h
                | basic bt_idx2 =>
                  cases bt with
                  | tvec T =>
                    cases bt_idx1 with
                    | u64 =>
                      cases bt_idx2 with
                      | u64 =>
                        simp only [hlookup_ref, hlookup_idx1, hlookup_idx2] at h
                        split at h
                        · rename_i hcob
                          have hout : check_outbound env.pathEnv r (fun re => only_matches_empty (simplify re)) := by
                            intro s' hs'
                            simp only [check_outbound_bool, List.all_eq_true] at hcob
                            exact hcob s' hs'
                          have hr_not_root : r ≠ Aref.root := hwf.siteEnv_wf refSite (.ref (.tvec T) r .siteBorrowMut) hlookup_ref
                          have hpe' := garbage_collect_wellformed env.pathEnv r hwf.pathEnv_wf hr_not_root
                          have hsenv_del1 := SiteEnv.delete_refs_not_root env.siteEnv idx2 hwf.siteEnv_wf
                          have hsenv_del2 := SiteEnv.delete_refs_not_root _ idx1 hsenv_del1
                          have hsenv_del3 := SiteEnv.delete_refs_not_root _ refSite hsenv_del2
                          let env' := {env with siteEnv := delete (delete (delete env.siteEnv idx2) idx1) refSite
                                                pathEnv := garbage_collect env.pathEnv r}
                          have hwf' : TypeEnv.WellFormed env' := ⟨hpe', hsenv_del3, hwf.varEnv_wf⟩
                          apply typecheck_stmt.vecSwap_rule lenv env refSite idx1 idx2 T r cont retTypes
                            hlookup_ref hlookup_idx1 hlookup_idx2 hout
                          exact ih_cont env' hwf' h
                        · simp at h
                      | _ => simp [hlookup_ref, hlookup_idx1, hlookup_idx2] at h
                    | _ => simp [hlookup_ref, hlookup_idx1, hlookup_idx2] at h
                  | _ => simp [hlookup_ref, hlookup_idx1, hlookup_idx2] at h

  | variantSwitch src cases_list =>
    intro h
    simp only [check_stmt] at h
    cases hlookup : lookup env.siteEnv src with
    | none => simp [hlookup] at h
    | some τ =>
      cases τ with
      | basic _ => simp [hlookup] at h
      | ref bt r bk =>
        cases bt with
        | tenum ename =>
          simp only [hlookup] at h
          -- Look up enum definition from enumEnv
          cases hlookup_enum : lookup env.enumEnv ename with
          | none => simp [hlookup_enum] at h
          | some enumDef =>
            simp only [hlookup_enum] at h
            split at h
            · rename_i hcond
              simp only [Bool.and_eq_true] at hcond
              obtain ⟨hcoverage, hcases⟩ := hcond
              apply typecheck_stmt.variantSwitch_rule lenv env src cases_list ename enumDef r bk
                retTypes hlookup hlookup_enum
              · -- Coverage: all variants are covered
                intro vname hne
                simp only [List.all_eq_true] at hcoverage
                -- vname is a key in enumDef.variants, so (vname, _) ∈ enumDef.variants.entries
                have hsome := Option.ne_none_iff_isSome.mp hne
                obtain ⟨fentries, hfent⟩ := Option.isSome_iff_exists.mp hsome
                have hmem_entries := lookup_some enumDef.variants vname fentries hfent
                have hcheck := hcoverage (vname, fentries) hmem_entries
                simp only [List.any_eq_true, beq_iff_eq] at hcheck
                obtain ⟨⟨vname', label⟩, hmem_cases, heq⟩ := hcheck
                simp at heq; subst heq
                exact ⟨label, hmem_cases⟩
              · -- Each case has a valid envL with subsumption
                intro vname label hmem
                simp only [List.all_eq_true] at hcases
                have hentry := hcases (vname, label) hmem
                simp only at hentry
                cases hlabel : lookup lenv label with
                | none => simp [hlabel] at hentry
                | some envL =>
                  simp only [hlabel] at hentry
                  exact ⟨envL, rfl, subsumes_bool_implies_subsumes envL _ hwf.varEnv_wf hentry⟩
            · simp at h
        | _ => simp [hlookup] at h

/- ---------------------------------------------------- -/
/-       Function type checking soundness                -/
/- ---------------------------------------------------- -/

/-- Soundness: If the algorithmic check succeeds, the relational judgment holds.
    Requires that all environments in the label environment are well-formed. -/
theorem check_fun_sound (f : FunDef) (lenv : LabelEnv) (enumEnv : EnumEnv)
    (hlenv_wf : ∀ l env, lookup lenv l = some env → TypeEnv.WellFormed env) :
    check_fun f lenv enumEnv = true → typecheck_fun f lenv enumEnv := by
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
        pathEnv := init_fun_pathEnv f
        funEnv := AssocMap.empty
        enumEnv := enumEnv
      }
      apply typecheck_fun.fun_ok f lenv enumEnv initEnv
      · rfl
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
