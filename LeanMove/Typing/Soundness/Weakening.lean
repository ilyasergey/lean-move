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
import LeanMove.Typing.TypesUtils

/-!
# Weakening for typecheck_stmt

If a statement type-checks under environment `envL`, and `envL.subsumes env`,
then the statement also type-checks under `env`.

The key insight: `envL.subsumes env` means env has fewer/narrower paths than envL.
More paths = more restrictions (e.g., harder to pass `check_outbound`).
So if the program passes all checks under the more restrictive envL, it also
passes under the less restrictive env.

This lemma is used in preservation_jump and preservation_branch.
-/

namespace LeanMove.Typing.TypeSoundness

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Typing
open AssocMap
open Regex

-- ============================================================
-- Helper: notIn ↔ lookup bridge
-- ============================================================

/-- If lookup returns none, then notIn returns true -/
private lemma lookup_none_implies_notIn {K V : Type} [DecidableEq K] (m : AssocMap K V) (k : K) :
    lookup m k = none → notIn m k = true := by
  rcases m with ⟨entries⟩
  simp only [lookup, notIn]
  intro h
  suffices hsuff : entries.find? (fun p => p.1 == k) = none by simp [hsuff]
  induction entries with
  | nil => rfl
  | cons hd rest ih =>
    obtain ⟨k', v'⟩ := hd
    by_cases hk : k = k'
    · subst hk; simp [List.lookup] at h
    · have hkk' : (k == k') = false := beq_eq_false_iff_ne.mpr hk
      have hk'k : (k' == k) = false := beq_eq_false_iff_ne.mpr (Ne.symm hk)
      simp only [List.find?, hk'k]
      simp only [List.lookup, hkk'] at h
      exact ih h

-- ============================================================
-- Helper lemmas: applySubstMoveType
-- ============================================================

/-- applySubstMoveType distributes over composition -/
private lemma applySubstMoveType_comp (σ1 σ2 : Aref → Aref) (τ : MoveType) :
    applySubstMoveType (fun r => σ2 (σ1 r)) τ = applySubstMoveType σ2 (applySubstMoveType σ1 τ) := by
  cases τ with
  | basic _ => rfl
  | ref _ _ _ => rfl

/-- applySubstMoveType on basic types is identity -/
private lemma applySubstMoveType_basic (σ : Aref → Aref) (bt : BasicMoveType) :
    applySubstMoveType σ (.basic bt) = .basic bt := rfl

/-- MoveType.baseCompatible is reflexive for applySubstMoveType -/
private lemma baseCompatible_applySubst (σ : Aref → Aref) (τ : MoveType) :
    MoveType.baseCompatible τ (applySubstMoveType σ τ) := by
  cases τ with
  | basic bt => simp [MoveType.baseCompatible, applySubstMoveType]
  | ref bt r bk => simp [MoveType.baseCompatible, applySubstMoveType]

/-- MoveType.baseCompatible is transitive -/
private lemma baseCompatible_trans (τ1 τ2 τ3 : MoveType) :
    MoveType.baseCompatible τ1 τ2 → MoveType.baseCompatible τ2 τ3 → MoveType.baseCompatible τ1 τ3 := by
  intro h12 h23
  cases τ1 <;> cases τ2 <;> cases τ3 <;> simp_all [MoveType.baseCompatible]

-- ============================================================
-- Helper lemmas: SiteEnvSubstEquiv
-- ============================================================

/-- SiteEnvSubstEquiv transitivity through composition -/
private lemma SiteEnvSubstEquiv_trans (σ1 σ2 : Aref → Aref) (se1 se2 se3 : SiteEnv) :
    SiteEnvSubstEquiv σ1 se1 se2 →
    SiteEnvSubstEquiv σ2 se2 se3 →
    SiteEnvSubstEquiv (fun r => σ2 (σ1 r)) se1 se3 := by
  intro hse1 hse2
  unfold SiteEnvSubstEquiv at hse1 hse2 ⊢
  intro k
  specialize hse1 k
  specialize hse2 k
  cases hk1 : lookup se1 k with
  | none =>
    simp only [hk1] at hse1 ⊢
    cases hk2 : lookup se2 k with
    | none =>
      simp only [hk2] at hse2
      cases hk3 : lookup se3 k with
      | none => trivial
      | some _ => simp only [hk3] at hse2
    | some _ => simp only [hk2] at hse1
  | some τ1 =>
    simp only [hk1] at hse1 ⊢
    cases hk2 : lookup se2 k with
    | none => simp only [hk2] at hse1
    | some τ2 =>
      simp only [hk2] at hse1 hse2
      cases hk3 : lookup se3 k with
      | none => simp only [hk3] at hse2
      | some τ3 =>
        simp only [hk3] at hse2 ⊢
        rw [applySubstMoveType_comp, hse1, hse2]

/-- SiteEnvSubstEquiv after deleting the same key from both SiteEnvs. -/
private lemma SiteEnvSubstEquiv_delete (σ : Aref → Aref) (se1 se2 : SiteEnv) (a : Site) :
    SiteEnvSubstEquiv σ se1 se2 →
    SiteEnvSubstEquiv σ (delete se1 a) (delete se2 a) := by
  intro hse
  unfold SiteEnvSubstEquiv at hse ⊢
  intro k
  by_cases hka : k = a
  · subst hka; simp only [lookup_delete_same]
  · rw [lookup_delete_ne _ a k hka, lookup_delete_ne _ a k hka]
    exact hse k

/-- SiteEnvSubstEquiv lookup: extract info about a specific key -/
private lemma SiteEnvSubstEquiv_lookup_some (σ : Aref → Aref) (se1 se2 : SiteEnv) (k : Site) (τ1 : MoveType) :
    SiteEnvSubstEquiv σ se1 se2 →
    lookup se1 k = some τ1 →
    lookup se2 k = some (applySubstMoveType σ τ1) := by
  intro hse hlook
  unfold SiteEnvSubstEquiv at hse
  specialize hse k
  simp only [hlook] at hse
  cases hk2 : lookup se2 k with
  | none => simp only [hk2] at hse
  | some τ2 =>
    simp only [hk2] at hse
    congr; exact hse.symm

/-- SiteEnvSubstEquiv: if se1 has no key k, then se2 has no key k either -/
private lemma SiteEnvSubstEquiv_lookup_none (σ : Aref → Aref) (se1 se2 : SiteEnv) (k : Site) :
    SiteEnvSubstEquiv σ se1 se2 →
    lookup se1 k = none →
    lookup se2 k = none := by
  intro hse hlook
  unfold SiteEnvSubstEquiv at hse
  specialize hse k
  simp only [hlook] at hse
  cases hk2 : lookup se2 k with
  | none => rfl
  | some _ => simp only [hk2] at hse

/-- SiteEnvSubstEquiv: notIn transfers -/
private lemma SiteEnvSubstEquiv_notIn (σ : Aref → Aref) (se1 se2 : SiteEnv) (a : Site) :
    SiteEnvSubstEquiv σ se1 se2 →
    notIn se1 a →
    notIn se2 a := by
  intro hse hnotIn
  have h1 : lookup se1 a = none := notIn_implies_lookup_none se1 a hnotIn
  have h2 : lookup se2 a = none := SiteEnvSubstEquiv_lookup_none σ se1 se2 a hse h1
  exact lookup_none_implies_notIn se2 a h2

/-- SiteEnvSubstEquiv after inserting the same key with σ-related types -/
private lemma SiteEnvSubstEquiv_insert (σ : Aref → Aref) (se1 se2 : SiteEnv) (a : Site)
    (τ1 τ2 : MoveType) :
    SiteEnvSubstEquiv σ se1 se2 →
    applySubstMoveType σ τ1 = τ2 →
    SiteEnvSubstEquiv σ (insert se1 a τ1) (insert se2 a τ2) := by
  intro hse heq
  unfold SiteEnvSubstEquiv at hse ⊢
  intro k
  by_cases hka : k = a
  · subst hka
    simp only [lookup_insert_same]
    exact heq
  · rw [lookup_insert_ne _ a k _ hka, lookup_insert_ne _ a k _ hka]
    exact hse k

-- ============================================================
-- Helper lemmas: VarEnvSubstEquiv
-- ============================================================

/-- VarEnvSubstEquiv transitivity through composition -/
private lemma VarEnvSubstEquiv_trans (σ1 σ2 : Aref → Aref) (ve1 ve2 ve3 : VarEnv) :
    VarEnvSubstEquiv σ1 ve1 ve2 →
    VarEnvSubstEquiv σ2 ve2 ve3 →
    VarEnvSubstEquiv (fun r => σ2 (σ1 r)) ve1 ve3 := by
  intro hve1 hve2
  unfold VarEnvSubstEquiv at hve1 hve2 ⊢
  intro k
  specialize hve1 k
  specialize hve2 k
  cases hk1 : lookup ve1 k with
  | none =>
    simp only [hk1] at hve1 ⊢
    cases hk2 : lookup ve2 k with
    | none =>
      simp only [hk2] at hve2
      cases hk3 : lookup ve3 k with
      | none => trivial
      | some _ => simp only [hk3] at hve2
    | some _ => simp only [hk2] at hve1
  | some val1 =>
    obtain ⟨isv1, τ1, ms1⟩ := val1
    simp only [hk1] at hve1 ⊢
    cases hk2 : lookup ve2 k with
    | none => simp only [hk2] at hve1
    | some val2 =>
      obtain ⟨isv2, τ2, ms2⟩ := val2
      simp only [hk2] at hve1 hve2
      cases hk3 : lookup ve3 k with
      | none => simp only [hk3] at hve2
      | some val3 =>
        obtain ⟨isv3, τ3, ms3⟩ := val3
        simp only [hk3] at hve2 ⊢
        -- Case-split on IsValid constructors; simp_all handles match reduction
        cases isv1 <;> cases isv2 <;> cases isv3 <;>
          simp_all [applySubstMoveType_comp] ;
          exact baseCompatible_trans _ _ _ hve1.1 hve2.1

/-- Extract valid var info from VarEnvSubstEquiv -/
private lemma VarEnvSubstEquiv_lookup_valid (σ : Aref → Aref) (ve1 ve2 : VarEnv) (x : Var)
    (τ : MoveType) (ms : Mut) :
    VarEnvSubstEquiv σ ve1 ve2 →
    lookup ve1 x = some (.validVar, τ, ms) →
    lookup ve2 x = some (.validVar, applySubstMoveType σ τ, ms) := by
  intro hve hlook
  unfold VarEnvSubstEquiv at hve
  specialize hve x
  simp only [hlook] at hve
  cases hk2 : lookup ve2 x with
  | none => simp only [hk2] at hve
  | some val2 =>
    obtain ⟨isv2, τ2, ms2⟩ := val2
    simp only [hk2] at hve
    cases isv2 <;> simp_all

/-- Extract invalid var info from VarEnvSubstEquiv -/
private lemma VarEnvSubstEquiv_lookup_invalid (σ : Aref → Aref) (ve1 ve2 : VarEnv) (x : Var)
    (τ : MoveType) (ms : Mut) :
    VarEnvSubstEquiv σ ve1 ve2 →
    lookup ve1 x = some (.invalidVar, τ, ms) →
    ∃ τ2, lookup ve2 x = some (.invalidVar, τ2, ms) ∧ MoveType.baseCompatible τ τ2 := by
  intro hve hlook
  unfold VarEnvSubstEquiv at hve
  specialize hve x
  simp only [hlook] at hve
  cases hk2 : lookup ve2 x with
  | none => simp only [hk2] at hve
  | some val2 =>
    obtain ⟨isv2, τ2, ms2⟩ := val2
    simp only [hk2] at hve
    cases isv2 with
    | validVar => simp at hve
    | invalidVar =>
      simp at hve
      obtain ⟨hbc, hms⟩ := hve
      subst hms
      exact ⟨τ2, rfl, hbc⟩

/-- VarEnvSubstEquiv after updating to invalidVar with σ-related types.
    Uses the fact that insert and update are identical for AssocMap. -/
private lemma VarEnvSubstEquiv_update_invalid (σ : Aref → Aref) (ve1 ve2 : VarEnv) (x : Var)
    (τ : MoveType) (ms : Mut) :
    VarEnvSubstEquiv σ ve1 ve2 →
    VarEnvSubstEquiv σ
      (update ve1 x (.invalidVar, τ, ms))
      (update ve2 x (.invalidVar, applySubstMoveType σ τ, ms)) := by
  intro hve
  unfold VarEnvSubstEquiv at hve ⊢
  intro k
  -- update and insert are definitionally equal
  have upd_eq1 : update ve1 x (.invalidVar, τ, ms) = insert ve1 x (.invalidVar, τ, ms) := rfl
  have upd_eq2 : update ve2 x (.invalidVar, applySubstMoveType σ τ, ms) =
      insert ve2 x (.invalidVar, applySubstMoveType σ τ, ms) := rfl
  by_cases hkx : k = x
  · subst hkx
    rw [upd_eq1, upd_eq2, lookup_insert_same, lookup_insert_same]
    exact ⟨baseCompatible_applySubst σ τ, rfl⟩
  · rw [upd_eq1, upd_eq2, lookup_insert_ne _ x k _ hkx, lookup_insert_ne _ x k _ hkx]
    exact hve k

/-- VarEnvSubstEquiv after updating to validVar with σ-related types. -/
private lemma VarEnvSubstEquiv_update_valid (σ : Aref → Aref) (ve1 ve2 : VarEnv) (x : Var)
    (τ : MoveType) (ms : Mut) :
    VarEnvSubstEquiv σ ve1 ve2 →
    VarEnvSubstEquiv σ
      (update ve1 x (.validVar, τ, ms))
      (update ve2 x (.validVar, applySubstMoveType σ τ, ms)) := by
  intro hve
  unfold VarEnvSubstEquiv at hve ⊢
  intro k
  have upd_eq1 : update ve1 x (.validVar, τ, ms) = insert ve1 x (.validVar, τ, ms) := rfl
  have upd_eq2 : update ve2 x (.validVar, applySubstMoveType σ τ, ms) =
      insert ve2 x (.validVar, applySubstMoveType σ τ, ms) := rfl
  by_cases hkx : k = x
  · subst hkx
    rw [upd_eq1, upd_eq2, lookup_insert_same, lookup_insert_same]
    exact ⟨rfl, rfl⟩
  · rw [upd_eq1, upd_eq2, lookup_insert_ne _ x k _ hkx, lookup_insert_ne _ x k _ hkx]
    exact hve k

/-- VarEnvSubstEquiv: none in ve1 implies none in ve2 -/
private lemma VarEnvSubstEquiv_lookup_none (σ : Aref → Aref) (ve1 ve2 : VarEnv) (x : Var) :
    VarEnvSubstEquiv σ ve1 ve2 →
    lookup ve1 x = none →
    lookup ve2 x = none := by
  intro hve hlook
  unfold VarEnvSubstEquiv at hve
  specialize hve x
  simp only [hlook] at hve
  cases hk2 : lookup ve2 x with
  | none => rfl
  | some _ => simp only [hk2] at hve

-- ============================================================
-- Helper lemmas: not_borrowed weakening
-- ============================================================

/-- not_borrowed weakens through subsumes, given .root ∈ envL.pathEnv.refs -/
private lemma not_borrowed_weaken (σ : Aref → Aref) (envL env : TypeEnv) (x : Var) :
    not_borrowed x envL →
    (∀ u v, u ∈ envL.pathEnv.refs → v ∈ envL.pathEnv.refs →
      ∀ path, interpret_regex (env.pathEnv.paths (σ u, σ v)) path →
              interpret_regex (envL.pathEnv.paths (u, v)) path) →
    (∀ r, (∀ n, r ≠ .refid n) → σ r = r) →
    envL.pathEnv.refs.map σ = env.pathEnv.refs →
    Aref.root ∈ envL.pathEnv.refs →
    not_borrowed x env := by
  intro hnb hpaths hid hrefs hroot_mem r hr
  -- r ∈ env.pathEnv.refs, so r = σ u for some u ∈ envL.pathEnv.refs
  rw [← hrefs] at hr
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hr
  -- σ .root = .root (identity on non-refid)
  have hσroot : σ .root = .root := hid .root (fun n h => by cases h)
  -- Contrapositive of path inclusion
  intro hinterp
  -- env.pathEnv.paths (.root, σ u) accepts [.root_to_var x]
  -- rewrite .root as σ .root
  rw [← hσroot] at hinterp
  -- By path inclusion: envL.pathEnv.paths (.root, u) accepts [.root_to_var x]
  have := hpaths .root u hroot_mem hu [.root_to_var x] hinterp
  -- But not_borrowed x envL says this doesn't happen
  exact hnb u hu this

-- ============================================================
-- Helper lemmas: MoveType.compatible with σ
-- ============================================================

/-- Aref.Compatible is preserved by σ when σ .root = .root and r ≠ .root implies σ r ≠ .root -/
private lemma Aref_Compatible_subst {r r' : Aref} {σ : Aref → Aref}
    (hcompat : Aref.Compatible r r')
    (hσroot : σ .root = .root)
    (hσ : r ≠ .root → σ r ≠ .root) :
    Aref.Compatible (σ r) r' := by
  cases r with
  | root =>
    rw [hσroot]
    exact hcompat
  | refid n =>
    have hne : Aref.refid n ≠ .root := by intro h; cases h
    have hσne := hσ hne
    cases r' with
    | root => exact absurd hcompat (by simp [Aref.Compatible])
    | refid _ =>
      unfold Aref.Compatible
      cases hσr : (σ (.refid n)) with
      | root => exact absurd hσr hσne
      | refid _ => trivial
      | varRef _ => trivial
    | varRef _ =>
      unfold Aref.Compatible
      cases hσr : (σ (.refid n)) with
      | root => exact absurd hσr hσne
      | refid _ => trivial
      | varRef _ => trivial
  | varRef v =>
    have hne : Aref.varRef v ≠ .root := by intro h; cases h
    have hσne := hσ hne
    cases r' with
    | root => exact absurd hcompat (by simp [Aref.Compatible])
    | refid _ =>
      unfold Aref.Compatible
      cases hσr : (σ (.varRef v)) with
      | root => exact absurd hσr hσne
      | refid _ => trivial
      | varRef _ => trivial
    | varRef _ =>
      unfold Aref.Compatible
      cases hσr : (σ (.varRef v)) with
      | root => exact absurd hσr hσne
      | refid _ => trivial
      | varRef _ => trivial

-- ============================================================
-- Helper: MoveType.compatible through baseCompatible + σ
-- ============================================================

/-- If τ is compatible with τ', τ_env is base-compatible with τ, and both τ_env and σ(τ')
    have non-root arefs, then τ_env is compatible with σ(τ'). -/
private lemma MoveType_compatible_of_baseCompatible_subst (σ : Aref → Aref) (τ τ_env τ' : MoveType)
    (hcompat : MoveType.compatible τ τ')
    (hbc : MoveType.baseCompatible τ τ_env)
    (hτ_env_notroot : moveTypeRefNotRoot τ_env)
    (hσ_nonroot : ∀ r, r ≠ .root → σ r ≠ .root)
    (hτ'_notroot : moveTypeRefNotRoot τ') :
    MoveType.compatible τ_env (applySubstMoveType σ τ') := by
  cases τ with
  | basic bt1 =>
    cases τ' with
    | basic bt2 =>
      cases τ_env with
      | basic bt3 =>
        simp only [MoveType.compatible] at hcompat ⊢
        simp only [MoveType.baseCompatible] at hbc
        simp only [applySubstMoveType]
        rw [← hcompat]; exact hbc.symm
      | ref _ _ _ => simp [MoveType.baseCompatible] at hbc
    | ref _ _ _ => exact absurd hcompat (by simp [MoveType.compatible])
  | ref bt1 r1 bk1 =>
    cases τ' with
    | basic _ => exact absurd hcompat (by simp [MoveType.compatible])
    | ref bt2 r2 bk2 =>
      cases τ_env with
      | basic _ => simp [MoveType.baseCompatible] at hbc
      | ref bt3 r3 bk3 =>
        simp only [MoveType.compatible, applySubstMoveType] at hcompat ⊢
        simp only [MoveType.baseCompatible] at hbc
        refine ⟨?_, ?_, ?_⟩
        · rw [← hcompat.1]; exact hbc.1.symm
        · -- Aref.Compatible r3 (σ r2): both non-root
          simp only [moveTypeRefNotRoot] at hτ_env_notroot hτ'_notroot
          unfold Aref.Compatible
          cases r3 with
          | root => exact absurd rfl hτ_env_notroot
          | refid _ =>
            cases hσr2 : σ r2 with
            | root => exact absurd hσr2 (hσ_nonroot r2 hτ'_notroot)
            | refid _ => trivial
            | varRef _ => trivial
          | varRef _ =>
            cases hσr2 : σ r2 with
            | root => exact absurd hσr2 (hσ_nonroot r2 hτ'_notroot)
            | refid _ => trivial
            | varRef _ => trivial
        · rw [← hcompat.2.2]; exact hbc.2.symm

-- ============================================================
-- Helper: moveTypeRefNotRoot preserved by applySubstMoveType
-- ============================================================

/-- moveTypeRefNotRoot is preserved by applySubstMoveType when σ doesn't create roots -/
private lemma moveTypeRefNotRoot_applySubst (σ : Aref → Aref) (τ : MoveType)
    (h : moveTypeRefNotRoot τ) (hσ : ∀ r, r ≠ .root → σ r ≠ .root) :
    moveTypeRefNotRoot (applySubstMoveType σ τ) := by
  cases τ with
  | basic _ => trivial
  | ref _ r _ => exact hσ r h

-- ============================================================
-- Transitivity of TypeEnv.subsumes
-- ============================================================

/-- Transitivity of TypeEnv.subsumes:
    if envL1.subsumes envL2 and envL2.subsumes env, then envL1.subsumes env. -/
theorem TypeEnv.subsumes_trans (envL1 envL2 env : TypeEnv) :
    TypeEnv.subsumes envL1 envL2 →
    TypeEnv.subsumes envL2 env →
    TypeEnv.subsumes envL1 env := by
  intro hsub1 hsub2
  obtain ⟨σ1, hid1, hve1, hse1, hrefs1, hinj1, hlast1⟩ := hsub1
  obtain ⟨hnonroot1, hpaths1⟩ := hlast1
  obtain ⟨σ2, hid2, hve2, hse2, hrefs2, hinj2, hlast2⟩ := hsub2
  obtain ⟨hnonroot2, hpaths2⟩ := hlast2
  refine ⟨fun r => σ2 (σ1 r), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r hr
    change σ2 (σ1 r) = r
    rw [hid1 r hr]
    exact hid2 r hr
  · exact VarEnvSubstEquiv_trans σ1 σ2 _ _ _ hve1 hve2
  · exact SiteEnvSubstEquiv_trans σ1 σ2 _ _ _ hse1 hse2
  · have hcomp : (fun r => σ2 (σ1 r)) = (σ2 ∘ σ1) := rfl
    rw [hcomp, ← List.map_map, hrefs1, hrefs2]
  · intro u v hu hv huv
    have hσ1u : σ1 u ∈ envL2.pathEnv.refs := by
      rw [← hrefs1]; exact List.mem_map_of_mem (f := σ1) hu
    have hσ1v : σ1 v ∈ envL2.pathEnv.refs := by
      rw [← hrefs1]; exact List.mem_map_of_mem (f := σ1) hv
    exact hinj1 u v hu hv (hinj2 (σ1 u) (σ1 v) hσ1u hσ1v huv)
  · constructor
    · -- nonroot: composed σ preserves non-root
      intro r hr
      change σ2 (σ1 r) ≠ .root
      exact hnonroot2 (σ1 r) (hnonroot1 r hr)
    · -- paths
      intro u v hu hv path hinterp
      have hσ1u : σ1 u ∈ envL2.pathEnv.refs := by
        rw [← hrefs1]; exact List.mem_map_of_mem (f := σ1) hu
      have hσ1v : σ1 v ∈ envL2.pathEnv.refs := by
        rw [← hrefs1]; exact List.mem_map_of_mem (f := σ1) hv
      exact hpaths1 u v hu hv path (hpaths2 (σ1 u) (σ1 v) hσ1u hσ1v path hinterp)

-- ============================================================
-- Helper: σ doesn't map non-root to root (from injectivity + root ∈ refs)
-- ============================================================

/-- If σ is injective on refs and .root ∈ refs and σ .root = .root,
    then for any r ∈ refs with r ≠ .root, σ r ≠ .root -/
private lemma σ_nonroot_of_inj (σ : Aref → Aref) (refs : List Aref)
    (hinj : ∀ u v, u ∈ refs → v ∈ refs → σ u = σ v → u = v)
    (hid : ∀ r, (∀ n, r ≠ .refid n) → σ r = r)
    (hroot : .root ∈ refs) (r : Aref) (hr : r ∈ refs) (hne : r ≠ .root) :
    σ r ≠ .root := by
  intro habs
  have hσroot : σ .root = .root := hid .root (fun n h => by cases h)
  have := hinj r .root hr hroot (by rw [habs, hσroot])
  exact hne this

-- ============================================================
-- Helper lemmas: site_tracked / var_tracked preservation
-- ============================================================

/-- site_tracked is preserved by inserting a basic type (no refs) -/
private lemma site_tracked_insert_basic (pe_refs : List Aref)
    (se : SiteEnv) (a : Site) (bt : BasicMoveType)
    (hst : ∀ s bbt r bk, lookup se s = some (.ref bbt r bk) → r ∈ pe_refs) :
    ∀ s bbt r bk, lookup (insert se a (.basic bt)) s = some (.ref bbt r bk) → r ∈ pe_refs := by
  intro s bbt r bk hlook
  by_cases hs : s = a
  · subst hs; rw [lookup_insert_same] at hlook; cases hlook
  · rw [lookup_insert_ne _ _ _ _ hs] at hlook; exact hst _ _ _ _ hlook

/-- site_tracked is preserved by delete -/
private lemma site_tracked_delete (pe_refs : List Aref)
    (se : SiteEnv) (a : Site)
    (hst : ∀ s bbt r bk, lookup se s = some (.ref bbt r bk) → r ∈ pe_refs) :
    ∀ s bbt r bk, lookup (delete se a) s = some (.ref bbt r bk) → r ∈ pe_refs := by
  intro s bbt r bk hlook
  by_cases hs : s = a
  · subst hs; rw [lookup_delete_same] at hlook; cases hlook
  · rw [lookup_delete_ne _ _ _ hs] at hlook; exact hst _ _ _ _ hlook

/-- site_tracked for insert of a type that came from varEnv (e.g., move) -/
private lemma site_tracked_insert_from_var (pe_refs : List Aref)
    (ve : VarEnv) (se : SiteEnv) (x : Var) (a : Site) (τ : MoveType) (ms : Mut)
    (hlook_x : lookup ve x = some (.validVar, τ, ms))
    (hst : ∀ s bt r bk, lookup se s = some (.ref bt r bk) → r ∈ pe_refs)
    (hvt : ∀ x' bt r bk ms', lookup ve x' = some (.validVar, .ref bt r bk, ms') → r ∈ pe_refs) :
    ∀ s bt r bk, lookup (insert se a τ) s = some (.ref bt r bk) → r ∈ pe_refs := by
  intro s bt r bk hlook
  by_cases hs : s = a
  · subst hs; rw [lookup_insert_same] at hlook
    simp only [Option.some.injEq] at hlook; subst hlook
    exact hvt _ _ _ _ _ hlook_x
  · rw [lookup_insert_ne _ _ _ _ hs] at hlook; exact hst _ _ _ _ hlook

/-- var_tracked is preserved by update to invalidVar -/
private lemma var_tracked_update_invalid (pe_refs : List Aref)
    (ve : VarEnv) (x : Var) (τ : MoveType) (ms : Mut)
    (hvt : ∀ x' bt r bk ms', lookup ve x' = some (.validVar, .ref bt r bk, ms') → r ∈ pe_refs) :
    ∀ x' bt r bk ms', lookup (update ve x (.invalidVar, τ, ms)) x' =
      some (.validVar, .ref bt r bk, ms') → r ∈ pe_refs := by
  intro x' bt r bk ms' hlook
  change lookup (insert _ _ _) _ = _ at hlook
  by_cases hx : x' = x
  · subst hx; rw [lookup_insert_same] at hlook; simp at hlook
  · rw [lookup_insert_ne _ _ _ _ hx] at hlook; exact hvt _ _ _ _ _ hlook

/-- var_tracked is preserved by update to validVar when new type comes from siteEnv -/
private lemma var_tracked_update_valid_from_site (pe_refs : List Aref)
    (ve : VarEnv) (se : SiteEnv) (x : Var) (a : Site) (τ' : MoveType) (ms : Mut)
    (hlook_a : lookup se a = some τ')
    (hst : ∀ s bt r bk, lookup se s = some (.ref bt r bk) → r ∈ pe_refs)
    (hvt : ∀ x' bt r bk ms', lookup ve x' = some (.validVar, .ref bt r bk, ms') → r ∈ pe_refs) :
    ∀ x' bt r bk ms', lookup (update ve x (.validVar, τ', ms)) x' =
      some (.validVar, .ref bt r bk, ms') → r ∈ pe_refs := by
  intro x' bt r bk ms' hlook
  change lookup (insert _ _ _) _ = _ at hlook
  by_cases hx : x' = x
  · subst hx; rw [lookup_insert_same] at hlook
    simp only [Option.some.injEq, Prod.mk.injEq] at hlook
    obtain ⟨-, rfl, -⟩ := hlook
    exact hst _ _ _ _ hlook_a
  · rw [lookup_insert_ne _ _ _ _ hx] at hlook; exact hvt _ _ _ _ _ hlook

/-- List.map σ commutes with List.filter (· ≠ r) when σ is injective and r ∈ l -/
private lemma map_filter_ne (σ : Aref → Aref) (l : List Aref) (r : Aref)
    (hinj : ∀ u v, u ∈ l → v ∈ l → σ u = σ v → u = v)
    (hr : r ∈ l) :
    (l.filter (· ≠ r)).map σ = (l.map σ).filter (· ≠ σ r) := by
  induction l with
  | nil => cases hr
  | cons hd tl ih =>
    have hinj' : ∀ u v, u ∈ tl → v ∈ tl → σ u = σ v → u = v :=
      fun u v hu hv => hinj u v (.tail _ hu) (.tail _ hv)
    simp only [List.filter, List.map]
    by_cases hhd : hd = r
    · -- After subst, r is eliminated (replaced by hd)
      subst hhd
      simp only [ne_eq, not_true_eq_false, decide_false]
      by_cases hr' : hd ∈ tl
      · exact ih hinj' hr'
      · -- hd ∉ tl: both filters are no-ops
        have h1 : tl.filter (· ≠ hd) = tl :=
          List.filter_eq_self.mpr fun x hx => decide_eq_true (fun h => hr' (h ▸ hx))
        have h2 : (tl.map σ).filter (· ≠ σ hd) = tl.map σ :=
          List.filter_eq_self.mpr fun y hy => by
            obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
            exact decide_eq_true fun h => hr' ((hinj x hd (.tail _ hx) (.head _) h) ▸ hx)
        rw [h1, h2]
    · have hr' : r ∈ tl := (List.mem_cons.mp hr).resolve_left (fun h => hhd h.symm)
      have hσne : σ hd ≠ σ r := fun h => hhd (hinj hd r (.head _) hr h)
      simp only [ne_eq, hhd, not_false_eq_true, decide_true, hσne]
      exact congrArg (σ hd :: ·) (ih hinj' hr')

/-- SiteEnvSubstEquiv is preserved by deleteAll on both sides -/
private lemma SiteEnvSubstEquiv_deleteAll (σ : Aref → Aref) (se1 se2 : SiteEnv) (keys : List Site) :
    SiteEnvSubstEquiv σ se1 se2 →
    SiteEnvSubstEquiv σ (deleteAll se1 keys) (deleteAll se2 keys) := by
  intro hse
  unfold SiteEnvSubstEquiv at hse ⊢
  intro k
  simp only [deleteAll, lookup]
  by_cases hk : k ∈ keys
  · rw [List.lookup_filter_mem_none se1.entries k keys hk,
        List.lookup_filter_mem_none se2.entries k keys hk]; trivial
  · rw [List.lookup_filter_notin se1.entries k keys hk,
        List.lookup_filter_notin se2.entries k keys hk]
    exact hse k

/-- site_tracked is preserved by deleteAll -/
private lemma site_tracked_deleteAll (pe_refs : List Aref)
    (se : SiteEnv) (keys : List Site)
    (hst : ∀ s bt r bk, lookup se s = some (.ref bt r bk) → r ∈ pe_refs) :
    ∀ s bt r bk, lookup (deleteAll se keys) s = some (.ref bt r bk) → r ∈ pe_refs := by
  intro s bt r bk hlook
  simp only [deleteAll, lookup] at hlook
  by_cases hs : s ∈ keys
  · rw [List.lookup_filter_mem_none se.entries s keys hs] at hlook; cases hlook
  · rw [List.lookup_filter_notin se.entries s keys hs] at hlook
    exact hst s bt r bk (by simp only [lookup]; exact hlook)

/-- SiteEnvSubstEquiv is preserved by addFieldSites (only basic types inserted) -/
private lemma SiteEnvSubstEquiv_addFieldSites (σ : Aref → Aref)
    (fentries : AssocMap Field BasicMoveType)
    (se1 se2 : SiteEnv) (fields : List (Field × Site)) :
    SiteEnvSubstEquiv σ se1 se2 →
    SiteEnvSubstEquiv σ (addFieldSites fentries se1 fields) (addFieldSites fentries se2 fields) := by
  intro hse
  unfold addFieldSites
  induction fields generalizing se1 se2 with
  | nil => exact hse
  | cons hd rest ih =>
    simp only [List.foldl]
    apply ih
    cases hlook : lookup fentries hd.1 with
    | none => exact hse
    | some bt =>
      exact SiteEnvSubstEquiv_insert σ _ _ _ _ _ hse (applySubstMoveType_basic σ bt)

/-- site_tracked is preserved by addFieldSites (only basic types inserted) -/
private lemma site_tracked_addFieldSites (pe_refs : List Aref)
    (fentries : AssocMap Field BasicMoveType)
    (se : SiteEnv) (fields : List (Field × Site))
    (hst : ∀ s bt r bk, lookup se s = some (.ref bt r bk) → r ∈ pe_refs) :
    ∀ s bt r bk, lookup (addFieldSites fentries se fields) s = some (.ref bt r bk) → r ∈ pe_refs := by
  unfold addFieldSites
  induction fields generalizing se with
  | nil => exact hst
  | cons hd rest ih =>
    simp only [List.foldl]
    apply ih
    cases hlook : lookup fentries hd.1 with
    | none => exact hst
    | some bt => exact site_tracked_insert_basic _ _ _ _ hst

-- ============================================================
-- Helper: is_empty completeness for deriv-free regexes
-- ============================================================

/-- Completeness of is_empty for derivative-free regexes over inhabited types -/
private lemma is_empty_complete_deriv_free [Inhabited α] [DecidableEq α]
    (r : Regex α) (hdf : DerivFree r) (h : ∀ s, ¬interpret_regex r s) :
    is_empty r = true := by
  induction r with
  | empty => rfl
  | ε => exact absurd rfl (h [])
  | char a => exact absurd rfl (h [a])
  | dot =>
    have : interpret_regex (Regex.dot : Regex α) [default] := show [default].length = 1 from rfl
    exact absurd this (h [default])
  | union r1 r2 ih1 ih2 =>
    simp only [is_empty, Bool.and_eq_true]
    exact ⟨ih1 hdf.1 (fun s hs => h s (Or.inl hs)),
           ih2 hdf.2 (fun s hs => h s (Or.inr hs))⟩
  | concat r1 r2 ih1 ih2 =>
    simp only [is_empty, Bool.or_eq_true]
    by_cases h1 : ∀ s, ¬interpret_regex r1 s
    · exact Or.inl (ih1 hdf.1 h1)
    · by_cases h2 : ∀ s, ¬interpret_regex r2 s
      · exact Or.inr (ih2 hdf.2 h2)
      · have ⟨s1, hs1⟩ : ∃ s, interpret_regex r1 s := by
          by_contra hc; exact h1 (fun s hs => hc ⟨s, hs⟩)
        have ⟨s2, hs2⟩ : ∃ s, interpret_regex r2 s := by
          by_contra hc; exact h2 (fun s hs => hc ⟨s, hs⟩)
        exact absurd ⟨s1, s2, rfl, hs1, hs2⟩ (h (s1 ++ s2))
  | star _ _ => exact absurd star_matches.nil (h [])
  | deriv _ _ _ => exact absurd hdf id

/-- Completeness of only_matches_empty for derivative-free regexes over inhabited types -/
private lemma only_matches_empty_complete_deriv_free [Inhabited α] [DecidableEq α]
    (r : Regex α) (hdf : DerivFree r) (h : ∀ s, interpret_regex r s → s = []) :
    only_matches_empty r = true := by
  induction r with
  | empty => rfl
  | ε => rfl
  | char a =>
    have hinterp : interpret_regex (Regex.char a) [a] := show [a] = [a] from rfl
    have := h [a] hinterp
    cases this
  | dot =>
    have hinterp : interpret_regex (Regex.dot : Regex α) [default] :=
      show [default].length = 1 from rfl
    have := h [default] hinterp
    cases this
  | union r1 r2 ih1 ih2 =>
    simp only [only_matches_empty, Bool.and_eq_true]
    exact ⟨ih1 hdf.1 (fun s hs => h s (Or.inl hs)),
           ih2 hdf.2 (fun s hs => h s (Or.inr hs))⟩
  | concat r1 r2 ih1 ih2 =>
    simp only [only_matches_empty, Bool.or_eq_true, Bool.and_eq_true]
    by_cases h1 : ∃ s, interpret_regex r1 s
    · by_cases h2 : ∃ s, interpret_regex r2 s
      · right
        exact ⟨ih1 hdf.1 (fun s hs => by
                obtain ⟨s2, hs2⟩ := h2
                have heq := h (s ++ s2) ⟨s, s2, rfl, hs, hs2⟩
                exact (List.append_eq_nil_iff.mp heq).1),
               ih2 hdf.2 (fun s hs => by
                obtain ⟨s1, hs1⟩ := h1
                have heq := h (s1 ++ s) ⟨s1, s, rfl, hs1, hs⟩
                exact (List.append_eq_nil_iff.mp heq).2)⟩
      · have h2' : ∀ s, ¬interpret_regex r2 s := fun s hs => h2 ⟨s, hs⟩
        left; exact Or.inr (is_empty_complete_deriv_free r2 hdf.2 h2')
    · have h1' : ∀ s, ¬interpret_regex r1 s := fun s hs => h1 ⟨s, hs⟩
      left; exact Or.inl (is_empty_complete_deriv_free r1 hdf.1 h1')
  | star r ih =>
    simp only [only_matches_empty]
    exact ih hdf (fun s hs => by
      by_cases heq : s = []
      · exact heq
      · have hstar := star_matches.cons s [] heq hs star_matches.nil
        have := h (s ++ []) hstar
        rw [List.append_nil] at this
        exact absurd this heq)
  | deriv _ _ _ => exact absurd hdf id

-- ============================================================
-- Helper: Regex monotonicity for extend and der
-- ============================================================

/-- Monotonicity of `extend` (∘): if re2 ⊆ re1, then extend re2 p ⊆ extend re1 p -/
private lemma extend_mono (re1 re2 : Regex PathElement) (p : Path)
    (h : ∀ s, interpret_regex re2 s → interpret_regex re1 s) :
    ∀ s, interpret_regex (re2 ∘ p) s → interpret_regex (re1 ∘ p) s := by
  induction p generalizing re1 re2 with
  | nil => exact h
  | cons a p ih =>
    apply ih
    intro s hs
    simp only [interpret_regex] at hs ⊢
    obtain ⟨s1, s2, heq, h1, h2⟩ := hs
    exact ⟨s1, s2, heq, h s1 h1, h2⟩

/-- Monotonicity of `der`: if re2 ⊆ re1, then der re2 p ⊆ der re1 p -/
private lemma der_mono (re1 re2 : Regex PathElement) (p : Path)
    (h : ∀ s, interpret_regex re2 s → interpret_regex re1 s) :
    ∀ s, interpret_regex (der re2 p) s → interpret_regex (der re1 p) s := by
  induction p generalizing re1 re2 with
  | nil => exact h
  | cons a p ih =>
    apply ih
    intro s hs
    simp only [interpret_regex] at hs ⊢
    exact h (a :: s) hs

-- ============================================================
-- Helper: check_outbound weakening
-- ============================================================

/-- check_outbound weakens: if outbound check passes for envL, it also passes for env (fewer paths) -/
private lemma check_outbound_weaken (σ : Aref → Aref) (peL peE : PathEnv)
    (r : Aref)
    (hrefs : peL.refs.map σ = peE.refs)
    (hpaths : ∀ u v, u ∈ peL.refs → v ∈ peL.refs →
      ∀ path, interpret_regex (peE.paths (σ u, σ v)) path →
              interpret_regex (peL.paths (u, v)) path)
    (hr_mem : r ∈ peL.refs)
    (houtbound : check_outbound peL r (λ re ↦ only_matches_empty (simplify re))) :
    check_outbound peE (σ r) (λ re ↦ only_matches_empty (simplify re)) := by
  unfold check_outbound at houtbound ⊢
  intro s' hs'
  rw [← hrefs] at hs'
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hs'
  have hL := houtbound v hv
  -- hL : only_matches_empty (simplify (peL.paths (r, v))) = true
  -- Need: only_matches_empty (simplify (peE.paths (σ r, σ v))) = true
  have hL_sound := only_matches_empty_sound (simplify (peL.paths (r, v))) hL
  -- hL_sound : ∀ s, interpret_regex (simplify (peL.paths (r, v))) s → s = []
  have hE_only_empty : ∀ s, interpret_regex (peE.paths (σ r, σ v)) s → s = [] := by
    intro s hs
    have := hpaths r v hr_mem hv s hs
    exact hL_sound s ((simplify_preserves_semantics (peL.paths (r, v)) s).mpr this)
  apply only_matches_empty_complete_deriv_free _ (simplify_deriv_free _)
  intro s hs
  exact hE_only_empty s ((simplify_preserves_semantics (peE.paths (σ r, σ v)) s).mp hs)

-- ============================================================
-- Helper: extending σ with a fresh ref mapping
-- ============================================================

/-- Extend σ with t ↦ t' -/
private abbrev extendSubst (σ : Aref → Aref) (t t' : Aref) : Aref → Aref :=
  fun r => if r = t then t' else σ r

/-- extendSubst is identity on non-refid when t is a refid -/
private lemma extendSubst_id (σ : Aref → Aref) (t t' : Aref)
    (hid : ∀ r, (∀ n, r ≠ .refid n) → σ r = r)
    (ht_refid : ∃ n, t = .refid n) :
    ∀ r, (∀ n, r ≠ .refid n) → extendSubst σ t t' r = r := by
  intro r hr
  obtain ⟨n, hn⟩ := ht_refid
  have hrt : r ≠ t := by subst hn; exact fun h => hr n h
  simp only [extendSubst, if_neg hrt]
  exact hid r hr

/-- VarEnvSubstEquiv is preserved by extendSubst when t doesn't appear in varEnv refs -/
private lemma VarEnvSubstEquiv_extend (σ : Aref → Aref) (t t' : Aref)
    (ve1 ve2 : VarEnv)
    (hve : VarEnvSubstEquiv σ ve1 ve2)
    (ht_fresh_ve : ∀ x bt s bk ms, lookup ve1 x = some (.validVar, .ref bt s bk, ms) → s ≠ t) :
    VarEnvSubstEquiv (extendSubst σ t t') ve1 ve2 := by
  unfold VarEnvSubstEquiv at hve ⊢
  intro k; specialize hve k
  cases hk1 : lookup ve1 k with
  | none =>
    simp only [hk1] at hve ⊢
    cases hk2 : lookup ve2 k with
    | none => simp only [hk2] at hve ⊢
    | some _ => simp only [hk2] at hve
  | some val1 =>
    obtain ⟨isv1, τ1, ms1⟩ := val1
    simp only [hk1] at hve ⊢
    cases hk2 : lookup ve2 k with
    | none => simp only [hk2] at hve
    | some val2 =>
      obtain ⟨isv2, τ2, ms2⟩ := val2
      simp only [hk2] at hve ⊢
      cases isv1 <;> cases isv2 <;> try exact hve
      -- Only validVar/validVar case remains
      obtain ⟨hτ, hms⟩ := hve
      refine ⟨?_, hms⟩
      cases τ1 with
      | basic _ => exact hτ
      | ref bt s bk =>
        simp only [applySubstMoveType] at hτ ⊢
        have hst : s ≠ t := ht_fresh_ve k bt s bk ms1 hk1
        simp only [extendSubst, if_neg hst]; exact hτ

/-- SiteEnvSubstEquiv for insert of ref type with extendSubst -/
private lemma SiteEnvSubstEquiv_extend_insert_ref (σ : Aref → Aref) (t t' : Aref)
    (se1 se2 : SiteEnv) (a : Site) (τ : BasicMoveType) (bk : BorrowingKind)
    (hse : SiteEnvSubstEquiv σ se1 se2)
    (ht_fresh_se : ∀ k bt r bk, lookup se1 k = some (.ref bt r bk) → r ≠ t) :
    SiteEnvSubstEquiv (extendSubst σ t t')
      (insert se1 a (.ref τ t bk))
      (insert se2 a (.ref τ t' bk)) := by
  unfold SiteEnvSubstEquiv at hse ⊢
  intro k
  by_cases hka : k = a
  · subst hka; simp only [lookup_insert_same, applySubstMoveType, extendSubst]
    simp
  · rw [lookup_insert_ne _ _ _ _ hka, lookup_insert_ne _ _ _ _ hka]
    specialize hse k
    cases hk1 : lookup se1 k with
    | none =>
      simp only [hk1] at hse ⊢
      cases hk2 : lookup se2 k with
      | none => simp only [hk2] at hse ⊢
      | some _ => simp only [hk2] at hse
    | some τk =>
      simp only [hk1] at hse ⊢
      cases hk2 : lookup se2 k with
      | none => simp only [hk2] at hse
      | some τk2 =>
        simp only [hk2] at hse ⊢
        cases τk with
        | basic bt => simp only [applySubstMoveType]; exact hse
        | ref bt r bk' =>
          simp only [applySubstMoveType] at hse ⊢
          have hrt : r ≠ t := ht_fresh_se k bt r bk' hk1
          simp only [extendSubst, if_neg hrt]
          exact hse

/-- extendSubst is injective on extended refs when t' is fresh in env -/
private lemma extendSubst_injective (σ : Aref → Aref) (t t' : Aref) (refs : List Aref)
    (hinj : ∀ u v, u ∈ refs → v ∈ refs → σ u = σ v → u = v)
    (ht_not_in : t ∉ refs)
    (ht'_not_in_mapped : t' ∉ refs.map σ) :
    ∀ u v, u ∈ (if t ∉ refs then t :: refs else refs) →
           v ∈ (if t ∉ refs then t :: refs else refs) →
           extendSubst σ t t' u = extendSubst σ t t' v → u = v := by
  rw [if_pos ht_not_in]
  intro u v hu hv heq
  rcases List.mem_cons.mp hu with hut | hu'
  · -- hut : u = t
    rcases List.mem_cons.mp hv with hvt | hv'
    · exact hut.trans hvt.symm
    · have hvne : v ≠ t := fun h => ht_not_in (h ▸ hv')
      have h1 : extendSubst σ t t' u = t' := by rw [hut]; simp [extendSubst]
      have h2 : extendSubst σ t t' v = σ v := by simp only [extendSubst, if_neg hvne]
      rw [h1, h2] at heq
      exact absurd (heq ▸ List.mem_map_of_mem (f := σ) hv') ht'_not_in_mapped
  · -- hu' : u ∈ refs
    have hune : u ≠ t := fun h => ht_not_in (h ▸ hu')
    rcases List.mem_cons.mp hv with hvt | hv'
    · -- hvt : v = t
      have h1 : extendSubst σ t t' u = σ u := by simp only [extendSubst, if_neg hune]
      have h2 : extendSubst σ t t' v = t' := by rw [hvt]; simp [extendSubst]
      rw [h1, h2] at heq
      exact absurd (heq.symm ▸ List.mem_map_of_mem (f := σ) hu') ht'_not_in_mapped
    · -- hv' : v ∈ refs
      have hvne : v ≠ t := fun h => ht_not_in (h ▸ hv')
      simp only [extendSubst, if_neg hune, if_neg hvne] at heq
      exact hinj u v hu' hv' heq

/-- extendSubst preserves nonroot -/
private lemma extendSubst_nonroot (σ : Aref → Aref) (t t' : Aref)
    (hnonroot : ∀ r, r ≠ .root → σ r ≠ .root)
    (ht'_ne_root : t' ≠ .root) :
    ∀ r, r ≠ .root → extendSubst σ t t' r ≠ .root := by
  intro r hr
  simp only [extendSubst]
  split
  · exact ht'_ne_root
  · exact hnonroot r hr

/-- List.map with extendSubst reduces to List.map with σ when t ∉ l -/
private lemma map_extendSubst_eq_map_σ (σ : Aref → Aref) (t t' : Aref) (l : List Aref)
    (ht : t ∉ l) :
    l.map (extendSubst σ t t') = l.map σ := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    have hne : hd ≠ t := fun h => ht (h ▸ .head tl)
    have ht' : t ∉ tl := fun h => ht (.tail hd h)
    simp only [List.map, extendSubst, if_neg hne, ih ht']

-- ============================================================
-- Main weakening theorem
-- ============================================================

/-- Ref uniqueness across varEnv and siteEnv: no ref appears in two places simultaneously.
    Mirrors live_refs_unique from WellTypedState but stated for arbitrary envs. -/
abbrev RefsUnique (ve : VarEnv) (se : SiteEnv) : Prop :=
  ∀ r,
    (∀ x bt bk ms s bt' bk',
       lookup ve x = some (.validVar, .ref bt r bk, ms) →
       lookup se s = some (.ref bt' r bk') → False) ∧
    (∀ s s' bt bt' bk bk', s ≠ s' →
       lookup se s = some (.ref bt r bk) →
       lookup se s' = some (.ref bt' r bk') → False) ∧
    (∀ x y bt bt' bk bk' ms ms', x ≠ y →
       lookup ve x = some (.validVar, .ref bt r bk, ms) →
       lookup ve y = some (.validVar, .ref bt' r bk', ms') → False)

-- ============================================================
-- RefsUnique preservation helpers
-- ============================================================

/-- RefsUnique is preserved by inserting a basic type into siteEnv -/
private lemma RefsUnique_insert_basic (ve : VarEnv) (se : SiteEnv) (a : Site) (bt : BasicMoveType)
    (h : RefsUnique ve se) : RefsUnique ve (insert se a (.basic bt)) := by
  intro r; refine ⟨fun x bt' bk ms s bt'' bk' hv hs => ?_, fun s s' bt' bt'' bk bk' hne hs hs' => ?_, (h r).2.2⟩
  · by_cases hsa : s = a
    · subst hsa; rw [lookup_insert_same] at hs; cases hs
    · rw [lookup_insert_ne _ _ _ _ hsa] at hs; exact (h r).1 _ _ _ _ _ _ _ hv hs
  · by_cases hsa : s = a
    · subst hsa; rw [lookup_insert_same] at hs; cases hs
    · by_cases hsa' : s' = a
      · subst hsa'; rw [lookup_insert_same] at hs'; cases hs'
      · rw [lookup_insert_ne _ _ _ _ hsa] at hs; rw [lookup_insert_ne _ _ _ _ hsa'] at hs'
        exact (h r).2.1 _ _ _ _ _ _ hne hs hs'

/-- RefsUnique is preserved by deleting a site -/
private lemma RefsUnique_delete_site (ve : VarEnv) (se : SiteEnv) (a : Site)
    (h : RefsUnique ve se) : RefsUnique ve (delete se a) := by
  intro r; refine ⟨fun x bt bk ms s bt' bk' hv hs => ?_, fun s s' bt bt' bk bk' hne hs hs' => ?_, (h r).2.2⟩
  · by_cases hsa : s = a
    · subst hsa; rw [lookup_delete_same] at hs; cases hs
    · rw [lookup_delete_ne _ _ _ hsa] at hs; exact (h r).1 _ _ _ _ _ _ _ hv hs
  · by_cases hsa : s = a
    · subst hsa; rw [lookup_delete_same] at hs; cases hs
    · by_cases hsa' : s' = a
      · subst hsa'; rw [lookup_delete_same] at hs'; cases hs'
      · rw [lookup_delete_ne _ _ _ hsa] at hs; rw [lookup_delete_ne _ _ _ hsa'] at hs'
        exact (h r).2.1 _ _ _ _ _ _ hne hs hs'

/-- RefsUnique is preserved by updating a var to invalidVar -/
private lemma RefsUnique_invalidate_var (ve : VarEnv) (se : SiteEnv) (x : Var) (τ : MoveType) (ms : Mut)
    (h : RefsUnique ve se) : RefsUnique (update ve x (.invalidVar, τ, ms)) se := by
  intro r; refine ⟨fun y bt bk ms' s bt' bk' hv hs => ?_, (h r).2.1, fun y z bt bt' bk bk' ms' ms'' hne hvy hvz => ?_⟩
  · change lookup (insert _ _ _) _ = _ at hv
    by_cases hyx : y = x
    · subst hyx; rw [lookup_insert_same] at hv; simp at hv
    · rw [lookup_insert_ne _ _ _ _ hyx] at hv; exact (h r).1 _ _ _ _ _ _ _ hv hs
  · change lookup (insert _ _ _) _ = _ at hvy hvz
    by_cases hyx : y = x
    · subst hyx; rw [lookup_insert_same] at hvy; simp at hvy
    · by_cases hzx : z = x
      · subst hzx; rw [lookup_insert_same] at hvz; simp at hvz
      · rw [lookup_insert_ne _ _ _ _ hyx] at hvy; rw [lookup_insert_ne _ _ _ _ hzx] at hvz
        exact (h r).2.2 _ _ _ _ _ _ _ _ hne hvy hvz

/-- RefsUnique for let_bind_move: invalidate var x, insert site a with x's type.
    Requires x's lookup to derive var-var contradictions. -/
private lemma RefsUnique_move_to_site (ve : VarEnv) (se : SiteEnv) (x : Var) (a : Site)
    (τ : MoveType) (ms : Mut)
    (hlook_x : lookup ve x = some (.validVar, τ, ms))
    (h : RefsUnique ve se) :
    RefsUnique (update ve x (.invalidVar, τ, ms)) (insert se a τ) := by
  intro r; obtain ⟨hvs, hss, hvv⟩ := h r
  refine ⟨fun y bt bk ms' s bt' bk' hv hs => ?_, fun s s' bt bt' bk bk' hne hs hs' => ?_,
    fun y z bt bt' bk bk' ms' ms'' hne hvy hvz => ?_⟩
  · -- var-site case
    change lookup (insert _ _ _) _ = _ at hv
    by_cases hyx : y = x
    · subst hyx; rw [lookup_insert_same] at hv; simp at hv
    · rw [lookup_insert_ne _ _ _ _ hyx] at hv
      by_cases hsa : s = a
      · rw [hsa, lookup_insert_same] at hs
        simp only [Option.some.injEq] at hs
        -- hs : τ = .ref bt' r bk'; use rw to avoid eliminating τ
        rw [hs] at hlook_x
        exact hvv y x _ _ _ _ _ _ hyx hv hlook_x
      · rw [lookup_insert_ne _ _ _ _ hsa] at hs; exact hvs _ _ _ _ _ _ _ hv hs
  · -- site-site case
    by_cases hsa : s = a
    · rw [hsa, lookup_insert_same] at hs
      by_cases hsa' : s' = a
      · exact absurd (hsa.trans hsa'.symm) hne
      · rw [lookup_insert_ne _ _ _ _ hsa'] at hs'
        simp only [Option.some.injEq] at hs
        rw [hs] at hlook_x
        exact hvs x _ _ _ _ _ _ hlook_x hs'
    · by_cases hsa' : s' = a
      · rw [hsa', lookup_insert_same] at hs'
        rw [lookup_insert_ne _ _ _ _ hsa] at hs
        simp only [Option.some.injEq] at hs'
        rw [hs'] at hlook_x
        exact hvs x _ _ _ _ _ _ hlook_x hs
      · rw [lookup_insert_ne _ _ _ _ hsa] at hs; rw [lookup_insert_ne _ _ _ _ hsa'] at hs'
        exact hss _ _ _ _ _ _ hne hs hs'
  · -- var-var case
    change lookup (insert _ _ _) _ = _ at hvy hvz
    by_cases hyx : y = x
    · subst hyx; rw [lookup_insert_same] at hvy; simp at hvy
    · by_cases hzx : z = x
      · subst hzx; rw [lookup_insert_same] at hvz; simp at hvz
      · rw [lookup_insert_ne _ _ _ _ hyx] at hvy; rw [lookup_insert_ne _ _ _ _ hzx] at hvz
        exact hvv _ _ _ _ _ _ _ _ hne hvy hvz

/-- RefsUnique for var_assign: make var x valid with type τ' from site a, delete site a -/
private lemma RefsUnique_assign_from_site (ve : VarEnv) (se : SiteEnv)
    (x : Var) (a : Site) (τ' : MoveType) (ms : Mut)
    (hlook_a : lookup se a = some τ')
    (h : RefsUnique ve se) :
    RefsUnique (update ve x (.validVar, τ', ms)) (delete se a) := by
  intro r; obtain ⟨hvs, hss, hvv⟩ := h r
  refine ⟨fun y bt bk ms' s bt' bk' hv hs => ?_, fun s s' bt bt' bk bk' hne hs hs' => ?_,
    fun y z bt bt' bk bk' ms' ms'' hne hvy hvz => ?_⟩
  · -- var-site case
    change lookup (insert _ _ _) _ = _ at hv
    by_cases hyx : y = x
    · rw [hyx, lookup_insert_same] at hv
      simp only [Option.some.injEq, Prod.mk.injEq] at hv
      obtain ⟨-, hτ', -⟩ := hv
      rw [hτ'] at hlook_a
      by_cases hsa : s = a
      · rw [hsa, lookup_delete_same] at hs; cases hs
      · rw [lookup_delete_ne _ _ _ hsa] at hs
        exact hss a s _ _ _ _ (Ne.symm hsa) hlook_a hs
    · rw [lookup_insert_ne _ _ _ _ hyx] at hv
      by_cases hsa : s = a
      · rw [hsa, lookup_delete_same] at hs; cases hs
      · rw [lookup_delete_ne _ _ _ hsa] at hs
        exact hvs _ _ _ _ _ _ _ hv hs
  · -- site-site case
    by_cases hsa : s = a
    · rw [hsa, lookup_delete_same] at hs; cases hs
    · by_cases hsa' : s' = a
      · rw [hsa', lookup_delete_same] at hs'; cases hs'
      · rw [lookup_delete_ne _ _ _ hsa] at hs; rw [lookup_delete_ne _ _ _ hsa'] at hs'
        exact hss _ _ _ _ _ _ hne hs hs'
  · -- var-var case
    change lookup (insert _ _ _) _ = _ at hvy hvz
    by_cases hyx : y = x
    · rw [hyx, lookup_insert_same] at hvy
      simp only [Option.some.injEq, Prod.mk.injEq] at hvy
      obtain ⟨-, hτ', -⟩ := hvy
      rw [hτ'] at hlook_a
      by_cases hzx : z = x
      · exact absurd (hyx.trans hzx.symm) hne
      · rw [lookup_insert_ne _ _ _ _ hzx] at hvz
        exact hvs z _ _ _ a _ _ hvz hlook_a
    · by_cases hzx : z = x
      · rw [hzx, lookup_insert_same] at hvz
        simp only [Option.some.injEq, Prod.mk.injEq] at hvz
        obtain ⟨-, hτ', -⟩ := hvz
        rw [hτ'] at hlook_a
        rw [lookup_insert_ne _ _ _ _ hyx] at hvy
        exact hvs y _ _ _ a _ _ hvy hlook_a
      · rw [lookup_insert_ne _ _ _ _ hyx] at hvy; rw [lookup_insert_ne _ _ _ _ hzx] at hvz
        exact hvv _ _ _ _ _ _ _ _ hne hvy hvz

/-- RefsUnique is preserved by deleteAll -/
private lemma RefsUnique_deleteAll (ve : VarEnv) (se : SiteEnv) (keys : List Site)
    (h : RefsUnique ve se) : RefsUnique ve (deleteAll se keys) := by
  intro r; obtain ⟨hvs, hss, hvv⟩ := h r
  refine ⟨fun x bt bk ms s bt' bk' hv hs => ?_, fun s s' bt bt' bk bk' hne hs hs' => ?_, hvv⟩
  · simp only [deleteAll, lookup] at hs
    by_cases hsk : s ∈ keys
    · rw [List.lookup_filter_mem_none se.entries s keys hsk] at hs; cases hs
    · rw [List.lookup_filter_notin se.entries s keys hsk] at hs
      exact hvs _ _ _ _ _ _ _ hv (by simp only [lookup]; exact hs)
  · simp only [deleteAll, lookup] at hs hs'
    by_cases hsk : s ∈ keys
    · rw [List.lookup_filter_mem_none se.entries s keys hsk] at hs; cases hs
    · by_cases hsk' : s' ∈ keys
      · rw [List.lookup_filter_mem_none se.entries s' keys hsk'] at hs'; cases hs'
      · rw [List.lookup_filter_notin se.entries s keys hsk] at hs
        rw [List.lookup_filter_notin se.entries s' keys hsk'] at hs'
        exact hss _ _ _ _ _ _ hne (by simp only [lookup]; exact hs) (by simp only [lookup]; exact hs')

/-- RefsUnique is preserved by addFieldSites (only basic types inserted) -/
private lemma RefsUnique_addFieldSites (ve : VarEnv) (se : SiteEnv)
    (fentries : AssocMap Field BasicMoveType) (fields : List (Field × Site))
    (h : RefsUnique ve se) :
    RefsUnique ve (addFieldSites fentries se fields) := by
  unfold addFieldSites
  induction fields generalizing se with
  | nil => exact h
  | cons hd rest ih =>
    simp only [List.foldl]
    apply ih
    cases hlook : lookup fentries hd.1 with
    | none => exact h
    | some bt => exact RefsUnique_insert_basic _ _ _ _ h

/-- RefsUnique is preserved by inserting a ref type with a fresh aref -/
private lemma RefsUnique_insert_fresh_ref (ve : VarEnv) (se : SiteEnv) (a : Site)
    (τ : BasicMoveType) (t : Aref) (bk : BorrowingKind)
    (huniq : RefsUnique ve se)
    (ht_ne_var : ∀ x bt r bk' ms, lookup ve x = some (.validVar, .ref bt r bk', ms) → r ≠ t)
    (ht_ne_site : ∀ s bt r bk', lookup se s = some (.ref bt r bk') → r ≠ t) :
    RefsUnique ve (insert se a (.ref τ t bk)) := by
  intro r; obtain ⟨hvs, hss, hvv⟩ := huniq r
  refine ⟨fun x bt' bk' ms s bt'' bk'' hv hs => ?_,
          fun s s' bt' bt'' bk' bk'' hne hs hs' => ?_, hvv⟩
  · -- var-site
    by_cases hsa : s = a
    · rw [hsa, lookup_insert_same] at hs
      simp only [Option.some.injEq, MoveType.ref.injEq] at hs
      obtain ⟨-, htr, -⟩ := hs  -- htr : t = r
      exact absurd htr.symm (ht_ne_var x bt' r bk' ms hv)
    · rw [lookup_insert_ne _ _ _ _ hsa] at hs; exact hvs _ _ _ _ _ _ _ hv hs
  · -- site-site
    by_cases hsa : s = a
    · rw [hsa, lookup_insert_same] at hs
      simp only [Option.some.injEq, MoveType.ref.injEq] at hs
      obtain ⟨-, htr, -⟩ := hs  -- htr : t = r
      by_cases hsa' : s' = a
      · exact absurd (hsa.trans hsa'.symm) hne
      · rw [lookup_insert_ne _ _ _ _ hsa'] at hs'
        exact absurd htr.symm (ht_ne_site s' bt'' r bk'' hs')
    · by_cases hsa' : s' = a
      · rw [hsa', lookup_insert_same] at hs'
        simp only [Option.some.injEq, MoveType.ref.injEq] at hs'
        obtain ⟨-, htr', -⟩ := hs'
        rw [lookup_insert_ne _ _ _ _ hsa] at hs
        exact absurd htr'.symm (ht_ne_site s bt' r bk' hs)
      · rw [lookup_insert_ne _ _ _ _ hsa] at hs; rw [lookup_insert_ne _ _ _ _ hsa'] at hs'
        exact hss _ _ _ _ _ _ hne hs hs'

/-- RefsUnique for delete-then-insert-ref pattern (e.g., freeze, borrowField) -/
private lemma RefsUnique_delete_insert_fresh_ref (ve : VarEnv) (se : SiteEnv) (a af : Site)
    (τ : BasicMoveType) (t : Aref) (bk : BorrowingKind)
    (huniq : RefsUnique ve se)
    (ht_ne_var : ∀ x bt r bk' ms, lookup ve x = some (.validVar, .ref bt r bk', ms) → r ≠ t)
    (ht_ne_site : ∀ s bt r bk', lookup se s = some (.ref bt r bk') → r ≠ t) :
    RefsUnique ve (insert (delete se a) af (.ref τ t bk)) :=
  RefsUnique_insert_fresh_ref ve (delete se a) af τ t bk
    (RefsUnique_delete_site ve se a huniq)
    ht_ne_var
    (fun s bt r bk' hs => by
      by_cases hsa : s = a
      · subst hsa; rw [lookup_delete_same] at hs; cases hs
      · rw [lookup_delete_ne _ _ _ hsa] at hs; exact ht_ne_site s bt r bk' hs)

-- ============================================================
-- Helper lemmas: update_with_extension characterization
-- ============================================================

/-- Characterize paths of update_with_extension when both args equal z -/
private lemma uwe_paths_eq_eq (z x : Aref) (p : Path) (pe : PathEnv) :
    (update_with_extension z x p pe).paths (z, z) = Regex.ε := by
  simp [update_with_extension]

/-- Characterize paths of update_with_extension when first arg ≠ z, second = z -/
private lemma uwe_paths_ne_eq (z x : Aref) (p : Path) (pe : PathEnv) (u : Aref) (h : u ≠ z) :
    (update_with_extension z x p pe).paths (u, z) = pe.paths (u, x) ∘ p := by
  simp [update_with_extension, h]

/-- Characterize paths of update_with_extension when first arg = z, second ≠ z -/
private lemma uwe_paths_eq_ne (z x : Aref) (p : Path) (pe : PathEnv) (v : Aref) (h : v ≠ z) :
    (update_with_extension z x p pe).paths (z, v) = der (pe.paths (x, v)) p := by
  simp [update_with_extension, h]

/-- Characterize paths of update_with_extension when both args ≠ z -/
private lemma uwe_paths_ne_ne (z x : Aref) (p : Path) (pe : PathEnv) (u v : Aref)
    (hu : u ≠ z) (hv : v ≠ z) :
    (update_with_extension z x p pe).paths (u, v) = pe.paths (u, v) := by
  simp [update_with_extension, hu, hv]

/-- Characterize refs of update_with_extension when z is fresh -/
private lemma uwe_refs_fresh (z x : Aref) (p : Path) (pe : PathEnv) (h : z ∉ pe.refs) :
    (update_with_extension z x p pe).refs = z :: pe.refs := by
  simp [update_with_extension, h]

private lemma uwe_epsilon_refs_fresh (z x : Aref) (pe : PathEnv) (h : z ∉ pe.refs) :
    (update_with_epsilon z x pe).refs = z :: pe.refs :=
  uwe_refs_fresh z x [] pe h

/-- Characterize refs of consume_ref_transfer when r' is fresh -/
private lemma crt_refs_fresh (pe : PathEnv) (r r' : Aref)
    (hr'_fresh : r' ∉ pe.refs) (hne : r' ≠ r) :
    (consume_ref_transfer pe r r').refs = r' :: pe.refs.filter (· ≠ r) := by
  show List.filter (· ≠ r) (if r' ∉ pe.refs then r' :: pe.refs else pe.refs) = _
  rw [if_pos hr'_fresh]
  simp only [List.filter_cons, decide_eq_true_eq, if_pos hne]

/-- When z is already in pe.refs, update_with_extension doesn't change refs -/
private lemma uwe_refs_not_fresh (z x : Aref) (p : Path) (pe : PathEnv) (h : z ∈ pe.refs) :
    (update_with_extension z x p pe).refs = pe.refs := by
  simp [update_with_extension, show ¬(z ∉ pe.refs) from not_not.mpr h]

/-- After gc(uwe(eps(pe, r, r), r, x, p), r), the refs are the same as pe.refs
    (r is added by eps, kept by uwe, then removed by gc) -/
private lemma gc_uwe_eps_refs_eq (pe : PathEnv) (r x : Aref) (p : Path)
    (hr_fresh : r ∉ pe.refs) :
    (garbage_collect (update_with_extension r x p (update_with_epsilon r r pe)) r).refs
    = pe.refs := by
  have h_eps_refs := uwe_epsilon_refs_fresh r r pe hr_fresh
  have h_eps_mem : r ∈ (update_with_epsilon r r pe).refs := by
    rw [h_eps_refs]; exact .head _
  have h_uwe_refs := uwe_refs_not_fresh r x p _ h_eps_mem
  simp only [garbage_collect, h_uwe_refs, h_eps_refs,
    List.filter_cons, ne_eq, not_true_eq_false, decide_false]
  exact List.filter_eq_self.mpr (fun a ha => by simp; exact fun heq => hr_fresh (heq ▸ ha))

/-- After uwe(eps(pe, r, r), r, x, p), paths (u, v) are unchanged when u ≠ r and v ≠ r -/
private lemma uwe_eps_paths_not_r (pe : PathEnv) (r x : Aref) (p : Path)
    (u v : Aref) (hu : u ≠ r) (hv : v ≠ r) :
    (update_with_extension r x p (update_with_epsilon r r pe)).paths (u, v)
    = pe.paths (u, v) := by
  simp only [update_with_extension, update_with_epsilon,
    show ¬(v = r) from hv, show ¬(u = r) from hu, false_and, ↓reduceIte]

/-- SiteEnvSubstEquiv is preserved through insert-delete-delete (ax inserted, then a and ax deleted) -/
private lemma SiteEnvSubstEquiv_delete_delete_insert (σ : Aref → Aref)
    (se1 se2 : SiteEnv) (ax a : Site) (v1 v2 : MoveType) :
    SiteEnvSubstEquiv σ se1 se2 →
    SiteEnvSubstEquiv σ (delete (delete (insert se1 ax v1) a) ax)
                        (delete (delete (insert se2 ax v2) a) ax) := by
  intro hse k
  by_cases hk_ax : k = ax
  · subst hk_ax; simp only [lookup_delete_same]
  · rw [lookup_delete_ne _ _ _ hk_ax, lookup_delete_ne _ _ _ hk_ax]
    by_cases hk_a : k = a
    · subst hk_a; simp only [lookup_delete_same]
    · rw [lookup_delete_ne _ _ _ hk_a, lookup_delete_ne _ _ _ hk_a,
        lookup_insert_ne _ _ _ _ hk_ax, lookup_insert_ne _ _ _ _ hk_ax]
      exact hse k

-- ============================================================
-- Helper: the outer update_with_extension absorbs the inner
-- update_with_epsilon when both use the same fresh ref z.
-- This is because the outer update completely overwrites all
-- paths involving z, making the inner update's path changes irrelevant.
-- ============================================================

private lemma update_extension_absorbs_epsilon (z x : Aref) (p : Path) (pe : PathEnv)
    (hz_fresh : z ∉ pe.refs) (hx_ne_z : x ≠ z) :
    update_with_extension z x p (update_with_extension z z [] pe)
    = update_with_extension z x p pe := by
  -- Inner update's paths at (a,b) with a≠z, b≠z equal pe.paths(a,b)
  have h_inner : ∀ a b, a ≠ z → b ≠ z →
    (update_with_extension z z [] pe).paths (a, b) = pe.paths (a, b) :=
    fun a b ha hb => uwe_paths_ne_ne z z [] pe a b ha hb
  let inner := update_with_extension z z [] pe
  -- Show refs match
  have h_refs : (update_with_extension z x p inner).refs
      = (update_with_extension z x p pe).refs := by
    have h_inner_refs : inner.refs = z :: pe.refs := uwe_refs_fresh z z [] pe hz_fresh
    simp [update_with_extension, hz_fresh, h_inner_refs]
  -- Show paths match
  have h_paths : (update_with_extension z x p inner).paths
      = (update_with_extension z x p pe).paths := by
    funext ⟨u, v⟩
    by_cases hv : v = z
    · rw [hv]; by_cases hu : u = z
      · rw [hu, uwe_paths_eq_eq, uwe_paths_eq_eq]
      · rw [uwe_paths_ne_eq z x p inner u hu, uwe_paths_ne_eq z x p pe u hu]
        congr 1; exact h_inner u x hu hx_ne_z
    · by_cases hu : u = z
      · rw [hu, uwe_paths_eq_ne z x p inner v hv, uwe_paths_eq_ne z x p pe v hv]
        congr 1; exact h_inner x v hx_ne_z hv
      · rw [uwe_paths_ne_ne z x p inner u v hu hv, uwe_paths_ne_ne z x p pe u v hu hv]
        exact h_inner u v hu hv
  -- Combine
  have h_ext : ∀ (pe : PathEnv), pe = ⟨pe.refs, pe.paths⟩ := fun ⟨_, _⟩ => rfl
  rw [h_ext (update_with_extension z x p inner),
      h_ext (update_with_extension z x p pe), h_refs, h_paths]

/-- Variant of update_extension_absorbs_epsilon using update_with_epsilon notation -/
private lemma uwe_absorbs_epsilon (z x : Aref) (p : Path) (pe : PathEnv)
    (hz_fresh : z ∉ pe.refs) (hx_ne_z : x ≠ z) :
    update_with_extension z x p (update_with_epsilon z z pe)
    = update_with_extension z x p pe :=
  update_extension_absorbs_epsilon z x p pe hz_fresh hx_ne_z

-- ============================================================
-- Helper: path inclusion through update_with_extension
-- ============================================================

/-- Path inclusion is preserved through update_with_extension with extendSubst.
    This handles all fresh-ref cases (copy_ref, borrowImm, borrowMut, borrowField, borrowMutField). -/
private lemma path_inclusion_update_with_extension
    (σ : Aref → Aref) (peL peE : PathEnv) (t t' x : Aref) (p : Path)
    (hpaths : ∀ u v, u ∈ peL.refs → v ∈ peL.refs →
      ∀ path, interpret_regex (peE.paths (σ u, σ v)) path → interpret_regex (peL.paths (u, v)) path)
    (ht_fresh : t ∉ peL.refs)
    (ht'_not_mapped : t' ∉ peL.refs.map σ)
    (hx_mem : x ∈ peL.refs) :
    ∀ u v, u ∈ (update_with_extension t x p peL).refs →
           v ∈ (update_with_extension t x p peL).refs →
      ∀ path, interpret_regex ((update_with_extension t' (σ x) p peE).paths
                (extendSubst σ t t' u, extendSubst σ t t' v)) path →
              interpret_regex ((update_with_extension t x p peL).paths (u, v)) path := by
  intro u v hu hv pth hinterp
  rw [uwe_refs_fresh _ _ _ _ ht_fresh] at hu hv
  -- Derive membership and inequality facts
  by_cases hut : u = t
  · by_cases hvt : v = t
    · -- Case 1: u = t, v = t → both sides are ε
      rw [hut, hvt] at hinterp ⊢
      simp only [extendSubst, ite_true] at hinterp
      rw [uwe_paths_eq_eq] at hinterp
      rw [uwe_paths_eq_eq]
      exact hinterp
    · -- Case 2: u = t, v ≠ t → der monotonicity
      have hv' : v ∈ peL.refs := (List.mem_cons.mp hv).resolve_left hvt
      have hσv_ne : σ v ≠ t' := by
        intro h; exact ht'_not_mapped (h ▸ List.mem_map_of_mem (f := σ) hv')
      rw [hut] at hinterp ⊢
      simp only [extendSubst, ite_true, if_neg hvt] at hinterp
      rw [uwe_paths_eq_ne _ _ _ _ _ hσv_ne] at hinterp
      rw [uwe_paths_eq_ne _ _ _ _ _ hvt]
      exact der_mono _ _ p (hpaths x v hx_mem hv') pth hinterp
  · have hu' : u ∈ peL.refs := (List.mem_cons.mp hu).resolve_left hut
    have hσu_ne : σ u ≠ t' := by
      intro h; exact ht'_not_mapped (h ▸ List.mem_map_of_mem (f := σ) hu')
    by_cases hvt : v = t
    · -- Case 3: u ≠ t, v = t → extend monotonicity
      rw [hvt] at hinterp ⊢
      simp only [extendSubst, if_neg hut, ite_true] at hinterp
      rw [uwe_paths_ne_eq _ _ _ _ _ hσu_ne] at hinterp
      rw [uwe_paths_ne_eq _ _ _ _ _ hut]
      exact extend_mono _ _ p (hpaths u x hu' hx_mem) pth hinterp
    · -- Case 4: u ≠ t, v ≠ t → direct from original
      have hv' : v ∈ peL.refs := (List.mem_cons.mp hv).resolve_left hvt
      have hσv_ne : σ v ≠ t' := by
        intro h; exact ht'_not_mapped (h ▸ List.mem_map_of_mem (f := σ) hv')
      simp only [extendSubst, if_neg hut, if_neg hvt] at hinterp
      rw [uwe_paths_ne_ne _ _ _ _ _ _ hσu_ne hσv_ne] at hinterp
      rw [uwe_paths_ne_ne _ _ _ _ _ _ hut hvt]
      exact hpaths u v hu' hv' pth hinterp

-- ============================================================
-- Helper: self_loop_only_empty preservation
-- ============================================================

/-- self_loop_only_empty is preserved by update_with_extension -/
private lemma self_loop_only_empty_uwe (z x : Aref) (p : Path) (pe : PathEnv)
    (h : ∀ u path, interpret_regex (pe.paths (u, u)) path → path = []) :
    ∀ u path, interpret_regex ((update_with_extension z x p pe).paths (u, u)) path → path = [] := by
  intro u path hinterp
  simp only [update_with_extension] at hinterp
  by_cases huz : u = z
  · subst huz; simp only [and_self, ↓reduceIte, interpret_regex] at hinterp; exact hinterp
  · simp only [↓reduceIte, show (u = z) = False from propext ⟨huz, False.elim⟩,
               ↓reduceIte] at hinterp
    exact h u path hinterp

/-- self_loop_only_empty is preserved by delete_ref_node -/
private lemma self_loop_only_empty_drn (pe : PathEnv) (r : Aref)
    (h : ∀ u path, interpret_regex (pe.paths (u, u)) path → path = []) :
    ∀ u path, interpret_regex ((delete_ref_node pe r).paths (u, u)) path → path = [] := by
  intro u path hinterp
  simp only [delete_ref_node] at hinterp
  by_cases hur : u = r
  · subst hur; simp only [and_self, ↓reduceIte, interpret_regex] at hinterp; exact hinterp
  · simp only [show ¬(u = r ∧ u = r) from fun ⟨h, _⟩ => hur h, ↓reduceIte,
               show ¬(u = r ∨ u = r) from not_or.mpr ⟨hur, hur⟩, ↓reduceIte] at hinterp
    exact h u path hinterp

/-- self_loop_only_empty is preserved by garbage_collect -/
private lemma self_loop_only_empty_gc (pe : PathEnv) (r : Aref)
    (h : ∀ u path, interpret_regex (pe.paths (u, u)) path → path = []) :
    ∀ u path, interpret_regex ((garbage_collect pe r).paths (u, u)) path → path = [] := by
  intro u path hinterp
  simp only [garbage_collect] at hinterp
  by_cases hur : u = r
  · subst hur; simp only [and_self, ↓reduceIte, interpret_regex] at hinterp; exact hinterp
  · simp only [show ¬(u = r ∧ u = r) from fun ⟨h, _⟩ => hur h, ↓reduceIte,
               show ¬(u = r ∨ u = r) from not_or.mpr ⟨hur, hur⟩, ↓reduceIte] at hinterp
    exact h u path hinterp

/-- self_loop_only_empty is preserved by consume_ref_transfer
    (requires paths_from_non_member_empty for the union case at fresh ref) -/
private lemma self_loop_only_empty_crt (pe : PathEnv) (r r' : Aref)
    (h : ∀ u path, interpret_regex (pe.paths (u, u)) path → path = [])
    (hpaths_from_nm : ∀ u v p, u ∉ pe.refs → u ≠ .root → u ≠ v →
      ¬interpret_regex (pe.paths (u, v)) p)
    (hr'_fresh : r' ∉ pe.refs) (hr'_ne_root : r' ≠ .root) (hr'_ne_r : r' ≠ r) :
    ∀ u path, interpret_regex ((consume_ref_transfer pe r r').paths (u, u)) path → path = [] := by
  intro u path hinterp
  simp only [consume_ref_transfer] at hinterp
  by_cases hur : u = r
  · subst hur; simp only [and_self, ↓reduceIte, interpret_regex] at hinterp; exact hinterp
  · simp only [show ¬(u = r ∧ u = r) from fun ⟨h, _⟩ => hur h, ↓reduceIte,
               show ¬(u = r ∨ u = r) from not_or.mpr ⟨hur, hur⟩, ↓reduceIte] at hinterp
    by_cases hur' : u = r'
    · subst hur'; simp only [ite_true, interpret_regex] at hinterp
      cases hinterp with
      | inl h_self => exact h u path h_self
      | inr h_from => exact absurd h_from (hpaths_from_nm u r path hr'_fresh hr'_ne_root hr'_ne_r)
    · simp only [show (u = r') = False from propext ⟨hur', False.elim⟩, ↓reduceIte] at hinterp
      exact h u path hinterp

-- ============================================================
-- Helper: path inclusion through consume_ref_transfer
-- ============================================================

/-- Path inclusion is preserved through consume_ref_transfer with extendSubst.
    This handles the freeze case where a mutable borrow is consumed and an immutable one created. -/
private lemma path_inclusion_consume_ref_transfer
    (σ : Aref → Aref) (peL peE : PathEnv) (r r' r'' : Aref)
    (hpaths : ∀ u v, u ∈ peL.refs → v ∈ peL.refs →
      ∀ path, interpret_regex (peE.paths (σ u, σ v)) path → interpret_regex (peL.paths (u, v)) path)
    (hr_mem : r ∈ peL.refs)
    (hr'_fresh : r' ∉ peL.refs)
    (hr''_fresh : r'' ∉ peE.refs)
    (hr''_not_mapped : r'' ∉ peL.refs.map σ)
    (hinj : ∀ u v, u ∈ peL.refs → v ∈ peL.refs → σ u = σ v → u = v)
    (hr'_ne_r : r' ≠ r)
    (hr''_ne_σr : r'' ≠ σ r)
    (hr''_not_root : r'' ≠ .root)
    (hself_loop_env : ∀ u p, interpret_regex (peE.paths (u, u)) p → p = [])
    (hpaths_from_nm : ∀ u v p, u ∉ peE.refs → u ≠ .root → u ≠ v →
      ¬interpret_regex (peE.paths (u, v)) p)
    (hpaths_to_nm : ∀ u v p, v ∉ peE.refs → v ≠ .root → u ≠ v →
      ¬interpret_regex (peE.paths (u, v)) p)
    (hself_loop_envL : ∀ u, interpret_regex (peL.paths (u, u)) []) :
    ∀ u v, u ∈ (consume_ref_transfer peL r r').refs →
           v ∈ (consume_ref_transfer peL r r').refs →
      ∀ path, interpret_regex ((consume_ref_transfer peE (σ r) r'').paths
                (extendSubst σ r' r'' u, extendSubst σ r' r'' v)) path →
              interpret_regex ((consume_ref_transfer peL r r').paths (u, v)) path := by
  intro u v hu hv pth hinterp
  -- Membership in crt refs means u,v ∈ r' :: filter (≠ r) peL.refs
  rw [crt_refs_fresh peL r r' hr'_fresh hr'_ne_r] at hu hv
  -- Case split on u = r' and v = r'
  by_cases hur' : u = r'
  · by_cases hvr' : v = r'
    · -- Case D: u = r', v = r' (both fresh, self-loop)
      subst hur'; subst hvr'
      simp only [extendSubst, ite_true] at hinterp
      -- crt_peE.paths(r'', r''): v = r'' branch → union(peE.paths(r'', r''), peE.paths(r'', σ r))
      have hr''_ne_σr_and : ¬(r'' = σ r ∧ r'' = σ r) :=
        fun ⟨h, _⟩ => hr''_ne_σr h
      have hr''_or : ¬(r'' = σ r ∨ r'' = σ r) :=
        not_or.mpr ⟨hr''_ne_σr, hr''_ne_σr⟩
      simp only [consume_ref_transfer, hr''_ne_σr_and, ↓reduceIte, hr''_or] at hinterp
      -- hinterp : interpret_regex (Regex.union (peE.paths (r'', r'')) (peE.paths (r'', σ r))) pth
      simp only [interpret_regex] at hinterp
      cases hinterp with
      | inl h_self =>
        -- peE.paths(r'', r'') is a self-loop, so pth = []
        have hpth_nil := hself_loop_env r'' pth h_self
        -- After both substs, r' is now v. crt_peL.paths(v, v):
        have hv_ne_r_and : ¬(v = r ∧ v = r) :=
          fun ⟨h, _⟩ => hr'_ne_r h
        have hv_or : ¬(v = r ∨ v = r) :=
          not_or.mpr ⟨hr'_ne_r, hr'_ne_r⟩
        simp only [consume_ref_transfer, hv_ne_r_and, ↓reduceIte, hv_or]
        simp only [interpret_regex]
        exact Or.inl (hpth_nil ▸ hself_loop_envL v)
      | inr h_from_r =>
        -- peE.paths(r'', σ r): r'' ∉ peE.refs, r'' ≠ root, r'' ≠ σ r → contradiction
        exact absurd h_from_r (hpaths_from_nm r'' (σ r) pth hr''_fresh hr''_not_root hr''_ne_σr)
    · -- Case B: u = r', v ≠ r' (u is fresh)
      subst hur'
      have hv_filter : v ∈ peL.refs.filter (· ≠ r) :=
        (List.mem_cons.mp hv).resolve_left hvr'
      have hv_filter' := List.mem_filter.mp hv_filter
      simp only [decide_eq_true_eq] at hv_filter'
      have ⟨hv_mem, hv_ne_r⟩ := hv_filter'
      simp only [extendSubst, ite_true, if_neg hvr'] at hinterp
      -- σ v ≠ r'' because v ∈ peL.refs → σ v ∈ peL.refs.map σ, and r'' ∉ peL.refs.map σ
      have hσv_ne_r'' : σ v ≠ r'' := by
        intro h; exact hr''_not_mapped (h ▸ List.mem_map_of_mem (f := σ) hv_mem)
      -- σ v ≠ σ r because v ≠ r and both in peL.refs, by injectivity
      have hσv_ne_σr : σ v ≠ σ r := by
        intro h; exact hv_ne_r (hinj v r hv_mem hr_mem h)
      -- crt_peE.paths(r'', σ v): ¬(r'' = σ r ∧ σ v = σ r), ¬(r'' = σ r ∨ σ v = σ r), σ v ≠ r''
      -- So: crt_peE.paths(r'', σ v) = peE.paths(r'', σ v)
      have hr''_σv_and : ¬(r'' = σ r ∧ σ v = σ r) :=
        fun ⟨h, _⟩ => hr''_ne_σr h
      have hr''_σv_or : ¬(r'' = σ r ∨ σ v = σ r) :=
        not_or.mpr ⟨hr''_ne_σr, hσv_ne_σr⟩
      simp only [consume_ref_transfer, hr''_σv_and, ↓reduceIte, hr''_σv_or,
                  show (σ v = r'') = False from propext ⟨fun h => hσv_ne_r'' h, False.elim⟩,
                  ↓reduceIte] at hinterp
      -- hinterp : interpret_regex (peE.paths (r'', σ v)) pth
      -- r'' ∉ peE.refs, r'' ≠ root, r'' ≠ σ v → contradiction
      have hr''_ne_σv : r'' ≠ σ v := Ne.symm hσv_ne_r''
      exact absurd hinterp (hpaths_from_nm r'' (σ v) pth hr''_fresh hr''_not_root hr''_ne_σv)
  · by_cases hvr' : v = r'
    · -- Case C: u ≠ r', v = r' (v is fresh)
      subst hvr'
      have hu_filter : u ∈ peL.refs.filter (· ≠ r) :=
        (List.mem_cons.mp hu).resolve_left hur'
      have hu_filter' := List.mem_filter.mp hu_filter
      simp only [decide_eq_true_eq] at hu_filter'
      have ⟨hu_mem, hu_ne_r⟩ := hu_filter'
      simp only [extendSubst, if_neg hur', ite_true] at hinterp
      -- σ u ≠ r'' because u ∈ peL.refs → σ u ∈ peL.refs.map σ, and r'' ∉ peL.refs.map σ
      have hσu_ne_r'' : σ u ≠ r'' := by
        intro h; exact hr''_not_mapped (h ▸ List.mem_map_of_mem (f := σ) hu_mem)
      -- σ u ≠ σ r because u ≠ r and both in peL.refs, by injectivity
      have hσu_ne_σr : σ u ≠ σ r := by
        intro h; exact hu_ne_r (hinj u r hu_mem hr_mem h)
      -- crt_peE.paths(σ u, r''): ¬(σ u = σ r ∧ r'' = σ r), ¬(σ u = σ r ∨ r'' = σ r), r'' = r'' → true
      -- So: v=r'' branch → union(peE.paths(σ u, r''), peE.paths(σ u, σ r))
      have hσu_r''_and : ¬(σ u = σ r ∧ r'' = σ r) :=
        fun ⟨_, h⟩ => hr''_ne_σr h
      have hσu_r''_or : ¬(σ u = σ r ∨ r'' = σ r) :=
        not_or.mpr ⟨hσu_ne_σr, hr''_ne_σr⟩
      simp only [consume_ref_transfer, hσu_r''_and, ↓reduceIte, hσu_r''_or] at hinterp
      -- hinterp : interpret_regex (Regex.union (peE.paths (σ u, r'')) (peE.paths (σ u, σ r))) pth
      simp only [interpret_regex] at hinterp
      -- After subst hvr', r' is now v. crt_peL.paths(u, v):
      have hu_v_and : ¬(u = r ∧ v = r) :=
        fun ⟨_, h⟩ => hr'_ne_r h
      have hu_v_or : ¬(u = r ∨ v = r) :=
        not_or.mpr ⟨hu_ne_r, hr'_ne_r⟩
      simp only [consume_ref_transfer, hu_v_and, ↓reduceIte, hu_v_or]
      simp only [interpret_regex]
      cases hinterp with
      | inl h_to_r'' =>
        -- peE.paths(σ u, r''): r'' ∉ peE.refs, r'' ≠ root, σ u ≠ r'' → contradiction
        exact absurd h_to_r'' (hpaths_to_nm (σ u) r'' pth hr''_fresh hr''_not_root hσu_ne_r'')
      | inr h_to_σr =>
        -- peE.paths(σ u, σ r): by hpaths → peL.paths(u, r)
        exact Or.inr (hpaths u r hu_mem hr_mem pth h_to_σr)
    · -- Case A: u ≠ r', v ≠ r' (both from original refs with u ≠ r, v ≠ r)
      have hu_filter : u ∈ peL.refs.filter (· ≠ r) :=
        (List.mem_cons.mp hu).resolve_left hur'
      have hv_filter : v ∈ peL.refs.filter (· ≠ r) :=
        (List.mem_cons.mp hv).resolve_left hvr'
      have hu_filter' := List.mem_filter.mp hu_filter
      simp only [decide_eq_true_eq] at hu_filter'
      have ⟨hu_mem, hu_ne_r⟩ := hu_filter'
      have hv_filter' := List.mem_filter.mp hv_filter
      simp only [decide_eq_true_eq] at hv_filter'
      have ⟨hv_mem, hv_ne_r⟩ := hv_filter'
      simp only [extendSubst, if_neg hur', if_neg hvr'] at hinterp
      -- σ u ≠ σ r, σ v ≠ σ r by injectivity
      have hσu_ne_σr : σ u ≠ σ r := fun h => hu_ne_r (hinj u r hu_mem hr_mem h)
      have hσv_ne_σr : σ v ≠ σ r := fun h => hv_ne_r (hinj v r hv_mem hr_mem h)
      -- σ v ≠ r'' (since σ v ∈ image, r'' ∉ image)
      have hσv_ne_r'' : σ v ≠ r'' := by
        intro h; exact hr''_not_mapped (h ▸ List.mem_map_of_mem (f := σ) hv_mem)
      -- crt_peE.paths(σ u, σ v): ¬(σ u = σ r ∧ σ v = σ r), ¬(σ u = σ r ∨ σ v = σ r), σ v ≠ r''
      -- So: crt_peE.paths(σ u, σ v) = peE.paths(σ u, σ v)
      have hσuσv_and : ¬(σ u = σ r ∧ σ v = σ r) :=
        fun ⟨h, _⟩ => hσu_ne_σr h
      have hσuσv_or : ¬(σ u = σ r ∨ σ v = σ r) :=
        not_or.mpr ⟨hσu_ne_σr, hσv_ne_σr⟩
      simp only [consume_ref_transfer, hσuσv_and, ↓reduceIte, hσuσv_or,
                  show (σ v = r'') = False from propext ⟨fun h => hσv_ne_r'' h, False.elim⟩,
                  ↓reduceIte] at hinterp
      -- hinterp : interpret_regex (peE.paths (σ u, σ v)) pth
      -- crt_peL.paths(u, v): ¬(u = r ∧ v = r), ¬(u = r ∨ v = r), v ≠ r'
      -- So: crt_peL.paths(u, v) = peL.paths(u, v)
      have huv_and : ¬(u = r ∧ v = r) :=
        fun ⟨h, _⟩ => hu_ne_r h
      have huv_or : ¬(u = r ∨ v = r) :=
        not_or.mpr ⟨hu_ne_r, hv_ne_r⟩
      simp only [consume_ref_transfer, huv_and, ↓reduceIte, huv_or,
                  show (v = r') = False from propext ⟨fun h => hvr' h, False.elim⟩,
                  ↓reduceIte]
      -- hinterp : interpret_regex (peE.paths (σ u, σ v)) pth
      exact hpaths u v hu_mem hv_mem pth hinterp

/-- Helper abbreviation for the modified envL in weakening IH calls -/
private abbrev WeakenIH (lenv : LabelEnv) (envL_mod : TypeEnv) (cont : Stmt) (retTypes : List ParamType) :=
  ∀ (env' : TypeEnv),
    TypeEnv.subsumes envL_mod env' →
    envL_mod.funEnv = env'.funEnv →
    TypeEnv.WellFormed envL_mod →
    TypeEnv.WellFormed env' →
    (∀ s bt r bk, lookup envL_mod.siteEnv s = some (.ref bt r bk) → r ∈ envL_mod.pathEnv.refs) →
    (∀ x bt r bk ms, lookup envL_mod.varEnv x = some (.validVar, .ref bt r bk, ms) → r ∈ envL_mod.pathEnv.refs) →
    RefsUnique envL_mod.varEnv envL_mod.siteEnv →
    (∀ u v p, v ∉ env'.pathEnv.refs → v ≠ .root → u ≠ v →
      ¬interpret_regex (env'.pathEnv.paths (u, v)) p) →
    (∀ u v p, u ∉ env'.pathEnv.refs → u ≠ .root → u ≠ v →
      ¬interpret_regex (env'.pathEnv.paths (u, v)) p) →
    (∀ u p, interpret_regex (env'.pathEnv.paths (u, u)) p → p = []) →
    Aref.root ∈ envL_mod.pathEnv.refs →
    typecheck_stmt lenv env' cont retTypes

private theorem weaken_let_bind_borrowImm
    (lenv : LabelEnv) (envL env : TypeEnv)
    (a : Site) (x_var : Var) (τ : BasicMoveType) (ms : Mut) (r : Aref)
    (cont : Stmt) (retTypes : List ParamType)
    (hlookup : lookup envL.varEnv x_var = some (.validVar, .basic τ, ms))
    (hnotIn : notIn envL.siteEnv a)
    (hfresh : freshRefInEnv r envL)
    (hsub : TypeEnv.subsumes envL env)
    (hfuneq : envL.funEnv = env.funEnv)
    (hwfL : TypeEnv.WellFormed envL) (hwfE : TypeEnv.WellFormed env)
    (hsite_tracked : ∀ s bt r bk, lookup envL.siteEnv s = some (.ref bt r bk) → r ∈ envL.pathEnv.refs)
    (hvar_tracked : ∀ x bt r bk ms, lookup envL.varEnv x = some (.validVar, .ref bt r bk, ms) → r ∈ envL.pathEnv.refs)
    (huniq : RefsUnique envL.varEnv envL.siteEnv)
    (hpaths_to_nm : ∀ u v p, v ∉ env.pathEnv.refs → v ≠ .root → u ≠ v →
      ¬interpret_regex (env.pathEnv.paths (u, v)) p)
    (hpaths_from_nm : ∀ u v p, u ∉ env.pathEnv.refs → u ≠ .root → u ≠ v →
      ¬interpret_regex (env.pathEnv.paths (u, v)) p)
    (hself_loop_only_empty : ∀ u p, interpret_regex (env.pathEnv.paths (u, u)) p → p = [])
    (hroot : Aref.root ∈ envL.pathEnv.refs)
    (ih : WeakenIH lenv
        {envL with siteEnv := insert envL.siteEnv a (.ref τ r .siteBorrowImm)
                   pathEnv := update_with_epsilon r r envL.pathEnv |>
                              update_with_extension r .root [.root_to_var x_var]}
        cont retTypes) :
    typecheck_stmt lenv env (.letBind a (.usage (.borrowImm x_var)) cont) retTypes := by
  obtain ⟨σ, hid, hve, hse, hrefs, hinj, hnonroot, hpaths⟩ := hsub
  have hlook_env := VarEnvSubstEquiv_lookup_valid σ _ _ _ _ _ hve hlookup
  simp only [applySubstMoveType] at hlook_env
  -- Freshness of r in envL
  have hr_fresh_pe : r ∉ envL.pathEnv.refs := freshRefInEnv_implies_freshRef r envL hfresh
  have hr_ne_root : r ≠ .root := fun h => hr_fresh_pe (h ▸ hroot)
  have hr_not_varRef : ∀ v, r ≠ .varRef v := (hfresh.2.2 : _ ∧ _).2
  have hr_refid : ∃ n, r = .refid n := by
    cases r with
    | root => exact absurd rfl hr_ne_root
    | refid n => exact ⟨n, rfl⟩
    | varRef v => exact absurd rfl (hr_not_varRef v)
  have hσ_root : σ .root = .root := hid .root (fun n => Aref.noConfusion)
  -- Pick fresh r' for env
  let r' := nextFreshRefInEnv env
  have hr'_fresh_prop := nextFreshRefInEnv_fresh_prop env
  have hr'_fresh_pe := nextFreshRefInEnv_not_in_pathEnv env
  have hr'_not_root := nextFreshRefInEnv_not_root env
  have hr'_not_mapped : r' ∉ envL.pathEnv.refs.map σ := by rw [hrefs]; exact hr'_fresh_pe
  -- Compound pathEnv refs simplification
  have h_compound_refs :
      (update_with_extension r .root [.root_to_var x_var]
        (update_with_epsilon r r envL.pathEnv)).refs = r :: envL.pathEnv.refs := by
    rw [uwe_absorbs_epsilon r .root _ envL.pathEnv hr_fresh_pe (Ne.symm hr_ne_root),
        uwe_refs_fresh r .root _ envL.pathEnv hr_fresh_pe]
  -- Apply borrowImm rule
  apply typecheck_stmt.let_bind_borrowImm lenv env _ _ _ _ r' _ _
    hlook_env
    (SiteEnvSubstEquiv_notIn σ _ _ _ hse hnotIn)
    hr'_fresh_prop
  -- IH: need subsumes for modified envs
  apply ih
  · -- subsumes: simplify compound pathEnvs via absorb lemma
    rw [uwe_absorbs_epsilon r .root _ envL.pathEnv hr_fresh_pe (Ne.symm hr_ne_root),
        uwe_absorbs_epsilon r' .root _ env.pathEnv hr'_fresh_pe (Ne.symm hr'_not_root)]
    refine ⟨extendSubst σ r r',
      extendSubst_id σ r r' hid hr_refid,
      VarEnvSubstEquiv_extend σ r r' _ _ hve
        (fun x' bt' s' bk' ms' hlook' =>
          Ne.symm (freshRefInEnv_ne_varEnv_ref r _ x' .validVar bt' s' bk' ms' hfresh hlook')),
      SiteEnvSubstEquiv_extend_insert_ref σ r r' _ _ _ _ _ hse
        (fun k bt ref bk hlook' =>
          Ne.symm (freshRefInEnv_ne_siteEnv_ref r _ k bt ref bk hfresh hlook')),
      ?_, ?_, ?_, ?_⟩
    · -- refs
      simp only [uwe_refs_fresh r .root _ envL.pathEnv hr_fresh_pe,
          uwe_refs_fresh r' .root _ env.pathEnv hr'_fresh_pe]
      simp only [List.map, extendSubst, ite_true]
      congr 1
      rw [map_extendSubst_eq_map_σ σ r r' _ hr_fresh_pe, hrefs]
    · -- injectivity
      exact extendSubst_injective σ r r' _ hinj hr_fresh_pe hr'_not_mapped
    · -- nonroot
      exact extendSubst_nonroot σ r r' hnonroot hr'_not_root
    · -- path_inclusion
      have := path_inclusion_update_with_extension σ _ _ r r' .root
        [.root_to_var x_var] hpaths hr_fresh_pe hr'_not_mapped hroot
      rw [hσ_root] at this
      exact this
  · exact hfuneq
  · -- WellFormed envL'
    exact ⟨update_with_extension_wellformed r .root [.root_to_var x_var]
            (update_with_epsilon r r envL.pathEnv)
            (update_with_epsilon_wellformed r r envL.pathEnv hwfL.pathEnv_wf hr_ne_root)
            hr_ne_root,
           SiteEnv.insert_refs_not_root _ _ _ hwfL.siteEnv_wf hr_ne_root,
           hwfL.varEnv_wf⟩
  · -- WellFormed env'
    exact ⟨update_with_extension_wellformed r' .root [.root_to_var x_var]
            (update_with_epsilon r' r' env.pathEnv)
            (update_with_epsilon_wellformed r' r' env.pathEnv hwfE.pathEnv_wf hr'_not_root)
            hr'_not_root,
           SiteEnv.insert_refs_not_root _ _ _ hwfE.siteEnv_wf hr'_not_root,
           hwfE.varEnv_wf⟩
  · -- site_tracked
    intro s' bt ref bk hlook_s'
    simp only [h_compound_refs]
    by_cases hs' : s' = a
    · subst hs'; rw [lookup_insert_same] at hlook_s'
      simp only [Option.some.injEq, MoveType.ref.injEq] at hlook_s'
      obtain ⟨-, rfl, -⟩ := hlook_s'
      exact .head _
    · rw [lookup_insert_ne _ _ _ _ hs'] at hlook_s'
      exact .tail _ (hsite_tracked _ _ _ _ hlook_s')
  · -- var_tracked
    intro x' bt ref bk ms' hlook_x'
    simp only [h_compound_refs]
    exact .tail _ (hvar_tracked _ _ _ _ _ hlook_x')
  · -- RefsUnique
    exact RefsUnique_insert_fresh_ref _ _ _ _ _ _ huniq
      (fun x' bt' ref bk' ms' hlook' =>
        Ne.symm (freshRefInEnv_ne_varEnv_ref r _ x' .validVar bt' ref bk' ms' hfresh hlook'))
      (fun s' bt' ref bk' hlook' =>
        Ne.symm (freshRefInEnv_ne_siteEnv_ref r _ s' bt' ref bk' hfresh hlook'))
  · exact update_with_extension_paths_to_non_member r' .root [.root_to_var x_var] _
      (by unfold update_with_epsilon
          exact update_with_extension_paths_to_non_member r' r' [] env.pathEnv
            hpaths_to_nm (Or.inr rfl))
      (Or.inl (by rw [uwe_epsilon_refs_fresh r' r' env.pathEnv hr'_fresh_pe]
                  exact List.mem_cons_of_mem _ hwfE.pathEnv_wf.root_in_refs))
  · exact update_with_extension_paths_from_non_member r' .root [.root_to_var x_var] _
      (by unfold update_with_epsilon
          exact update_with_extension_paths_from_non_member r' r' [] env.pathEnv
            hpaths_from_nm (Or.inr rfl))
      (Or.inl (by rw [uwe_epsilon_refs_fresh r' r' env.pathEnv hr'_fresh_pe]
                  exact List.mem_cons_of_mem _ hwfE.pathEnv_wf.root_in_refs))
  · exact self_loop_only_empty_uwe _ _ _ _
      (by unfold update_with_epsilon
          exact self_loop_only_empty_uwe r' r' [] env.pathEnv hself_loop_only_empty)
  · -- root ∈ updated refs
    simp only [h_compound_refs]
    exact .tail _ hroot

private theorem weaken_let_bind_borrowMut
    (lenv : LabelEnv) (envL env : TypeEnv)
    (a : Site) (x_var : Var) (τ : BasicMoveType) (ms : Mut) (r : Aref)
    (cont : Stmt) (retTypes : List ParamType)
    (hle : LE.le .mutable ms)
    (hlookup : lookup envL.varEnv x_var = some (.validVar, .basic τ, ms))
    (hnotIn : notIn envL.siteEnv a)
    (hfresh : freshRefInEnv r envL)
    (hsub : TypeEnv.subsumes envL env)
    (hfuneq : envL.funEnv = env.funEnv)
    (hwfL : TypeEnv.WellFormed envL) (hwfE : TypeEnv.WellFormed env)
    (hsite_tracked : ∀ s bt r bk, lookup envL.siteEnv s = some (.ref bt r bk) → r ∈ envL.pathEnv.refs)
    (hvar_tracked : ∀ x bt r bk ms, lookup envL.varEnv x = some (.validVar, .ref bt r bk, ms) → r ∈ envL.pathEnv.refs)
    (huniq : RefsUnique envL.varEnv envL.siteEnv)
    (hpaths_to_nm : ∀ u v p, v ∉ env.pathEnv.refs → v ≠ .root → u ≠ v →
      ¬interpret_regex (env.pathEnv.paths (u, v)) p)
    (hpaths_from_nm : ∀ u v p, u ∉ env.pathEnv.refs → u ≠ .root → u ≠ v →
      ¬interpret_regex (env.pathEnv.paths (u, v)) p)
    (hself_loop_only_empty : ∀ u p, interpret_regex (env.pathEnv.paths (u, u)) p → p = [])
    (hroot : Aref.root ∈ envL.pathEnv.refs)
    (ih : WeakenIH lenv
        {envL with siteEnv := insert envL.siteEnv a (.ref τ r .siteBorrowMut)
                   pathEnv := update_with_epsilon r r envL.pathEnv |>
                              update_with_extension r .root [.root_to_var x_var]}
        cont retTypes) :
    typecheck_stmt lenv env (.letBind a (.usage (.borrowMut x_var)) cont) retTypes := by
  obtain ⟨σ, hid, hve, hse, hrefs, hinj, hnonroot, hpaths⟩ := hsub
  have hlook_env := VarEnvSubstEquiv_lookup_valid σ _ _ _ _ _ hve hlookup
  simp only [applySubstMoveType] at hlook_env
  have hr_fresh_pe : r ∉ envL.pathEnv.refs := freshRefInEnv_implies_freshRef r envL hfresh
  have hr_ne_root : r ≠ .root := fun h => hr_fresh_pe (h ▸ hroot)
  have hr_not_varRef : ∀ v, r ≠ .varRef v := (hfresh.2.2 : _ ∧ _).2
  have hr_refid : ∃ n, r = .refid n := by
    cases r with
    | root => exact absurd rfl hr_ne_root
    | refid n => exact ⟨n, rfl⟩
    | varRef v => exact absurd rfl (hr_not_varRef v)
  have hσ_root : σ .root = .root := hid .root (fun n => Aref.noConfusion)
  let r' := nextFreshRefInEnv env
  have hr'_fresh_prop := nextFreshRefInEnv_fresh_prop env
  have hr'_fresh_pe := nextFreshRefInEnv_not_in_pathEnv env
  have hr'_not_root := nextFreshRefInEnv_not_root env
  have hr'_not_mapped : r' ∉ envL.pathEnv.refs.map σ := by rw [hrefs]; exact hr'_fresh_pe
  have h_compound_refs :
      (update_with_extension r .root [.root_to_var x_var]
        (update_with_epsilon r r envL.pathEnv)).refs = r :: envL.pathEnv.refs := by
    rw [uwe_absorbs_epsilon r .root _ envL.pathEnv hr_fresh_pe (Ne.symm hr_ne_root),
        uwe_refs_fresh r .root _ envL.pathEnv hr_fresh_pe]
  apply typecheck_stmt.let_bind_borrowMut lenv env _ _ _ _ r' _ _
    hle hlook_env
    (SiteEnvSubstEquiv_notIn σ _ _ _ hse hnotIn)
    hr'_fresh_prop
  apply ih
  · -- subsumes
    rw [uwe_absorbs_epsilon r .root _ envL.pathEnv hr_fresh_pe (Ne.symm hr_ne_root),
        uwe_absorbs_epsilon r' .root _ env.pathEnv hr'_fresh_pe (Ne.symm hr'_not_root)]
    refine ⟨extendSubst σ r r',
      extendSubst_id σ r r' hid hr_refid,
      VarEnvSubstEquiv_extend σ r r' _ _ hve
        (fun x' bt' s' bk' ms' hlook' =>
          Ne.symm (freshRefInEnv_ne_varEnv_ref r _ x' .validVar bt' s' bk' ms' hfresh hlook')),
      SiteEnvSubstEquiv_extend_insert_ref σ r r' _ _ _ _ _ hse
        (fun k bt ref bk hlook' =>
          Ne.symm (freshRefInEnv_ne_siteEnv_ref r _ k bt ref bk hfresh hlook')),
      ?_, ?_, ?_, ?_⟩
    · -- refs
      simp only [uwe_refs_fresh r .root _ envL.pathEnv hr_fresh_pe,
          uwe_refs_fresh r' .root _ env.pathEnv hr'_fresh_pe]
      simp only [List.map, extendSubst, ite_true]
      congr 1
      rw [map_extendSubst_eq_map_σ σ r r' _ hr_fresh_pe, hrefs]
    · exact extendSubst_injective σ r r' _ hinj hr_fresh_pe hr'_not_mapped
    · exact extendSubst_nonroot σ r r' hnonroot hr'_not_root
    · have := path_inclusion_update_with_extension σ _ _ r r' .root
        [.root_to_var x_var] hpaths hr_fresh_pe hr'_not_mapped hroot
      rw [hσ_root] at this; exact this
  · exact hfuneq
  · exact ⟨update_with_extension_wellformed r .root [.root_to_var x_var]
            (update_with_epsilon r r envL.pathEnv)
            (update_with_epsilon_wellformed r r envL.pathEnv hwfL.pathEnv_wf hr_ne_root)
            hr_ne_root,
           SiteEnv.insert_refs_not_root _ _ _ hwfL.siteEnv_wf hr_ne_root,
           hwfL.varEnv_wf⟩
  · exact ⟨update_with_extension_wellformed r' .root [.root_to_var x_var]
            (update_with_epsilon r' r' env.pathEnv)
            (update_with_epsilon_wellformed r' r' env.pathEnv hwfE.pathEnv_wf hr'_not_root)
            hr'_not_root,
           SiteEnv.insert_refs_not_root _ _ _ hwfE.siteEnv_wf hr'_not_root,
           hwfE.varEnv_wf⟩
  · intro s' bt ref bk hlook_s'
    simp only [h_compound_refs]
    by_cases hs' : s' = a
    · subst hs'; rw [lookup_insert_same] at hlook_s'
      simp only [Option.some.injEq, MoveType.ref.injEq] at hlook_s'
      obtain ⟨-, rfl, -⟩ := hlook_s'
      exact .head _
    · rw [lookup_insert_ne _ _ _ _ hs'] at hlook_s'
      exact .tail _ (hsite_tracked _ _ _ _ hlook_s')
  · intro x' bt ref bk ms' hlook_x'
    simp only [h_compound_refs]
    exact .tail _ (hvar_tracked _ _ _ _ _ hlook_x')
  · exact RefsUnique_insert_fresh_ref _ _ _ _ _ _ huniq
      (fun x' bt' ref bk' ms' hlook' =>
        Ne.symm (freshRefInEnv_ne_varEnv_ref r _ x' .validVar bt' ref bk' ms' hfresh hlook'))
      (fun s' bt' ref bk' hlook' =>
        Ne.symm (freshRefInEnv_ne_siteEnv_ref r _ s' bt' ref bk' hfresh hlook'))
  · exact update_with_extension_paths_to_non_member r' .root [.root_to_var x_var] _
      (by unfold update_with_epsilon
          exact update_with_extension_paths_to_non_member r' r' [] env.pathEnv
            hpaths_to_nm (Or.inr rfl))
      (Or.inl (by rw [uwe_epsilon_refs_fresh r' r' env.pathEnv hr'_fresh_pe]
                  exact List.mem_cons_of_mem _ hwfE.pathEnv_wf.root_in_refs))
  · exact update_with_extension_paths_from_non_member r' .root [.root_to_var x_var] _
      (by unfold update_with_epsilon
          exact update_with_extension_paths_from_non_member r' r' [] env.pathEnv
            hpaths_from_nm (Or.inr rfl))
      (Or.inl (by rw [uwe_epsilon_refs_fresh r' r' env.pathEnv hr'_fresh_pe]
                  exact List.mem_cons_of_mem _ hwfE.pathEnv_wf.root_in_refs))
  · exact self_loop_only_empty_uwe _ _ _ _
      (by unfold update_with_epsilon
          exact self_loop_only_empty_uwe r' r' [] env.pathEnv hself_loop_only_empty)
  · simp only [h_compound_refs]
    exact .tail _ hroot

private theorem weaken_let_bind_borrowField
    (lenv : LabelEnv) (envL env : TypeEnv)
    (a af : Site) (f : Field) (bt bt' : BasicMoveType) (isBor : BorrowingKind)
    (fentries : AssocMap Field BasicMoveType) (s : Aref) (rf : Aref)
    (cont : Stmt) (retTypes : List ParamType)
    (hlookup_a : lookup envL.siteEnv a = some (.ref bt s isBor))
    (hbt : bt = .trecord fentries)
    (hlookup_f : lookup fentries f = some bt')
    (hnotIn : notIn envL.siteEnv af)
    (hfresh : freshRefInEnv rf envL)
    (hsub : TypeEnv.subsumes envL env)
    (hfuneq : envL.funEnv = env.funEnv)
    (hwfL : TypeEnv.WellFormed envL) (hwfE : TypeEnv.WellFormed env)
    (hsite_tracked : ∀ s bt r bk, lookup envL.siteEnv s = some (.ref bt r bk) → r ∈ envL.pathEnv.refs)
    (hvar_tracked : ∀ x bt r bk ms, lookup envL.varEnv x = some (.validVar, .ref bt r bk, ms) → r ∈ envL.pathEnv.refs)
    (huniq : RefsUnique envL.varEnv envL.siteEnv)
    (hpaths_to_nm : ∀ u v p, v ∉ env.pathEnv.refs → v ≠ .root → u ≠ v →
      ¬interpret_regex (env.pathEnv.paths (u, v)) p)
    (hpaths_from_nm : ∀ u v p, u ∉ env.pathEnv.refs → u ≠ .root → u ≠ v →
      ¬interpret_regex (env.pathEnv.paths (u, v)) p)
    (hself_loop_only_empty : ∀ u p, interpret_regex (env.pathEnv.paths (u, u)) p → p = [])
    (hroot : Aref.root ∈ envL.pathEnv.refs)
    (ih : WeakenIH lenv
        {envL with siteEnv := insert (delete envL.siteEnv a) af (.ref bt' rf isBor)
                   pathEnv := update_with_extension rf s [.field f] envL.pathEnv}
        cont retTypes) :
    typecheck_stmt lenv env (.letBind af (.borrowField a bt f) cont) retTypes := by
  obtain ⟨σ, hid, hve, hse, hrefs, hinj, hnonroot, hpaths⟩ := hsub
  -- Site lookup in env
  have hlook_a_env := SiteEnvSubstEquiv_lookup_some σ _ _ _ _ hse hlookup_a
  simp only [applySubstMoveType] at hlook_a_env
  -- Freshness of rf in envL
  have hrf_fresh_pe : rf ∉ envL.pathEnv.refs := freshRefInEnv_implies_freshRef rf envL hfresh
  have hrf_ne_root : rf ≠ .root := fun h => hrf_fresh_pe (h ▸ hroot)
  have hrf_not_varRef : ∀ v, rf ≠ .varRef v := (hfresh.2.2 : _ ∧ _).2
  have hrf_refid : ∃ n, rf = .refid n := by
    cases rf with
    | root => exact absurd rfl hrf_ne_root
    | refid n => exact ⟨n, rfl⟩
    | varRef v => exact absurd rfl (hrf_not_varRef v)
  -- Pick fresh rf' for env
  let rf' := nextFreshRefInEnv env
  have hrf'_fresh_prop := nextFreshRefInEnv_fresh_prop env
  have hrf'_fresh_pe := nextFreshRefInEnv_not_in_pathEnv env
  have hrf'_not_root := nextFreshRefInEnv_not_root env
  have hrf'_not_mapped : rf' ∉ envL.pathEnv.refs.map σ := by rw [hrefs]; exact hrf'_fresh_pe
  -- s ∈ envL.pathEnv.refs (from site_tracked)
  have hs_mem := hsite_tracked _ _ _ _ hlookup_a
  -- Apply borrowField rule
  apply typecheck_stmt.let_bind_borrowField lenv env a af f _ _ _ _ (σ s) rf' _ _
    hlook_a_env hbt hlookup_f
    (SiteEnvSubstEquiv_notIn σ _ _ _ hse hnotIn)
    hrf'_fresh_prop
  -- IH: need subsumes for modified envs
  apply ih
  · -- subsumes with extendSubst σ rf rf'
    refine ⟨extendSubst σ rf rf',
      extendSubst_id σ rf rf' hid hrf_refid,
      VarEnvSubstEquiv_extend σ rf rf' _ _ hve
        (fun x bt s' bk ms hlook' =>
          Ne.symm (freshRefInEnv_ne_varEnv_ref rf envL x .validVar bt s' bk ms hfresh hlook')),
      SiteEnvSubstEquiv_extend_insert_ref σ rf rf' _ _ af _ _
        (SiteEnvSubstEquiv_delete σ _ _ a hse)
        (fun k bt r bk hlook' => by
          by_cases hka : k = a
          · subst hka; rw [lookup_delete_same] at hlook'; cases hlook'
          · rw [lookup_delete_ne _ _ _ hka] at hlook'
            exact Ne.symm (freshRefInEnv_ne_siteEnv_ref rf envL k bt r bk hfresh hlook')),
      ?_, ?_, ?_, ?_⟩
    · -- refs
      simp only [uwe_refs_fresh rf s _ envL.pathEnv hrf_fresh_pe,
          uwe_refs_fresh rf' (σ s) _ env.pathEnv hrf'_fresh_pe]
      simp only [List.map, extendSubst, ite_true]
      congr 1
      rw [map_extendSubst_eq_map_σ σ rf rf' _ hrf_fresh_pe, hrefs]
    · -- injectivity
      exact extendSubst_injective σ rf rf' _ hinj hrf_fresh_pe hrf'_not_mapped
    · -- nonroot
      exact extendSubst_nonroot σ rf rf' hnonroot hrf'_not_root
    · -- path_inclusion
      exact path_inclusion_update_with_extension σ _ _ rf rf' s [.field f]
        hpaths hrf_fresh_pe hrf'_not_mapped hs_mem
  · exact hfuneq
  · -- WellFormed envL'
    exact ⟨update_with_extension_wellformed rf s [.field f] envL.pathEnv
            hwfL.pathEnv_wf hrf_ne_root,
           SiteEnv.insert_refs_not_root _ _ _
            (SiteEnv.delete_refs_not_root _ _ hwfL.siteEnv_wf) hrf_ne_root,
           hwfL.varEnv_wf⟩
  · -- WellFormed env'
    exact ⟨update_with_extension_wellformed rf' (σ s) [.field f] env.pathEnv
            hwfE.pathEnv_wf hrf'_not_root,
           SiteEnv.insert_refs_not_root _ _ _
            (SiteEnv.delete_refs_not_root _ _ hwfE.siteEnv_wf) hrf'_not_root,
           hwfE.varEnv_wf⟩
  · -- site_tracked
    intro s' bt_s r bk hlook_s'
    simp only [uwe_refs_fresh rf s _ envL.pathEnv hrf_fresh_pe]
    by_cases hs'_af : s' = af
    · subst hs'_af; rw [lookup_insert_same] at hlook_s'
      simp only [Option.some.injEq, MoveType.ref.injEq] at hlook_s'
      obtain ⟨-, rfl, -⟩ := hlook_s'
      exact .head _
    · rw [lookup_insert_ne _ _ _ _ hs'_af] at hlook_s'
      have hlook_orig : lookup envL.siteEnv s' = some (.ref bt_s r bk) := by
        by_cases hs'a : s' = a
        · subst hs'a; rw [lookup_delete_same] at hlook_s'; cases hlook_s'
        · rwa [lookup_delete_ne _ _ _ hs'a] at hlook_s'
      exact .tail _ (hsite_tracked _ _ _ _ hlook_orig)
  · -- var_tracked
    intro x bt r bk ms hlook_x
    simp only [uwe_refs_fresh rf s _ envL.pathEnv hrf_fresh_pe]
    exact .tail _ (hvar_tracked _ _ _ _ _ hlook_x)
  · -- RefsUnique
    exact RefsUnique_delete_insert_fresh_ref _ _ a af _ rf _ huniq
      (fun x bt r bk' ms hlook' =>
        Ne.symm (freshRefInEnv_ne_varEnv_ref rf envL x .validVar bt r bk' ms hfresh hlook'))
      (fun s' bt r bk' hlook' =>
        Ne.symm (freshRefInEnv_ne_siteEnv_ref rf envL s' bt r bk' hfresh hlook'))
  · exact update_with_extension_paths_to_non_member _ _ _ _ hpaths_to_nm
      (Or.inl (by rw [← hrefs]; exact List.mem_map_of_mem hs_mem))
  · exact update_with_extension_paths_from_non_member _ _ _ _ hpaths_from_nm
      (Or.inl (by rw [← hrefs]; exact List.mem_map_of_mem hs_mem))
  · exact self_loop_only_empty_uwe _ _ _ env.pathEnv hself_loop_only_empty
  · -- root ∈ updated refs
    simp only [uwe_refs_fresh rf s _ envL.pathEnv hrf_fresh_pe]
    exact .tail _ hroot

private theorem weaken_let_bind_borrowMutField
    (lenv : LabelEnv) (envL env : TypeEnv)
    (a af : Site) (f : Field) (bt btf : BasicMoveType)
    (fentries : AssocMap Field BasicMoveType) (s rf : Aref)
    (cont : Stmt) (retTypes : List ParamType)
    (hlookup_a : lookup envL.siteEnv a = some (.ref bt s .siteBorrowMut))
    (hbt : bt = .trecord fentries)
    (hlookup_f : lookup fentries f = some btf)
    (hnotIn : notIn envL.siteEnv af)
    (hfresh : freshRefInEnv rf envL)
    (hsub : TypeEnv.subsumes envL env)
    (hfuneq : envL.funEnv = env.funEnv)
    (hwfL : TypeEnv.WellFormed envL) (hwfE : TypeEnv.WellFormed env)
    (hsite_tracked : ∀ s bt r bk, lookup envL.siteEnv s = some (.ref bt r bk) → r ∈ envL.pathEnv.refs)
    (hvar_tracked : ∀ x bt r bk ms, lookup envL.varEnv x = some (.validVar, .ref bt r bk, ms) → r ∈ envL.pathEnv.refs)
    (huniq : RefsUnique envL.varEnv envL.siteEnv)
    (hpaths_to_nm : ∀ u v p, v ∉ env.pathEnv.refs → v ≠ .root → u ≠ v →
      ¬interpret_regex (env.pathEnv.paths (u, v)) p)
    (hpaths_from_nm : ∀ u v p, u ∉ env.pathEnv.refs → u ≠ .root → u ≠ v →
      ¬interpret_regex (env.pathEnv.paths (u, v)) p)
    (hself_loop_only_empty : ∀ u p, interpret_regex (env.pathEnv.paths (u, u)) p → p = [])
    (hroot : Aref.root ∈ envL.pathEnv.refs)
    (ih : WeakenIH lenv
        {envL with siteEnv := insert (delete envL.siteEnv a) af (.ref btf rf .siteBorrowMut)
                   pathEnv := update_with_extension rf s [.field f] envL.pathEnv}
        cont retTypes) :
    typecheck_stmt lenv env (.letBind af (.borrowMutField a bt f) cont) retTypes := by
  obtain ⟨σ, hid, hve, hse, hrefs, hinj, hnonroot, hpaths⟩ := hsub
  have hlook_a_env := SiteEnvSubstEquiv_lookup_some σ _ _ _ _ hse hlookup_a
  simp only [applySubstMoveType] at hlook_a_env
  have hrf_fresh_pe : rf ∉ envL.pathEnv.refs := freshRefInEnv_implies_freshRef rf envL hfresh
  have hrf_ne_root : rf ≠ .root := fun h => hrf_fresh_pe (h ▸ hroot)
  have hrf_not_varRef : ∀ v, rf ≠ .varRef v := (hfresh.2.2 : _ ∧ _).2
  have hrf_refid : ∃ n, rf = .refid n := by
    cases rf with
    | root => exact absurd rfl hrf_ne_root
    | refid n => exact ⟨n, rfl⟩
    | varRef v => exact absurd rfl (hrf_not_varRef v)
  let rf' := nextFreshRefInEnv env
  have hrf'_fresh_prop := nextFreshRefInEnv_fresh_prop env
  have hrf'_fresh_pe := nextFreshRefInEnv_not_in_pathEnv env
  have hrf'_not_root := nextFreshRefInEnv_not_root env
  have hrf'_not_mapped : rf' ∉ envL.pathEnv.refs.map σ := by rw [hrefs]; exact hrf'_fresh_pe
  have hs_mem := hsite_tracked _ _ _ _ hlookup_a
  apply typecheck_stmt.let_bind_borrowMutField lenv env a af f _ _ _ (σ s) rf' _ _
    hlook_a_env hbt hlookup_f
    (SiteEnvSubstEquiv_notIn σ _ _ _ hse hnotIn)
    hrf'_fresh_prop
  apply ih
  · -- subsumes
    refine ⟨extendSubst σ rf rf',
      extendSubst_id σ rf rf' hid hrf_refid,
      VarEnvSubstEquiv_extend σ rf rf' _ _ hve
        (fun x bt s' bk ms hlook' =>
          Ne.symm (freshRefInEnv_ne_varEnv_ref rf envL x .validVar bt s' bk ms hfresh hlook')),
      SiteEnvSubstEquiv_extend_insert_ref σ rf rf' _ _ af _ _
        (SiteEnvSubstEquiv_delete σ _ _ a hse)
        (fun k bt r bk hlook' => by
          by_cases hka : k = a
          · subst hka; rw [lookup_delete_same] at hlook'; cases hlook'
          · rw [lookup_delete_ne _ _ _ hka] at hlook'
            exact Ne.symm (freshRefInEnv_ne_siteEnv_ref rf envL k bt r bk hfresh hlook')),
      ?_, ?_, ?_, ?_⟩
    · simp only [uwe_refs_fresh rf s _ envL.pathEnv hrf_fresh_pe,
          uwe_refs_fresh rf' (σ s) _ env.pathEnv hrf'_fresh_pe]
      simp only [List.map, extendSubst, ite_true]
      congr 1
      rw [map_extendSubst_eq_map_σ σ rf rf' _ hrf_fresh_pe, hrefs]
    · exact extendSubst_injective σ rf rf' _ hinj hrf_fresh_pe hrf'_not_mapped
    · exact extendSubst_nonroot σ rf rf' hnonroot hrf'_not_root
    · exact path_inclusion_update_with_extension σ _ _ rf rf' s [.field f]
        hpaths hrf_fresh_pe hrf'_not_mapped hs_mem
  · exact hfuneq
  · exact ⟨update_with_extension_wellformed rf s [.field f] envL.pathEnv
            hwfL.pathEnv_wf hrf_ne_root,
           SiteEnv.insert_refs_not_root _ _ _
            (SiteEnv.delete_refs_not_root _ _ hwfL.siteEnv_wf) hrf_ne_root,
           hwfL.varEnv_wf⟩
  · exact ⟨update_with_extension_wellformed rf' (σ s) [.field f] env.pathEnv
            hwfE.pathEnv_wf hrf'_not_root,
           SiteEnv.insert_refs_not_root _ _ _
            (SiteEnv.delete_refs_not_root _ _ hwfE.siteEnv_wf) hrf'_not_root,
           hwfE.varEnv_wf⟩
  · intro s' bt_s r bk hlook_s'
    simp only [uwe_refs_fresh rf s _ envL.pathEnv hrf_fresh_pe]
    by_cases hs'_af : s' = af
    · subst hs'_af; rw [lookup_insert_same] at hlook_s'
      simp only [Option.some.injEq, MoveType.ref.injEq] at hlook_s'
      obtain ⟨-, rfl, -⟩ := hlook_s'
      exact .head _
    · rw [lookup_insert_ne _ _ _ _ hs'_af] at hlook_s'
      have hlook_orig : lookup envL.siteEnv s' = some (.ref bt_s r bk) := by
        by_cases hs'a : s' = a
        · subst hs'a; rw [lookup_delete_same] at hlook_s'; cases hlook_s'
        · rwa [lookup_delete_ne _ _ _ hs'a] at hlook_s'
      exact .tail _ (hsite_tracked _ _ _ _ hlook_orig)
  · intro x bt r bk ms hlook_x
    simp only [uwe_refs_fresh rf s _ envL.pathEnv hrf_fresh_pe]
    exact .tail _ (hvar_tracked _ _ _ _ _ hlook_x)
  · exact RefsUnique_delete_insert_fresh_ref _ _ a af _ rf _ huniq
      (fun x bt r bk' ms hlook' =>
        Ne.symm (freshRefInEnv_ne_varEnv_ref rf envL x .validVar bt r bk' ms hfresh hlook'))
      (fun s' bt r bk' hlook' =>
        Ne.symm (freshRefInEnv_ne_siteEnv_ref rf envL s' bt r bk' hfresh hlook'))
  · exact update_with_extension_paths_to_non_member _ _ _ _ hpaths_to_nm
      (Or.inl (by rw [← hrefs]; exact List.mem_map_of_mem hs_mem))
  · exact update_with_extension_paths_from_non_member _ _ _ _ hpaths_from_nm
      (Or.inl (by rw [← hrefs]; exact List.mem_map_of_mem hs_mem))
  · exact self_loop_only_empty_uwe _ _ _ env.pathEnv hself_loop_only_empty
  · simp only [uwe_refs_fresh rf s _ envL.pathEnv hrf_fresh_pe]
    exact .tail _ hroot

private theorem weaken_let_bind_freeze
    (lenv : LabelEnv) (envL env : TypeEnv)
    (a c : Site) (τ : BasicMoveType) (r r' : Aref) (isBor : BorrowingKind)
    (cont : Stmt) (retTypes : List ParamType)
    (hlook : lookup envL.siteEnv a = some (.ref τ r isBor))
    (hnotIn : notIn envL.siteEnv c)
    (hfresh : freshRefInEnv r' envL)
    (hsub : TypeEnv.subsumes envL env)
    (hfuneq : envL.funEnv = env.funEnv)
    (hwfL : TypeEnv.WellFormed envL) (hwfE : TypeEnv.WellFormed env)
    (hsite_tracked : ∀ s bt r bk, lookup envL.siteEnv s = some (.ref bt r bk) → r ∈ envL.pathEnv.refs)
    (hvar_tracked : ∀ x bt r bk ms, lookup envL.varEnv x = some (.validVar, .ref bt r bk, ms) → r ∈ envL.pathEnv.refs)
    (huniq : RefsUnique envL.varEnv envL.siteEnv)
    (hpaths_to_nm : ∀ u v p, v ∉ env.pathEnv.refs → v ≠ .root → u ≠ v →
      ¬interpret_regex (env.pathEnv.paths (u, v)) p)
    (hpaths_from_nm : ∀ u v p, u ∉ env.pathEnv.refs → u ≠ .root → u ≠ v →
      ¬interpret_regex (env.pathEnv.paths (u, v)) p)
    (hself_loop_only_empty : ∀ u p, interpret_regex (env.pathEnv.paths (u, u)) p → p = [])
    (hroot : Aref.root ∈ envL.pathEnv.refs)
    (ih : WeakenIH lenv
        {envL with siteEnv := insert (delete envL.siteEnv a) c (.ref τ r' .siteBorrowImm)
                   pathEnv := consume_ref_transfer envL.pathEnv r r'}
        cont retTypes) :
    typecheck_stmt lenv env (.letBind c (.freeze a) cont) retTypes := by
  obtain ⟨σ, hid, hve, hse, hrefs, hinj, hnonroot, hpaths⟩ := hsub
  -- Site lookup in env
  have hlook_env := SiteEnvSubstEquiv_lookup_some σ _ _ _ _ hse hlook
  simp only [applySubstMoveType] at hlook_env
  -- r ≠ .root from SiteEnv well-formedness
  have hr_ne_root : r ≠ .root := hwfL.siteEnv_wf _ _ hlook
  -- Freshness of r' in envL
  have hr'_fresh_pe : r' ∉ envL.pathEnv.refs := freshRefInEnv_implies_freshRef r' envL hfresh
  have hr'_ne_root : r' ≠ .root := fun h => hr'_fresh_pe (h ▸ hroot)
  have hr'_not_varRef : ∀ v, r' ≠ .varRef v := (hfresh.2.2 : _ ∧ _).2
  have hr'_refid : ∃ n, r' = .refid n := by
    cases r' with
    | root => exact absurd rfl hr'_ne_root
    | refid n => exact ⟨n, rfl⟩
    | varRef v => exact absurd rfl (hr'_not_varRef v)
  -- r is tracked in envL (from site_tracked + lookup)
  have hr_mem : r ∈ envL.pathEnv.refs := hsite_tracked _ _ _ _ hlook
  have hr_ne_r' : r ≠ r' := fun h => hr'_fresh_pe (h ▸ hr_mem)
  -- Pick fresh r'' for env
  let r'' := nextFreshRefInEnv env
  have hr''_fresh_prop := nextFreshRefInEnv_fresh_prop env
  have hr''_fresh_pe := nextFreshRefInEnv_not_in_pathEnv env
  have hr''_not_root := nextFreshRefInEnv_not_root env
  have hr''_not_varRef := nextFreshRefInEnv_not_varRef env
  have hr''_not_mapped : r'' ∉ envL.pathEnv.refs.map σ := by rw [hrefs]; exact hr''_fresh_pe
  -- σ r ∈ env.pathEnv.refs
  have hσr_mem : σ r ∈ env.pathEnv.refs := by rw [← hrefs]; exact List.mem_map_of_mem hr_mem
  -- r'' ≠ σ r
  have hr''_ne_σr : r'' ≠ σ r := by intro heq; rw [← heq] at hσr_mem; exact hr''_fresh_pe hσr_mem
  -- Apply freeze rule
  apply typecheck_stmt.let_bind_freeze lenv env _ _ _ _ r'' _ _ _
    hlook_env
    (SiteEnvSubstEquiv_notIn σ _ _ _ hse hnotIn)
    hr''_fresh_prop
  -- IH: need subsumes for modified envs
  apply ih
  · -- subsumes with extendSubst σ r' r''
    refine ⟨extendSubst σ r' r'',
      extendSubst_id σ r' r'' hid hr'_refid,
      VarEnvSubstEquiv_extend σ r' r'' _ _ hve
        (fun x' bt' s' bk' ms' hlook' =>
          Ne.symm (freshRefInEnv_ne_varEnv_ref r' envL x' .validVar bt' s' bk' ms' hfresh hlook')),
      SiteEnvSubstEquiv_extend_insert_ref σ r' r'' _ _ c τ .siteBorrowImm
        (SiteEnvSubstEquiv_delete σ _ _ a hse)
        (fun k bt ref bk hlook' => by
          by_cases hka : k = a
          · subst hka; rw [lookup_delete_same] at hlook'; cases hlook'
          · rw [lookup_delete_ne _ _ _ hka] at hlook'
            exact Ne.symm (freshRefInEnv_ne_siteEnv_ref r' envL k bt ref bk hfresh hlook')),
      ?_, ?_, ?_, ?_⟩
    · -- refs
      rw [crt_refs_fresh envL.pathEnv r r' hr'_fresh_pe (Ne.symm hr_ne_r'),
          crt_refs_fresh env.pathEnv (σ r) r'' hr''_fresh_pe hr''_ne_σr]
      simp only [List.map, extendSubst, ite_true]
      congr 1
      rw [map_extendSubst_eq_map_σ σ r' r'' _
            (fun h => hr'_fresh_pe ((List.mem_filter.mp h).1)),
          map_filter_ne σ _ r hinj hr_mem, hrefs]
    · -- injectivity
      have key := extendSubst_injective σ r' r'' _ hinj hr'_fresh_pe hr''_not_mapped
      simp only [if_pos hr'_fresh_pe] at key
      intro u v hu hv heq_uv
      rw [crt_refs_fresh envL.pathEnv r r' hr'_fresh_pe (Ne.symm hr_ne_r')] at hu hv
      apply key
      · exact List.mem_cons.mpr ((List.mem_cons.mp hu).imp id (fun h => (List.mem_filter.mp h).1))
      · exact List.mem_cons.mpr ((List.mem_cons.mp hv).imp id (fun h => (List.mem_filter.mp h).1))
      · exact heq_uv
    · -- nonroot
      exact extendSubst_nonroot σ r' r'' hnonroot hr''_not_root
    · -- path_inclusion
      exact path_inclusion_consume_ref_transfer σ envL.pathEnv env.pathEnv r r' r''
        hpaths hr_mem hr'_fresh_pe hr''_fresh_pe hr''_not_mapped hinj
        (Ne.symm hr_ne_r') hr''_ne_σr hr''_not_root
        hself_loop_only_empty hpaths_from_nm hpaths_to_nm
        hwfL.pathEnv_wf.self_loop_accepts_nil
  · exact hfuneq
  · -- WellFormed envL'
    exact ⟨consume_ref_transfer_wellformed envL.pathEnv r r'
            hwfL.pathEnv_wf hr_ne_root hr'_fresh_pe hr'_not_varRef,
           SiteEnv.insert_refs_not_root _ _ _
            (SiteEnv.delete_refs_not_root _ _ hwfL.siteEnv_wf) hr'_ne_root,
           hwfL.varEnv_wf⟩
  · -- WellFormed env'
    exact ⟨consume_ref_transfer_wellformed env.pathEnv (σ r) r''
            hwfE.pathEnv_wf (hnonroot r hr_ne_root) hr''_fresh_pe
            (fun v => hr''_not_varRef v),
           SiteEnv.insert_refs_not_root _ _ _
            (SiteEnv.delete_refs_not_root _ _ hwfE.siteEnv_wf) hr''_not_root,
           hwfE.varEnv_wf⟩
  · -- site_tracked
    intro s' bt_s ref bk hlook_s'
    by_cases hs'c : s' = c
    · subst hs'c; rw [lookup_insert_same] at hlook_s'
      simp only [Option.some.injEq, MoveType.ref.injEq] at hlook_s'
      obtain ⟨-, rfl, -⟩ := hlook_s'
      rw [crt_refs_fresh envL.pathEnv r r' hr'_fresh_pe (Ne.symm hr_ne_r')]
      exact .head _
    · rw [lookup_insert_ne _ _ _ _ hs'c] at hlook_s'
      by_cases hs'a : s' = a
      · subst hs'a; rw [lookup_delete_same] at hlook_s'; cases hlook_s'
      · rw [lookup_delete_ne _ _ _ hs'a] at hlook_s'
        have href_mem := hsite_tracked _ _ _ _ hlook_s'
        have href_ne_r : ref ≠ r := by
          intro heq; rw [heq] at hlook_s'
          exact (huniq r).2.1 s' a bt_s τ bk isBor hs'a hlook_s' hlook
        rw [crt_refs_fresh envL.pathEnv r r' hr'_fresh_pe (Ne.symm hr_ne_r')]
        exact .tail _ (List.mem_filter.mpr ⟨href_mem, decide_eq_true_eq.mpr href_ne_r⟩)
  · -- var_tracked
    intro x bt ref bk ms hlook_x
    have href_mem := hvar_tracked _ _ _ _ _ hlook_x
    have href_ne_r : ref ≠ r := by
      intro heq; rw [heq] at hlook_x
      exact (huniq r).1 x bt bk ms a τ isBor hlook_x hlook
    rw [crt_refs_fresh envL.pathEnv r r' hr'_fresh_pe (Ne.symm hr_ne_r')]
    exact .tail _ (List.mem_filter.mpr ⟨href_mem, decide_eq_true_eq.mpr href_ne_r⟩)
  · -- RefsUnique
    exact RefsUnique_delete_insert_fresh_ref _ _ a c _ r' _ huniq
      (fun x bt ref bk' ms hlook' =>
        Ne.symm (freshRefInEnv_ne_varEnv_ref r' envL x .validVar bt ref bk' ms hfresh hlook'))
      (fun s' bt ref bk' hlook' =>
        Ne.symm (freshRefInEnv_ne_siteEnv_ref r' envL s' bt ref bk' hfresh hlook'))
  · -- hpaths_to_nm
    exact consume_ref_transfer_paths_to_non_member env.pathEnv (σ r) r'' hpaths_to_nm
  · -- hpaths_from_nm
    exact consume_ref_transfer_paths_from_non_member env.pathEnv (σ r) r'' hpaths_from_nm
  · exact self_loop_only_empty_crt env.pathEnv (σ r) r'' hself_loop_only_empty
      hpaths_from_nm hr''_fresh_pe hr''_not_root hr''_ne_σr
  · -- root ∈ updated refs
    rw [crt_refs_fresh envL.pathEnv r r' hr'_fresh_pe (Ne.symm hr_ne_r')]
    exact .tail _ (List.mem_filter.mpr ⟨hroot, decide_eq_true_eq.mpr (Ne.symm hr_ne_root)⟩)

private theorem weaken_var_assign_valid
    (lenv : LabelEnv) (envL env : TypeEnv)
    (x : Var) (a ax : Site) (τ : BasicMoveType) (ms : Mut) (r : Aref)
    (cont : Stmt) (retTypes : List ParamType)
    (hms : LE.le .mutable ms)
    (hlook_x : lookup envL.varEnv x = some (.validVar, .basic τ, ms))
    (hlook_a : lookup envL.siteEnv a = some (.basic τ))
    (hnotIn : notIn envL.siteEnv ax)
    (hfresh : freshRefInEnv r envL)
    (hsub : TypeEnv.subsumes envL env)
    (hfuneq : envL.funEnv = env.funEnv)
    (hwfL : TypeEnv.WellFormed envL) (hwfE : TypeEnv.WellFormed env)
    (hsite_tracked : ∀ s bt r bk, lookup envL.siteEnv s = some (.ref bt r bk) → r ∈ envL.pathEnv.refs)
    (hvar_tracked : ∀ x bt r bk ms, lookup envL.varEnv x = some (.validVar, .ref bt r bk, ms) → r ∈ envL.pathEnv.refs)
    (huniq : RefsUnique envL.varEnv envL.siteEnv)
    (hpaths_to_nm : ∀ u v p, v ∉ env.pathEnv.refs → v ≠ .root → u ≠ v →
      ¬interpret_regex (env.pathEnv.paths (u, v)) p)
    (hpaths_from_nm : ∀ u v p, u ∉ env.pathEnv.refs → u ≠ .root → u ≠ v →
      ¬interpret_regex (env.pathEnv.paths (u, v)) p)
    (hself_loop_only_empty : ∀ u p, interpret_regex (env.pathEnv.paths (u, u)) p → p = [])
    (hroot : Aref.root ∈ envL.pathEnv.refs)
    (ih : WeakenIH lenv
        {envL with siteEnv := delete (delete (insert envL.siteEnv ax (.ref τ r .siteBorrowMut)) a) ax
                   pathEnv := garbage_collect (update_with_extension r .root [.root_to_var x] (update_with_epsilon r r envL.pathEnv)) r}
        cont retTypes) :
    typecheck_stmt lenv env (.assign x a cont) retTypes := by
  obtain ⟨σ, hid, hve, hse, hrefs, hinj, hnonroot, hpaths⟩ := hsub
  -- Var lookup in env (basic type, so σ doesn't affect it)
  have hlook_x_env := VarEnvSubstEquiv_lookup_valid σ _ _ _ _ _ hve hlook_x
  simp only [applySubstMoveType] at hlook_x_env
  -- Site lookup in env (basic type)
  have hlook_a_env := SiteEnvSubstEquiv_lookup_some σ _ _ _ _ hse hlook_a
  simp only [applySubstMoveType] at hlook_a_env
  -- r freshness in envL
  have hr_fresh_pe : r ∉ envL.pathEnv.refs := freshRefInEnv_implies_freshRef r envL hfresh
  have hr_ne_root : r ≠ .root := fun h => hr_fresh_pe (h ▸ hroot)
  -- Pick fresh r'' for env
  let r'' := nextFreshRefInEnv env
  have hr''_fresh_prop := nextFreshRefInEnv_fresh_prop env
  have hr''_fresh_pe := nextFreshRefInEnv_not_in_pathEnv env
  have hr''_not_root := nextFreshRefInEnv_not_root env
  have hr''_not_varRef := nextFreshRefInEnv_not_varRef env
  -- Apply var_assign_valid rule for env with r''
  apply typecheck_stmt.var_assign_valid lenv env _ _ ax τ _ r'' _ _
    hms hlook_x_env hlook_a_env
    (SiteEnvSubstEquiv_notIn σ _ _ _ hse hnotIn)
    hr''_fresh_prop
  -- IH: need subsumes for modified envs
  apply ih
  · -- subsumes: use σ directly (r/r'' are gc'd, pathEnv reverts to original refs/paths)
    refine ⟨σ, hid, hve,
      SiteEnvSubstEquiv_delete_delete_insert σ _ _ ax a _ _ hse,
      ?_, ?_, hnonroot, ?_⟩
    · -- refs: gc refs = pe.refs on both sides
      rw [gc_uwe_eps_refs_eq envL.pathEnv r .root [.root_to_var x] hr_fresh_pe,
          gc_uwe_eps_refs_eq env.pathEnv r'' .root [.root_to_var x] hr''_fresh_pe]
      exact hrefs
    · -- injectivity: same as original (refs unchanged after gc)
      intro u v hu hv heq_uv
      rw [gc_uwe_eps_refs_eq envL.pathEnv r .root [.root_to_var x] hr_fresh_pe] at hu hv
      exact hinj u v hu hv heq_uv
    · -- path_inclusion: gc+uwe+eps paths for non-r = original paths
      intro u v hu hv path hinterp
      rw [gc_uwe_eps_refs_eq envL.pathEnv r .root _ hr_fresh_pe] at hu hv
      have hu_ne : u ≠ r := fun h => hr_fresh_pe (h ▸ hu)
      have hv_ne : v ≠ r := fun h => hr_fresh_pe (h ▸ hv)
      have hσu_ne : σ u ≠ r'' := by
        intro h
        have : σ u ∈ env.pathEnv.refs := by rw [← hrefs]; exact List.mem_map_of_mem (f := σ) hu
        rw [h] at this; exact hr''_fresh_pe this
      have hσv_ne : σ v ≠ r'' := by
        intro h
        have : σ v ∈ env.pathEnv.refs := by rw [← hrefs]; exact List.mem_map_of_mem (f := σ) hv
        rw [h] at this; exact hr''_fresh_pe this
      simp only [garbage_collect] at hinterp ⊢
      rw [if_neg (fun ⟨h, _⟩ => hu_ne h), if_neg (not_or.mpr ⟨hu_ne, hv_ne⟩)]
      rw [if_neg (fun ⟨h, _⟩ => hσu_ne h), if_neg (not_or.mpr ⟨hσu_ne, hσv_ne⟩)] at hinterp
      rw [uwe_eps_paths_not_r envL.pathEnv r .root [.root_to_var x] u v hu_ne hv_ne]
      rw [uwe_eps_paths_not_r env.pathEnv r'' .root [.root_to_var x] (σ u) (σ v) hσu_ne hσv_ne] at hinterp
      exact hpaths u v hu hv path hinterp
  · exact hfuneq
  · -- WellFormed envL'
    exact ⟨garbage_collect_wellformed _ _ (update_with_extension_wellformed r .root [.root_to_var x] _
            (update_with_extension_wellformed r r [] envL.pathEnv hwfL.pathEnv_wf hr_ne_root)
            hr_ne_root) hr_ne_root,
          SiteEnv.delete_refs_not_root _ _
            (SiteEnv.delete_refs_not_root _ _
              (SiteEnv.insert_refs_not_root _ _ _ hwfL.siteEnv_wf hr_ne_root)),
          hwfL.varEnv_wf⟩
  · -- WellFormed env'
    exact ⟨garbage_collect_wellformed _ _ (update_with_extension_wellformed r'' .root [.root_to_var x] _
            (update_with_extension_wellformed r'' r'' [] env.pathEnv hwfE.pathEnv_wf hr''_not_root)
            hr''_not_root) hr''_not_root,
          SiteEnv.delete_refs_not_root _ _
            (SiteEnv.delete_refs_not_root _ _
              (SiteEnv.insert_refs_not_root _ _ _ hwfE.siteEnv_wf hr''_not_root)),
          hwfE.varEnv_wf⟩
  · -- site_tracked: refs in gc'd pathEnv = envL.pe.refs
    intro s' bt' ref bk' hlook_s'
    rw [gc_uwe_eps_refs_eq envL.pathEnv r .root [.root_to_var x] hr_fresh_pe]
    by_cases hs'_ax : s' = ax
    · subst hs'_ax; rw [lookup_delete_same] at hlook_s'; cases hlook_s'
    · rw [lookup_delete_ne _ _ _ hs'_ax] at hlook_s'
      by_cases hs'_a : s' = a
      · subst hs'_a; rw [lookup_delete_same] at hlook_s'; cases hlook_s'
      · rw [lookup_delete_ne _ _ _ hs'_a, lookup_insert_ne _ _ _ _ hs'_ax] at hlook_s'
        exact hsite_tracked _ _ _ _ hlook_s'
  · -- var_tracked: varEnv unchanged, pathEnv refs unchanged
    intro x' bt' ref bk' ms' hlook_x'
    rw [gc_uwe_eps_refs_eq envL.pathEnv r .root [.root_to_var x] hr_fresh_pe]
    exact hvar_tracked _ _ _ _ _ hlook_x'
  · -- RefsUnique: insert then double-delete
    exact RefsUnique_delete_site _ _ _
      (RefsUnique_delete_site _ _ _
        (RefsUnique_insert_fresh_ref _ _ ax _ r .siteBorrowMut huniq
          (fun x' bt' r' bk' ms' hlook' =>
            Ne.symm (freshRefInEnv_ne_varEnv_ref r envL x' .validVar bt' r' bk' ms' hfresh hlook'))
          (fun s' bt' r' bk' hlook' =>
            Ne.symm (freshRefInEnv_ne_siteEnv_ref r envL s' bt' r' bk' hfresh hlook'))))
  · -- hpaths_to_nm: thread through uwe/eps/gc
    exact garbage_collect_paths_to_non_member _ _
      (update_with_extension_paths_to_non_member r'' .root [.root_to_var x] _
        (by unfold update_with_epsilon
            exact update_with_extension_paths_to_non_member r'' r'' [] env.pathEnv
              hpaths_to_nm (Or.inr rfl))
        (Or.inl (by rw [uwe_epsilon_refs_fresh r'' r'' env.pathEnv hr''_fresh_pe]
                    exact List.mem_cons_of_mem _ hwfE.pathEnv_wf.root_in_refs)))
  · -- hpaths_from_nm: thread through uwe/eps/gc
    exact garbage_collect_paths_from_non_member _ _
      (update_with_extension_paths_from_non_member r'' .root [.root_to_var x] _
        (by unfold update_with_epsilon
            exact update_with_extension_paths_from_non_member r'' r'' [] env.pathEnv
              hpaths_from_nm (Or.inr rfl))
        (Or.inl (by rw [uwe_epsilon_refs_fresh r'' r'' env.pathEnv hr''_fresh_pe]
                    exact List.mem_cons_of_mem _ hwfE.pathEnv_wf.root_in_refs)))
  · exact self_loop_only_empty_gc _ _
      (self_loop_only_empty_uwe _ _ _ _
        (by unfold update_with_epsilon
            exact self_loop_only_empty_uwe r'' r'' [] env.pathEnv hself_loop_only_empty))
  · -- root ∈ gc'd refs = envL.pe.refs
    rw [gc_uwe_eps_refs_eq envL.pathEnv r .root [.root_to_var x] hr_fresh_pe]
    exact hroot

private theorem weaken_let_bind_intLit
    (lenv : LabelEnv) (envL env : TypeEnv)
    (a : Site) (n : Nat)
    (cont : Stmt) (retTypes : List ParamType)
    (hnotIn : notIn envL.siteEnv a)
    (hsub : TypeEnv.subsumes envL env)
    (hfuneq : envL.funEnv = env.funEnv)
    (hwfL : TypeEnv.WellFormed envL) (hwfE : TypeEnv.WellFormed env)
    (hsite_tracked : ∀ s bt r bk, lookup envL.siteEnv s = some (.ref bt r bk) → r ∈ envL.pathEnv.refs)
    (hvar_tracked : ∀ x bt r bk ms, lookup envL.varEnv x = some (.validVar, .ref bt r bk, ms) → r ∈ envL.pathEnv.refs)
    (huniq : RefsUnique envL.varEnv envL.siteEnv)
    (hpaths_to_nm : ∀ u v p, v ∉ env.pathEnv.refs → v ≠ .root → u ≠ v →
      ¬interpret_regex (env.pathEnv.paths (u, v)) p)
    (hpaths_from_nm : ∀ u v p, u ∉ env.pathEnv.refs → u ≠ .root → u ≠ v →
      ¬interpret_regex (env.pathEnv.paths (u, v)) p)
    (hself_loop_only_empty : ∀ u p, interpret_regex (env.pathEnv.paths (u, u)) p → p = [])
    (hroot : Aref.root ∈ envL.pathEnv.refs)
    (ih : WeakenIH lenv
        {envL with siteEnv := insert envL.siteEnv a (.basic .u64)}
        cont retTypes) :
    typecheck_stmt lenv env (.letBind a (.intLit n) cont) retTypes := by
  obtain ⟨σ, hid, hve, hse, hrefs, hinj, hnonroot, hpaths⟩ := hsub
  apply typecheck_stmt.let_bind_intLit
  · exact SiteEnvSubstEquiv_notIn σ _ _ _ hse hnotIn
  · apply ih
    · exact ⟨σ, hid, hve,
        SiteEnvSubstEquiv_insert σ _ _ _ _ _ hse (applySubstMoveType_basic σ _),
        hrefs, hinj, hnonroot, hpaths⟩
    · exact hfuneq
    · exact TypeEnv.insert_siteEnv_wf _ _ _ hwfL trivial
    · exact TypeEnv.insert_siteEnv_wf _ _ _ hwfE trivial
    · exact site_tracked_insert_basic _ _ _ _ hsite_tracked
    · exact hvar_tracked
    · exact RefsUnique_insert_basic _ _ _ _ huniq
    · exact hpaths_to_nm
    · exact hpaths_from_nm
    · exact hself_loop_only_empty
    · exact hroot

private theorem weaken_let_bind_copy_val
    (lenv : LabelEnv) (envL env : TypeEnv)
    (a : Site) (x : Var) (bt : BasicMoveType) (ms : Mut)
    (cont : Stmt) (retTypes : List ParamType)
    (hlookup : lookup envL.varEnv x = some (.validVar, .basic bt, ms))
    (hnotIn : notIn envL.siteEnv a)
    (hsub : TypeEnv.subsumes envL env)
    (hfuneq : envL.funEnv = env.funEnv)
    (hwfL : TypeEnv.WellFormed envL) (hwfE : TypeEnv.WellFormed env)
    (hsite_tracked : ∀ s bt r bk, lookup envL.siteEnv s = some (.ref bt r bk) → r ∈ envL.pathEnv.refs)
    (hvar_tracked : ∀ x bt r bk ms, lookup envL.varEnv x = some (.validVar, .ref bt r bk, ms) → r ∈ envL.pathEnv.refs)
    (huniq : RefsUnique envL.varEnv envL.siteEnv)
    (hpaths_to_nm : ∀ u v p, v ∉ env.pathEnv.refs → v ≠ .root → u ≠ v →
      ¬interpret_regex (env.pathEnv.paths (u, v)) p)
    (hpaths_from_nm : ∀ u v p, u ∉ env.pathEnv.refs → u ≠ .root → u ≠ v →
      ¬interpret_regex (env.pathEnv.paths (u, v)) p)
    (hself_loop_only_empty : ∀ u p, interpret_regex (env.pathEnv.paths (u, u)) p → p = [])
    (hroot : Aref.root ∈ envL.pathEnv.refs)
    (ih : WeakenIH lenv
        {envL with siteEnv := insert envL.siteEnv a (.basic bt)}
        cont retTypes) :
    typecheck_stmt lenv env (.letBind a (.usage (.copy x)) cont) retTypes := by
  obtain ⟨σ, hid, hve, hse, hrefs, hinj, hnonroot, hpaths⟩ := hsub
  have hlook_env := VarEnvSubstEquiv_lookup_valid σ _ _ _ _ _ hve hlookup
  simp only [applySubstMoveType] at hlook_env
  apply typecheck_stmt.let_bind_copy_val lenv env _ _ _ _ _ _
    hlook_env
    (SiteEnvSubstEquiv_notIn σ _ _ _ hse hnotIn)
  apply ih
  · exact ⟨σ, hid, hve,
      SiteEnvSubstEquiv_insert σ _ _ _ _ _ hse (applySubstMoveType_basic σ _),
      hrefs, hinj, hnonroot, hpaths⟩
  · exact hfuneq
  · exact TypeEnv.insert_siteEnv_wf _ _ _ hwfL trivial
  · exact TypeEnv.insert_siteEnv_wf _ _ _ hwfE trivial
  · exact site_tracked_insert_basic _ _ _ _ hsite_tracked
  · exact hvar_tracked
  · exact RefsUnique_insert_basic _ _ _ _ huniq
  · exact hpaths_to_nm
  · exact hpaths_from_nm
  · exact hself_loop_only_empty
  · exact hroot

private theorem weaken_let_bind_move
    (lenv : LabelEnv) (envL env : TypeEnv)
    (a : Site) (x : Var) (τ : MoveType) (ms : Mut)
    (cont : Stmt) (retTypes : List ParamType)
    (hlookup : lookup envL.varEnv x = some (.validVar, τ, ms))
    (hnb : not_borrowed x envL)
    (hnotIn : notIn envL.siteEnv a)
    (hsub : TypeEnv.subsumes envL env)
    (hfuneq : envL.funEnv = env.funEnv)
    (hwfL : TypeEnv.WellFormed envL) (hwfE : TypeEnv.WellFormed env)
    (hsite_tracked : ∀ s bt r bk, lookup envL.siteEnv s = some (.ref bt r bk) → r ∈ envL.pathEnv.refs)
    (hvar_tracked : ∀ x bt r bk ms, lookup envL.varEnv x = some (.validVar, .ref bt r bk, ms) → r ∈ envL.pathEnv.refs)
    (huniq : RefsUnique envL.varEnv envL.siteEnv)
    (hpaths_to_nm : ∀ u v p, v ∉ env.pathEnv.refs → v ≠ .root → u ≠ v →
      ¬interpret_regex (env.pathEnv.paths (u, v)) p)
    (hpaths_from_nm : ∀ u v p, u ∉ env.pathEnv.refs → u ≠ .root → u ≠ v →
      ¬interpret_regex (env.pathEnv.paths (u, v)) p)
    (hself_loop_only_empty : ∀ u p, interpret_regex (env.pathEnv.paths (u, u)) p → p = [])
    (hroot : Aref.root ∈ envL.pathEnv.refs)
    (ih : WeakenIH lenv
        {envL with varEnv := update envL.varEnv x (.invalidVar, τ, ms)
                   siteEnv := insert envL.siteEnv a τ}
        cont retTypes) :
    typecheck_stmt lenv env (.letBind a (.usage (.move x)) cont) retTypes := by
  obtain ⟨σ, hid, hve, hse, hrefs, hinj, hnonroot, hpaths⟩ := hsub
  have hlook_env := VarEnvSubstEquiv_lookup_valid σ _ _ _ _ _ hve hlookup
  have hτ_nr := hwfL.varEnv_wf _ _ hlookup
  apply typecheck_stmt.let_bind_move lenv env _ _ _ _ _ _
    hlook_env
    (not_borrowed_weaken σ _ env _ hnb hpaths hid hrefs hroot)
    (SiteEnvSubstEquiv_notIn σ _ _ _ hse hnotIn)
  apply ih
  · exact ⟨σ, hid,
      VarEnvSubstEquiv_update_invalid σ _ _ _ _ _ hve,
      SiteEnvSubstEquiv_insert σ _ _ _ _ _ hse rfl,
      hrefs, hinj, hnonroot, hpaths⟩
  · exact hfuneq
  · exact ⟨hwfL.pathEnv_wf,
          SiteEnv.insert_refs_not_root _ _ _ hwfL.siteEnv_wf hτ_nr,
          VarEnv.update_refs_not_root _ _ _ hwfL.varEnv_wf hτ_nr⟩
  · exact ⟨hwfE.pathEnv_wf,
          SiteEnv.insert_refs_not_root _ _ _ hwfE.siteEnv_wf
            (moveTypeRefNotRoot_applySubst σ _ hτ_nr hnonroot),
          VarEnv.update_refs_not_root _ _ _ hwfE.varEnv_wf
            (moveTypeRefNotRoot_applySubst σ _ hτ_nr hnonroot)⟩
  · exact site_tracked_insert_from_var _ _ _ _ _ _ _ hlookup hsite_tracked hvar_tracked
  · exact var_tracked_update_invalid _ _ _ _ _ hvar_tracked
  · exact RefsUnique_move_to_site _ _ _ _ _ _ hlookup huniq
  · exact hpaths_to_nm
  · exact hpaths_from_nm
  · exact hself_loop_only_empty
  · exact hroot

private theorem weaken_let_bind_binop
    (lenv : LabelEnv) (envL env : TypeEnv)
    (bop : Binop) (bt1 bt2 bt3 : BasicMoveType) (sa sb sc : Site)
    (cont : Stmt) (retTypes : List ParamType)
    (hlook_a : lookup envL.siteEnv sa = some (.basic bt1))
    (hlook_b : lookup envL.siteEnv sb = some (.basic bt2))
    (hbinop : binop_type bop bt1 bt2 = some bt3)
    (hnotIn : notIn envL.siteEnv sc)
    (hsub : TypeEnv.subsumes envL env)
    (hfuneq : envL.funEnv = env.funEnv)
    (hwfL : TypeEnv.WellFormed envL) (hwfE : TypeEnv.WellFormed env)
    (hsite_tracked : ∀ s bt r bk, lookup envL.siteEnv s = some (.ref bt r bk) → r ∈ envL.pathEnv.refs)
    (hvar_tracked : ∀ x bt r bk ms, lookup envL.varEnv x = some (.validVar, .ref bt r bk, ms) → r ∈ envL.pathEnv.refs)
    (huniq : RefsUnique envL.varEnv envL.siteEnv)
    (hpaths_to_nm : ∀ u v p, v ∉ env.pathEnv.refs → v ≠ .root → u ≠ v →
      ¬interpret_regex (env.pathEnv.paths (u, v)) p)
    (hpaths_from_nm : ∀ u v p, u ∉ env.pathEnv.refs → u ≠ .root → u ≠ v →
      ¬interpret_regex (env.pathEnv.paths (u, v)) p)
    (hself_loop_only_empty : ∀ u p, interpret_regex (env.pathEnv.paths (u, u)) p → p = [])
    (hroot : Aref.root ∈ envL.pathEnv.refs)
    (ih : WeakenIH lenv
        {envL with siteEnv := insert (delete (delete envL.siteEnv sa) sb) sc (.basic bt3)}
        cont retTypes) :
    typecheck_stmt lenv env (.letBind sc (.binop bop sa sb) cont) retTypes := by
  obtain ⟨σ, hid, hve, hse, hrefs, hinj, hnonroot, hpaths⟩ := hsub
  have hlook_a_env := SiteEnvSubstEquiv_lookup_some σ _ _ _ _ hse hlook_a
  have hlook_b_env := SiteEnvSubstEquiv_lookup_some σ _ _ _ _ hse hlook_b
  simp only [applySubstMoveType] at hlook_a_env hlook_b_env
  apply typecheck_stmt.let_bind_binop lenv env _ _ _ _ _ _ _ _ _
    hlook_a_env hlook_b_env hbinop
  · exact SiteEnvSubstEquiv_notIn σ _ _ _ hse hnotIn
  · apply ih
    · exact ⟨σ, hid, hve,
        SiteEnvSubstEquiv_insert σ _ _ _ _ _ (SiteEnvSubstEquiv_delete σ _ _ sb
          (SiteEnvSubstEquiv_delete σ _ _ sa hse)) (applySubstMoveType_basic σ _),
        hrefs, hinj, hnonroot, hpaths⟩
    · exact hfuneq
    · exact TypeEnv.delete_delete_insert_wf _ _ _ _ _ hwfL trivial
    · exact TypeEnv.delete_delete_insert_wf _ _ _ _ _ hwfE trivial
    · exact site_tracked_insert_basic _ _ _ _
        (site_tracked_delete _ _ sb (site_tracked_delete _ _ sa hsite_tracked))
    · exact hvar_tracked
    · exact RefsUnique_insert_basic _ _ _ _
        (RefsUnique_delete_site _ _ _ (RefsUnique_delete_site _ _ _ huniq))
    · exact hpaths_to_nm
    · exact hpaths_from_nm
    · exact hself_loop_only_empty
    · exact hroot

private theorem weaken_var_assign_invalid
    (lenv : LabelEnv) (envL env : TypeEnv)
    (x : Var) (a : Site) (τ τ' : MoveType)
    (cont : Stmt) (retTypes : List ParamType)
    (hlook_x : lookup envL.varEnv x = some (.invalidVar, τ, .mutable))
    (hlook_a : lookup envL.siteEnv a = some τ')
    (hcompat : MoveType.compatible τ τ')
    (hsub : TypeEnv.subsumes envL env)
    (hfuneq : envL.funEnv = env.funEnv)
    (hwfL : TypeEnv.WellFormed envL) (hwfE : TypeEnv.WellFormed env)
    (hsite_tracked : ∀ s bt r bk, lookup envL.siteEnv s = some (.ref bt r bk) → r ∈ envL.pathEnv.refs)
    (hvar_tracked : ∀ x bt r bk ms, lookup envL.varEnv x = some (.validVar, .ref bt r bk, ms) → r ∈ envL.pathEnv.refs)
    (huniq : RefsUnique envL.varEnv envL.siteEnv)
    (hpaths_to_nm : ∀ u v p, v ∉ env.pathEnv.refs → v ≠ .root → u ≠ v →
      ¬interpret_regex (env.pathEnv.paths (u, v)) p)
    (hpaths_from_nm : ∀ u v p, u ∉ env.pathEnv.refs → u ≠ .root → u ≠ v →
      ¬interpret_regex (env.pathEnv.paths (u, v)) p)
    (hself_loop_only_empty : ∀ u p, interpret_regex (env.pathEnv.paths (u, u)) p → p = [])
    (hroot : Aref.root ∈ envL.pathEnv.refs)
    (ih : WeakenIH lenv
        {envL with varEnv := update envL.varEnv x (.validVar, τ', .mutable)
                   siteEnv := delete envL.siteEnv a}
        cont retTypes) :
    typecheck_stmt lenv env (.assign x a cont) retTypes := by
  obtain ⟨σ, hid, hve, hse, hrefs, hinj, hnonroot, hpaths⟩ := hsub
  obtain ⟨τ_env, hlook_x_env, hbc⟩ := VarEnvSubstEquiv_lookup_invalid σ _ _ _ _ _ hve hlook_x
  have hlook_a_env := SiteEnvSubstEquiv_lookup_some σ _ _ _ _ hse hlook_a
  have hτ'_nr := hwfL.siteEnv_wf _ _ hlook_a
  apply typecheck_stmt.var_assign_invalid lenv env _ _ _ _ _ _
    hlook_x_env hlook_a_env
  · -- MoveType.compatible τ_env (applySubstMoveType σ τ')
    exact MoveType_compatible_of_baseCompatible_subst σ _ _ _ hcompat hbc
      (hwfE.varEnv_wf _ _ hlook_x_env)
      hnonroot
      hτ'_nr
  · -- IH: continuation env subsumes
    apply ih
    · exact ⟨σ, hid,
        VarEnvSubstEquiv_update_valid σ _ _ _ _ _ hve,
        SiteEnvSubstEquiv_delete σ _ _ _ hse,
        hrefs, hinj, hnonroot, hpaths⟩
    · exact hfuneq
    · exact ⟨hwfL.pathEnv_wf,
            SiteEnv.delete_refs_not_root _ _ hwfL.siteEnv_wf,
            VarEnv.update_refs_not_root _ _ _ hwfL.varEnv_wf hτ'_nr⟩
    · exact ⟨hwfE.pathEnv_wf,
            SiteEnv.delete_refs_not_root _ _ hwfE.siteEnv_wf,
            VarEnv.update_refs_not_root _ _ _ hwfE.varEnv_wf
              (moveTypeRefNotRoot_applySubst σ _ hτ'_nr hnonroot)⟩
    · exact site_tracked_delete _ _ _ hsite_tracked
    · exact var_tracked_update_valid_from_site _ _ _ _ _ _ _ hlook_a hsite_tracked hvar_tracked
    · exact RefsUnique_assign_from_site _ _ _ _ _ _ hlook_a huniq
    · exact hpaths_to_nm
    · exact hpaths_from_nm
    · exact hself_loop_only_empty
    · exact hroot

private theorem weaken_let_bind_readRef
    (lenv : LabelEnv) (envL env : TypeEnv)
    (a c : Site) (r : Aref) (τ : BasicMoveType) (isBor : BorrowingKind)
    (cont : Stmt) (retTypes : List ParamType)
    (hlook_a : lookup envL.siteEnv a = some (.ref τ r isBor))
    (hnotIn : notIn envL.siteEnv c)
    (hsub : TypeEnv.subsumes envL env)
    (hfuneq : envL.funEnv = env.funEnv)
    (hwfL : TypeEnv.WellFormed envL) (hwfE : TypeEnv.WellFormed env)
    (hsite_tracked : ∀ s bt r bk, lookup envL.siteEnv s = some (.ref bt r bk) → r ∈ envL.pathEnv.refs)
    (hvar_tracked : ∀ x bt r bk ms, lookup envL.varEnv x = some (.validVar, .ref bt r bk, ms) → r ∈ envL.pathEnv.refs)
    (huniq : RefsUnique envL.varEnv envL.siteEnv)
    (hpaths_to_nm : ∀ u v p, v ∉ env.pathEnv.refs → v ≠ .root → u ≠ v →
      ¬interpret_regex (env.pathEnv.paths (u, v)) p)
    (hpaths_from_nm : ∀ u v p, u ∉ env.pathEnv.refs → u ≠ .root → u ≠ v →
      ¬interpret_regex (env.pathEnv.paths (u, v)) p)
    (hself_loop_only_empty : ∀ u p, interpret_regex (env.pathEnv.paths (u, u)) p → p = [])
    (hroot : Aref.root ∈ envL.pathEnv.refs)
    (ih : WeakenIH lenv
        {envL with siteEnv := insert (delete envL.siteEnv a) c (.basic τ)
                   pathEnv := delete_ref_node envL.pathEnv r}
        cont retTypes) :
    typecheck_stmt lenv env (.letBind c (.readRef a) cont) retTypes := by
  obtain ⟨σ, hid, hve, hse, hrefs, hinj, hnonroot, hpaths⟩ := hsub
  have hlook_a_env := SiteEnvSubstEquiv_lookup_some σ _ _ _ _ hse hlook_a
  simp only [applySubstMoveType] at hlook_a_env
  have hr_mem := hsite_tracked _ _ _ _ hlook_a
  have hr_ne_root := hwfL.siteEnv_wf _ _ hlook_a
  have hσr_ne_root : σ r ≠ .root := hnonroot r hr_ne_root
  apply typecheck_stmt.let_bind_readRef lenv env _ _ _ _ _ _ _
    hlook_a_env
    (SiteEnvSubstEquiv_notIn σ _ _ _ hse hnotIn)
  apply ih
  · -- subsumes
    refine ⟨σ, hid, hve,
      SiteEnvSubstEquiv_insert σ _ _ _ _ _
        (SiteEnvSubstEquiv_delete σ _ _ _ hse) (applySubstMoveType_basic σ _),
      ?_, ?_, hnonroot, ?_⟩
    · simp only [delete_ref_node]; rw [map_filter_ne σ _ r hinj hr_mem, hrefs]
    · intro u v hu hv
      simp only [delete_ref_node, List.mem_filter, decide_eq_true_eq] at hu hv
      exact hinj u v hu.1 hv.1
    · intro u v hu hv path hinterp
      simp only [delete_ref_node, List.mem_filter, decide_eq_true_eq] at hu hv
      have hσu_ne : σ u ≠ σ r := fun h => hu.2 (hinj u r hu.1 hr_mem h)
      have hσv_ne : σ v ≠ σ r := fun h => hv.2 (hinj v r hv.1 hr_mem h)
      simp only [delete_ref_node] at hinterp ⊢
      rw [if_neg (fun ⟨h, _⟩ => hu.2 h), if_neg (not_or.mpr ⟨hu.2, hv.2⟩)]
      rw [if_neg (fun ⟨h, _⟩ => hσu_ne h), if_neg (not_or.mpr ⟨hσu_ne, hσv_ne⟩)] at hinterp
      exact hpaths u v hu.1 hv.1 path hinterp
  · exact hfuneq
  · exact TypeEnv.delete_insert_pathEnv_wf _ _ _ _ _ hwfL
      (delete_ref_node_wellformed _ _ hwfL.pathEnv_wf hr_ne_root) trivial
  · exact TypeEnv.delete_insert_pathEnv_wf _ _ _ _ _ hwfE
      (delete_ref_node_wellformed _ _ hwfE.pathEnv_wf hσr_ne_root) trivial
  · -- site_tracked
    intro s' bt' r' bk' hlook_s'
    simp only [delete_ref_node, List.mem_filter, decide_eq_true_eq]
    by_cases hs'c : s' = c
    · subst hs'c; rw [lookup_insert_same] at hlook_s'; cases hlook_s'
    · rw [lookup_insert_ne _ _ _ _ hs'c] at hlook_s'
      by_cases hs'a : s' = a
      · subst hs'a; rw [lookup_delete_same] at hlook_s'; cases hlook_s'
      · rw [lookup_delete_ne _ _ _ hs'a] at hlook_s'
        exact ⟨hsite_tracked _ _ _ _ hlook_s',
          fun hr'_eq => by rw [hr'_eq] at hlook_s'; exact (huniq r).2.1 s' a _ _ _ _ hs'a hlook_s' hlook_a⟩
  · -- var_tracked
    intro x' bt' r' bk' ms' hlook_x'
    simp only [delete_ref_node, List.mem_filter, decide_eq_true_eq]
    exact ⟨hvar_tracked _ _ _ _ _ hlook_x',
      fun hr'_eq => by rw [hr'_eq] at hlook_x'; exact (huniq r).1 x' _ _ _ a _ _ hlook_x' hlook_a⟩
  · exact RefsUnique_insert_basic _ _ _ _ (RefsUnique_delete_site _ _ _ huniq)
  · exact delete_ref_node_paths_to_non_member _ _ hpaths_to_nm
  · exact delete_ref_node_paths_from_non_member _ _ hpaths_from_nm
  · exact self_loop_only_empty_drn env.pathEnv _ hself_loop_only_empty
  · simp only [delete_ref_node, List.mem_filter, decide_eq_true_eq]
    exact ⟨hroot, Ne.symm hr_ne_root⟩

private theorem weaken_write_ref
    (lenv : LabelEnv) (envL env : TypeEnv)
    (a b : Site) (τ : BasicMoveType) (r : Aref)
    (cont : Stmt) (retTypes : List ParamType)
    (hlook_a : lookup envL.siteEnv a = some (.ref τ r .siteBorrowMut))
    (hlook_b : lookup envL.siteEnv b = some (.basic τ))
    (houtbound : check_outbound envL.pathEnv r (fun re => only_matches_empty (simplify re)))
    (hsub : TypeEnv.subsumes envL env)
    (hfuneq : envL.funEnv = env.funEnv)
    (hwfL : TypeEnv.WellFormed envL) (hwfE : TypeEnv.WellFormed env)
    (hsite_tracked : ∀ s bt r bk, lookup envL.siteEnv s = some (.ref bt r bk) → r ∈ envL.pathEnv.refs)
    (hvar_tracked : ∀ x bt r bk ms, lookup envL.varEnv x = some (.validVar, .ref bt r bk, ms) → r ∈ envL.pathEnv.refs)
    (huniq : RefsUnique envL.varEnv envL.siteEnv)
    (hpaths_to_nm : ∀ u v p, v ∉ env.pathEnv.refs → v ≠ .root → u ≠ v →
      ¬interpret_regex (env.pathEnv.paths (u, v)) p)
    (hpaths_from_nm : ∀ u v p, u ∉ env.pathEnv.refs → u ≠ .root → u ≠ v →
      ¬interpret_regex (env.pathEnv.paths (u, v)) p)
    (hself_loop_only_empty : ∀ u p, interpret_regex (env.pathEnv.paths (u, u)) p → p = [])
    (hroot : Aref.root ∈ envL.pathEnv.refs)
    (ih : WeakenIH lenv
        {envL with siteEnv := delete (delete envL.siteEnv b) a
                   pathEnv := garbage_collect envL.pathEnv r}
        cont retTypes) :
    typecheck_stmt lenv env (.writeRef a b cont) retTypes := by
  obtain ⟨σ, hid, hve, hse, hrefs, hinj, hnonroot, hpaths⟩ := hsub
  have hlook_a_env := SiteEnvSubstEquiv_lookup_some σ _ _ _ _ hse hlook_a
  have hlook_b_env := SiteEnvSubstEquiv_lookup_some σ _ _ _ _ hse hlook_b
  simp only [applySubstMoveType] at hlook_a_env hlook_b_env
  have hr_mem := hsite_tracked _ _ _ _ hlook_a
  have hr_ne_root := hwfL.siteEnv_wf _ _ hlook_a
  have hσr_ne_root : σ r ≠ .root := hnonroot r hr_ne_root
  apply typecheck_stmt.write_ref lenv env _ _ _ (σ r) _ _
    hlook_a_env hlook_b_env
    (check_outbound_weaken σ _ _ r hrefs hpaths hr_mem houtbound)
  apply ih
  · -- subsumes: garbage_collect is the same as delete_ref_node
    refine ⟨σ, hid, hve,
      SiteEnvSubstEquiv_delete σ _ _ _ (SiteEnvSubstEquiv_delete σ _ _ _ hse),
      ?_, ?_, hnonroot, ?_⟩
    · -- refs
      simp only [garbage_collect]
      rw [map_filter_ne σ _ r hinj hr_mem, hrefs]
    · -- injectivity
      intro u v hu hv
      simp only [garbage_collect, List.mem_filter, decide_eq_true_eq] at hu hv
      exact hinj u v hu.1 hv.1
    · -- path_inclusion
      intro u v hu hv path hinterp
      simp only [garbage_collect, List.mem_filter, decide_eq_true_eq] at hu hv
      have hσu_ne : σ u ≠ σ r := fun h => hu.2 (hinj u r hu.1 hr_mem h)
      have hσv_ne : σ v ≠ σ r := fun h => hv.2 (hinj v r hv.1 hr_mem h)
      simp only [garbage_collect] at hinterp ⊢
      rw [if_neg (fun ⟨h, _⟩ => hu.2 h), if_neg (not_or.mpr ⟨hu.2, hv.2⟩)]
      rw [if_neg (fun ⟨h, _⟩ => hσu_ne h), if_neg (not_or.mpr ⟨hσu_ne, hσv_ne⟩)] at hinterp
      exact hpaths u v hu.1 hv.1 path hinterp
  · exact hfuneq
  · exact ⟨garbage_collect_wellformed _ _ hwfL.pathEnv_wf hr_ne_root,
           SiteEnv.delete_refs_not_root _ _ (SiteEnv.delete_refs_not_root _ _ hwfL.siteEnv_wf),
           hwfL.varEnv_wf⟩
  · exact ⟨garbage_collect_wellformed _ _ hwfE.pathEnv_wf hσr_ne_root,
           SiteEnv.delete_refs_not_root _ _ (SiteEnv.delete_refs_not_root _ _ hwfE.siteEnv_wf),
           hwfE.varEnv_wf⟩
  · -- site_tracked
    intro s' bt' r' bk' hlook_s'
    simp only [garbage_collect, List.mem_filter, decide_eq_true_eq]
    by_cases hs'a : s' = a
    · subst hs'a; rw [lookup_delete_same] at hlook_s'; cases hlook_s'
    · rw [lookup_delete_ne _ _ _ hs'a] at hlook_s'
      by_cases hs'b : s' = b
      · subst hs'b; rw [lookup_delete_same] at hlook_s'; cases hlook_s'
      · rw [lookup_delete_ne _ _ _ hs'b] at hlook_s'
        exact ⟨hsite_tracked _ _ _ _ hlook_s',
          fun hr'_eq => by rw [hr'_eq] at hlook_s'; exact (huniq r).2.1 s' a _ _ _ _ hs'a hlook_s' hlook_a⟩
  · -- var_tracked
    intro x' bt' r' bk' ms' hlook_x'
    simp only [garbage_collect, List.mem_filter, decide_eq_true_eq]
    exact ⟨hvar_tracked _ _ _ _ _ hlook_x',
      fun hr'_eq => by rw [hr'_eq] at hlook_x'; exact (huniq r).1 x' _ _ _ a _ _ hlook_x' hlook_a⟩
  · exact RefsUnique_delete_site _ _ _ (RefsUnique_delete_site _ _ _ huniq)
  · exact garbage_collect_paths_to_non_member _ _ hpaths_to_nm
  · exact garbage_collect_paths_from_non_member _ _ hpaths_from_nm
  · exact self_loop_only_empty_gc env.pathEnv _ hself_loop_only_empty
  · simp only [garbage_collect, List.mem_filter, decide_eq_true_eq]
    exact ⟨hroot, Ne.symm hr_ne_root⟩

private theorem weaken_release
    (lenv : LabelEnv) (envL env : TypeEnv)
    (a : Site) (τ : BasicMoveType) (r : Aref) (isBor : BorrowingKind)
    (cont : Stmt) (retTypes : List ParamType)
    (hlook_a : lookup envL.siteEnv a = some (.ref τ r isBor))
    (hsub : TypeEnv.subsumes envL env)
    (hfuneq : envL.funEnv = env.funEnv)
    (hwfL : TypeEnv.WellFormed envL) (hwfE : TypeEnv.WellFormed env)
    (hsite_tracked : ∀ s bt r bk, lookup envL.siteEnv s = some (.ref bt r bk) → r ∈ envL.pathEnv.refs)
    (hvar_tracked : ∀ x bt r bk ms, lookup envL.varEnv x = some (.validVar, .ref bt r bk, ms) → r ∈ envL.pathEnv.refs)
    (huniq : RefsUnique envL.varEnv envL.siteEnv)
    (hpaths_to_nm : ∀ u v p, v ∉ env.pathEnv.refs → v ≠ .root → u ≠ v →
      ¬interpret_regex (env.pathEnv.paths (u, v)) p)
    (hpaths_from_nm : ∀ u v p, u ∉ env.pathEnv.refs → u ≠ .root → u ≠ v →
      ¬interpret_regex (env.pathEnv.paths (u, v)) p)
    (hself_loop_only_empty : ∀ u p, interpret_regex (env.pathEnv.paths (u, u)) p → p = [])
    (hroot : Aref.root ∈ envL.pathEnv.refs)
    (ih : WeakenIH lenv
        {envL with siteEnv := delete envL.siteEnv a
                   pathEnv := delete_ref_node envL.pathEnv r}
        cont retTypes) :
    typecheck_stmt lenv env (.release a cont) retTypes := by
  obtain ⟨σ, hid, hve, hse, hrefs, hinj, hnonroot, hpaths⟩ := hsub
  have hlook_a_env := SiteEnvSubstEquiv_lookup_some σ _ _ _ _ hse hlook_a
  simp only [applySubstMoveType] at hlook_a_env
  have hr_mem := hsite_tracked _ _ _ _ hlook_a
  have hr_ne_root := hwfL.siteEnv_wf _ _ hlook_a
  have hσr_ne_root : σ r ≠ .root := hnonroot r hr_ne_root
  apply typecheck_stmt.release lenv env _ _ (σ r) _ _ _ hlook_a_env
  apply ih
  · -- subsumes
    refine ⟨σ, hid, hve, SiteEnvSubstEquiv_delete σ _ _ _ hse, ?_, ?_, hnonroot, ?_⟩
    · -- refs
      simp only [delete_ref_node]
      rw [map_filter_ne σ _ r hinj hr_mem, hrefs]
    · -- injectivity
      intro u v hu hv
      simp only [delete_ref_node, List.mem_filter, decide_eq_true_eq] at hu hv
      exact hinj u v hu.1 hv.1
    · -- path_inclusion
      intro u v hu hv path hinterp
      simp only [delete_ref_node, List.mem_filter, decide_eq_true_eq] at hu hv
      have hσu_ne : σ u ≠ σ r := fun h => hu.2 (hinj u r hu.1 hr_mem h)
      have hσv_ne : σ v ≠ σ r := fun h => hv.2 (hinj v r hv.1 hr_mem h)
      simp only [delete_ref_node] at hinterp ⊢
      rw [if_neg (fun ⟨h, _⟩ => hu.2 h), if_neg (not_or.mpr ⟨hu.2, hv.2⟩)]
      rw [if_neg (fun ⟨h, _⟩ => hσu_ne h), if_neg (not_or.mpr ⟨hσu_ne, hσv_ne⟩)] at hinterp
      exact hpaths u v hu.1 hv.1 path hinterp
  · exact hfuneq
  · -- WellFormed modified envL
    exact ⟨delete_ref_node_wellformed _ _ hwfL.pathEnv_wf hr_ne_root,
           SiteEnv.delete_refs_not_root _ _ hwfL.siteEnv_wf,
           hwfL.varEnv_wf⟩
  · -- WellFormed modified env
    exact ⟨delete_ref_node_wellformed _ _ hwfE.pathEnv_wf hσr_ne_root,
           SiteEnv.delete_refs_not_root _ _ hwfE.siteEnv_wf,
           hwfE.varEnv_wf⟩
  · -- site_tracked
    intro s' bt' r' bk' hlook_s'
    simp only [delete_ref_node, List.mem_filter, decide_eq_true_eq]
    by_cases hs' : s' = a
    · subst hs'; rw [lookup_delete_same] at hlook_s'; cases hlook_s'
    · rw [lookup_delete_ne _ _ _ hs'] at hlook_s'
      exact ⟨hsite_tracked _ _ _ _ hlook_s',
        fun hr'_eq => by rw [hr'_eq] at hlook_s'; exact (huniq r).2.1 s' a _ _ _ _ hs' hlook_s' hlook_a⟩
  · -- var_tracked
    intro x' bt' r' bk' ms' hlook_x'
    simp only [delete_ref_node, List.mem_filter, decide_eq_true_eq]
    exact ⟨hvar_tracked _ _ _ _ _ hlook_x',
      fun hr'_eq => by rw [hr'_eq] at hlook_x'; exact (huniq r).1 x' _ _ _ a _ _ hlook_x' hlook_a⟩
  · exact RefsUnique_delete_site _ _ _ huniq
  · exact delete_ref_node_paths_to_non_member _ _ hpaths_to_nm
  · exact delete_ref_node_paths_from_non_member _ _ hpaths_from_nm
  · exact self_loop_only_empty_drn env.pathEnv _ hself_loop_only_empty
  · simp only [delete_ref_node, List.mem_filter, decide_eq_true_eq]
    exact ⟨hroot, Ne.symm hr_ne_root⟩

private theorem weaken_let_bind_copy_ref
    (lenv : LabelEnv) (envL env : TypeEnv)
    (a : Site) (x : Var) (τ : BasicMoveType) (ms : Mut) (s t : Aref) (isBor : BorrowingKind)
    (cont : Stmt) (retTypes : List ParamType)
    (hlookup : lookup envL.varEnv x = some (.validVar, .ref τ s isBor, ms))
    (hnotIn : notIn envL.siteEnv a)
    (hfresh : freshRefInEnv t envL)
    (hsub : TypeEnv.subsumes envL env)
    (hfuneq : envL.funEnv = env.funEnv)
    (hwfL : TypeEnv.WellFormed envL) (hwfE : TypeEnv.WellFormed env)
    (hsite_tracked : ∀ s bt r bk, lookup envL.siteEnv s = some (.ref bt r bk) → r ∈ envL.pathEnv.refs)
    (hvar_tracked : ∀ x bt r bk ms, lookup envL.varEnv x = some (.validVar, .ref bt r bk, ms) → r ∈ envL.pathEnv.refs)
    (huniq : RefsUnique envL.varEnv envL.siteEnv)
    (hpaths_to_nm : ∀ u v p, v ∉ env.pathEnv.refs → v ≠ .root → u ≠ v →
      ¬interpret_regex (env.pathEnv.paths (u, v)) p)
    (hpaths_from_nm : ∀ u v p, u ∉ env.pathEnv.refs → u ≠ .root → u ≠ v →
      ¬interpret_regex (env.pathEnv.paths (u, v)) p)
    (hself_loop_only_empty : ∀ u p, interpret_regex (env.pathEnv.paths (u, u)) p → p = [])
    (hroot : Aref.root ∈ envL.pathEnv.refs)
    (ih : WeakenIH lenv
        {envL with siteEnv := insert envL.siteEnv a (.ref τ t isBor)
                   pathEnv := update_with_epsilon t s envL.pathEnv}
        cont retTypes) :
    typecheck_stmt lenv env (.letBind a (.usage (.copy x)) cont) retTypes := by
  obtain ⟨σ, hid, hve, hse, hrefs, hinj, hnonroot, hpaths⟩ := hsub
  have hlook_env := VarEnvSubstEquiv_lookup_valid σ _ _ _ _ _ hve hlookup
  simp only [applySubstMoveType] at hlook_env
  -- Freshness of t in envL
  have ht_fresh_pe : t ∉ envL.pathEnv.refs := freshRefInEnv_implies_freshRef t envL hfresh
  have ht_ne_root : t ≠ .root := fun h => ht_fresh_pe (h ▸ hroot)
  have ht_not_varRef : ∀ v, t ≠ .varRef v := freshRefInEnv_not_varRef t envL hfresh
  -- t is a refid (from ht_ne_root + ht_not_varRef)
  have ht_refid : ∃ n, t = .refid n := by
    cases t with
    | root => exact absurd rfl ht_ne_root
    | refid n => exact ⟨n, rfl⟩
    | varRef v => exact absurd rfl (ht_not_varRef v)
  -- Pick fresh t' for env
  let t' := nextFreshRefInEnv env
  have ht'_fresh_prop := nextFreshRefInEnv_fresh_prop env
  have ht'_fresh_pe := nextFreshRefInEnv_not_in_pathEnv env
  have ht'_not_root := nextFreshRefInEnv_not_root env
  have ht'_not_mapped : t' ∉ envL.pathEnv.refs.map σ := by rw [hrefs]; exact ht'_fresh_pe
  -- s ∈ envL.pathEnv.refs (from var_tracked)
  have hs_mem := hvar_tracked _ _ _ _ _ hlookup
  -- Apply the copy_ref rule
  apply typecheck_stmt.let_bind_copy_ref lenv env _ _ _ _ (σ s) t' _ _ _
    hlook_env
    (SiteEnvSubstEquiv_notIn σ _ _ _ hse hnotIn)
    ht'_fresh_prop
  -- IH: need subsumes for modified envs
  apply ih
  · -- subsumes with extendSubst σ t t'
    refine ⟨extendSubst σ t t',
      extendSubst_id σ t t' hid ht_refid,
      VarEnvSubstEquiv_extend σ t t' _ _ hve
        (fun x' bt' s' bk' ms' hlook' =>
          Ne.symm (freshRefInEnv_ne_varEnv_ref t _ x' .validVar bt' s' bk' ms' hfresh hlook')),
      SiteEnvSubstEquiv_extend_insert_ref σ t t' _ _ _ _ _ hse
        (fun k bt r bk hlook' =>
          Ne.symm (freshRefInEnv_ne_siteEnv_ref t _ k bt r bk hfresh hlook')),
      ?_, ?_, ?_, ?_⟩
    · -- refs: (uwe t s [] peL).refs.map σ' = (uwe t' (σ s) [] peE).refs
      simp only [uwe_epsilon_refs_fresh t s envL.pathEnv ht_fresh_pe,
          uwe_epsilon_refs_fresh t' (σ s) env.pathEnv ht'_fresh_pe]
      simp only [List.map, extendSubst, ite_true]
      congr 1
      rw [map_extendSubst_eq_map_σ σ t t' _ ht_fresh_pe, hrefs]
    · -- injectivity
      exact extendSubst_injective σ t t' _ hinj ht_fresh_pe ht'_not_mapped
    · -- nonroot
      exact extendSubst_nonroot σ t t' hnonroot ht'_not_root
    · -- path_inclusion
      exact path_inclusion_update_with_extension σ _ _ t t' s [] hpaths ht_fresh_pe ht'_not_mapped hs_mem
  · exact hfuneq
  · -- WellFormed envL'
    exact ⟨update_with_epsilon_wellformed t s envL.pathEnv hwfL.pathEnv_wf ht_ne_root,
           SiteEnv.insert_refs_not_root _ _ _ hwfL.siteEnv_wf ht_ne_root,
           hwfL.varEnv_wf⟩
  · -- WellFormed env'
    exact ⟨update_with_epsilon_wellformed t' (σ s) env.pathEnv hwfE.pathEnv_wf ht'_not_root,
           SiteEnv.insert_refs_not_root _ _ _ hwfE.siteEnv_wf ht'_not_root,
           hwfE.varEnv_wf⟩
  · -- site_tracked
    intro s' bt r bk hlook_s'
    simp only [uwe_epsilon_refs_fresh t s envL.pathEnv ht_fresh_pe]
    by_cases hs' : s' = a
    · subst hs'; rw [lookup_insert_same] at hlook_s'
      simp only [Option.some.injEq, MoveType.ref.injEq] at hlook_s'
      obtain ⟨-, rfl, -⟩ := hlook_s'
      exact .head _
    · rw [lookup_insert_ne _ _ _ _ hs'] at hlook_s'
      exact .tail _ (hsite_tracked _ _ _ _ hlook_s')
  · -- var_tracked
    intro x' bt r bk ms' hlook_x'
    simp only [uwe_epsilon_refs_fresh t s envL.pathEnv ht_fresh_pe]
    exact .tail _ (hvar_tracked _ _ _ _ _ hlook_x')
  · -- RefsUnique
    exact RefsUnique_insert_fresh_ref _ _ _ _ _ _ huniq
      (fun x' bt' r bk' ms' hlook' =>
        Ne.symm (freshRefInEnv_ne_varEnv_ref t _ x' .validVar bt' r bk' ms' hfresh hlook'))
      (fun s' bt' r bk' hlook' =>
        Ne.symm (freshRefInEnv_ne_siteEnv_ref t _ s' bt' r bk' hfresh hlook'))
  · exact update_with_extension_paths_to_non_member _ _ _ _ hpaths_to_nm
      (Or.inl (by rw [← hrefs]; exact List.mem_map_of_mem hs_mem))
  · exact update_with_extension_paths_from_non_member _ _ _ _ hpaths_from_nm
      (Or.inl (by rw [← hrefs]; exact List.mem_map_of_mem hs_mem))
  · exact self_loop_only_empty_uwe _ _ _ env.pathEnv hself_loop_only_empty
  · -- root ∈ updated refs
    simp only [uwe_epsilon_refs_fresh t s envL.pathEnv ht_fresh_pe]
    exact .tail _ hroot

private theorem weaken_let_bind_pack
    (lenv : LabelEnv) (envL env : TypeEnv)
    (b : Site) (recName : Id) (fields : List (Field × Site)) (fentries : AssocMap Field BasicMoveType)
    (cont : Stmt) (retTypes : List ParamType)
    (hnotIn : notIn envL.siteEnv b)
    (hft : ∀ f a, (f, a) ∈ fields →
       ∃ (bt : BasicMoveType), lookup envL.siteEnv a = some (.basic bt) ∧
                                lookup fentries f = some bt)
    (hfc : ∀ f, lookup fentries f ≠ none → ∃ a, (f, a) ∈ fields)
    (hfi : ∀ a₁ a₂, (∃ f₁ f₂, (f₁, a₁) ∈ fields ∧ (f₂, a₂) ∈ fields ∧ f₁ ≠ f₂) → a₁ ≠ a₂)
    (hsub : TypeEnv.subsumes envL env)
    (hfuneq : envL.funEnv = env.funEnv)
    (hwfL : TypeEnv.WellFormed envL) (hwfE : TypeEnv.WellFormed env)
    (hsite_tracked : ∀ s bt r bk, lookup envL.siteEnv s = some (.ref bt r bk) → r ∈ envL.pathEnv.refs)
    (hvar_tracked : ∀ x bt r bk ms, lookup envL.varEnv x = some (.validVar, .ref bt r bk, ms) → r ∈ envL.pathEnv.refs)
    (huniq : RefsUnique envL.varEnv envL.siteEnv)
    (hpaths_to_nm : ∀ u v p, v ∉ env.pathEnv.refs → v ≠ .root → u ≠ v →
      ¬interpret_regex (env.pathEnv.paths (u, v)) p)
    (hpaths_from_nm : ∀ u v p, u ∉ env.pathEnv.refs → u ≠ .root → u ≠ v →
      ¬interpret_regex (env.pathEnv.paths (u, v)) p)
    (hself_loop_only_empty : ∀ u p, interpret_regex (env.pathEnv.paths (u, u)) p → p = [])
    (hroot : Aref.root ∈ envL.pathEnv.refs)
    (ih : WeakenIH lenv
        {envL with siteEnv := insert (deleteAll envL.siteEnv (fields.map Prod.snd)) b (.basic (.trecord fentries))}
        cont retTypes) :
    typecheck_stmt lenv env (.letBind b (.pack recName fields) cont) retTypes := by
  obtain ⟨σ, hid, hve, hse, hrefs, hinj, hnonroot, hpaths⟩ := hsub
  apply typecheck_stmt.let_bind_pack
  · exact SiteEnvSubstEquiv_notIn σ _ _ _ hse hnotIn
  · intro f a hmem
    obtain ⟨bt, hlook_a, hlook_f⟩ := hft f a hmem
    have hlook_a_env := SiteEnvSubstEquiv_lookup_some σ _ _ _ _ hse hlook_a
    simp only [applySubstMoveType] at hlook_a_env
    exact ⟨bt, hlook_a_env, hlook_f⟩
  · exact hfc
  · exact hfi
  · apply ih
    · exact ⟨σ, hid, hve,
        SiteEnvSubstEquiv_insert σ _ _ _ _ _
          (SiteEnvSubstEquiv_deleteAll σ _ _ _ hse) (applySubstMoveType_basic σ _),
        hrefs, hinj, hnonroot, hpaths⟩
    · exact hfuneq
    · exact TypeEnv.deleteAll_insert_wf _ _ _ _ hwfL trivial
    · exact TypeEnv.deleteAll_insert_wf _ _ _ _ hwfE trivial
    · exact site_tracked_insert_basic _ _ _ _
        (site_tracked_deleteAll _ _ _ hsite_tracked)
    · exact hvar_tracked
    · exact RefsUnique_insert_basic _ _ _ _ (RefsUnique_deleteAll _ _ _ huniq)
    · exact hpaths_to_nm
    · exact hpaths_from_nm
    · exact hself_loop_only_empty
    · exact hroot

private theorem weaken_unpack
    (lenv : LabelEnv) (envL env : TypeEnv)
    (fields : List (Field × Site)) (b : Site) (fentries : AssocMap Field BasicMoveType)
    (cont : Stmt) (retTypes : List ParamType)
    (hlook_b : lookup envL.siteEnv b = some (.basic (.trecord fentries)))
    (hfresh : ∀ (f : Field) (a : Site), (f, a) ∈ fields → notIn envL.siteEnv a)
    (hinj_f : ∀ a₁ a₂, (∃ f₁ f₂, (f₁, a₁) ∈ fields ∧ (f₂, a₂) ∈ fields ∧ f₁ ≠ f₂) → a₁ ≠ a₂)
    (hexist : ∀ (f : Field) (a : Site), (f, a) ∈ fields → ∃ bt, lookup fentries f = some bt)
    (hsub : TypeEnv.subsumes envL env)
    (hfuneq : envL.funEnv = env.funEnv)
    (hwfL : TypeEnv.WellFormed envL) (hwfE : TypeEnv.WellFormed env)
    (hsite_tracked : ∀ s bt r bk, lookup envL.siteEnv s = some (.ref bt r bk) → r ∈ envL.pathEnv.refs)
    (hvar_tracked : ∀ x bt r bk ms, lookup envL.varEnv x = some (.validVar, .ref bt r bk, ms) → r ∈ envL.pathEnv.refs)
    (huniq : RefsUnique envL.varEnv envL.siteEnv)
    (hpaths_to_nm : ∀ u v p, v ∉ env.pathEnv.refs → v ≠ .root → u ≠ v →
      ¬interpret_regex (env.pathEnv.paths (u, v)) p)
    (hpaths_from_nm : ∀ u v p, u ∉ env.pathEnv.refs → u ≠ .root → u ≠ v →
      ¬interpret_regex (env.pathEnv.paths (u, v)) p)
    (hself_loop_only_empty : ∀ u p, interpret_regex (env.pathEnv.paths (u, u)) p → p = [])
    (hroot : Aref.root ∈ envL.pathEnv.refs)
    (ih : WeakenIH lenv
        {envL with siteEnv := addFieldSites fentries (delete envL.siteEnv b) fields}
        cont retTypes) :
    typecheck_stmt lenv env (.unpack fields b cont) retTypes := by
  obtain ⟨σ, hid, hve, hse, hrefs, hinj, hnonroot, hpaths⟩ := hsub
  have hlook_env := SiteEnvSubstEquiv_lookup_some σ _ _ _ _ hse hlook_b
  simp only [applySubstMoveType] at hlook_env
  apply typecheck_stmt.unpack lenv env _ _ _ _ _
    hlook_env
  · intro f a hmem
    exact SiteEnvSubstEquiv_notIn σ _ _ _ hse (hfresh f a hmem)
  · exact hinj_f
  · exact hexist
  · apply ih
    · exact ⟨σ, hid, hve,
        SiteEnvSubstEquiv_addFieldSites σ _ _ _ _
          (SiteEnvSubstEquiv_delete σ _ _ _ hse),
        hrefs, hinj, hnonroot, hpaths⟩
    · exact hfuneq
    · exact ⟨hwfL.pathEnv_wf,
        addFieldSites_refs_not_root _ _ _
          (SiteEnv.delete_refs_not_root _ _ hwfL.siteEnv_wf),
        hwfL.varEnv_wf⟩
    · exact ⟨hwfE.pathEnv_wf,
        addFieldSites_refs_not_root _ _ _
          (SiteEnv.delete_refs_not_root _ _ hwfE.siteEnv_wf),
        hwfE.varEnv_wf⟩
    · exact site_tracked_addFieldSites _ _ _ _
        (site_tracked_delete _ _ _ hsite_tracked)
    · exact hvar_tracked
    · exact RefsUnique_addFieldSites _ _ _ _ (RefsUnique_delete_site _ _ _ huniq)
    · exact hpaths_to_nm
    · exact hpaths_from_nm
    · exact hself_loop_only_empty
    · exact hroot

-- ============================================================
-- Helper lemmas for the call case
-- ============================================================

/-- Generate n fresh refs for an environment. -/
private def makeFreshRefs (env : TypeEnv) (n : Nat) : List Aref :=
  let start := getRefId (nextFreshRefInEnv env)
  (List.range n).map fun i => .refid (start + i)

private lemma makeFreshRefs_length (env : TypeEnv) (n : Nat) :
    (makeFreshRefs env n).length = n := by
  simp [makeFreshRefs]

private lemma makeFreshRefs_fresh (env : TypeEnv) (n : Nat) :
    all_refs_fresh_in_env env (makeFreshRefs env n) := by
  intro r hr
  simp [makeFreshRefs] at hr
  obtain ⟨i, _, rfl⟩ := hr
  exact freshRefInEnvBool_implies_freshRefInEnv _ _ (refid_ge_start_fresh env _ (by omega))

private lemma makeFreshRefs_nodup (env : TypeEnv) (n : Nat) :
    List.Nodup (makeFreshRefs env n) := by
  simp only [makeFreshRefs, List.Nodup]
  rw [List.pairwise_map]
  exact List.nodup_range.imp (fun hab h => hab (by simp [Aref.refid.injEq] at h; omega))

private lemma makeFreshRefs_not_root (env : TypeEnv) (n : Nat) :
    ∀ r ∈ makeFreshRefs env n, r ≠ Aref.root := by
  intro r hr
  simp [makeFreshRefs] at hr
  obtain ⟨_, _, rfl⟩ := hr
  exact fun h => by cases h

private lemma makeFreshRefs_not_varRef (env : TypeEnv) (n : Nat) :
    ∀ r ∈ makeFreshRefs env n, ∀ v, r ≠ Aref.varRef v := by
  intro r hr v
  simp [makeFreshRefs] at hr
  obtain ⟨_, _, rfl⟩ := hr
  exact fun h => by cases h

/-- types_conform is preserved under SiteEnvSubstEquiv because it only checks
    basic types and borrow kinds, which are unaffected by σ. -/
private lemma types_conform_SiteEnvSubstEquiv (σ : Aref → Aref)
    (seL seE : SiteEnv) (bs : List Site) (params : List ParamType)
    (hse : SiteEnvSubstEquiv σ seL seE)
    (htc : types_conform seL bs params) :
    types_conform seE bs params := by
  induction bs generalizing params with
  | nil => cases params <;> exact htc
  | cons b bs' ihbs =>
    cases params with
    | nil => exact htc
    | cons pt pts =>
      unfold types_conform at htc ⊢
      cases hlL : AssocMap.lookup seL b with
      | none => rw [hlL] at htc; exact htc.elim
      | some τL =>
        rw [hlL] at htc
        have hlE := SiteEnvSubstEquiv_lookup_some σ seL seE b τL hse hlL
        rw [hlE]
        obtain ⟨pbt, isRefMut⟩ := pt
        cases τL with
        | basic bt' =>
          simp only [applySubstMoveType] at hlE ⊢
          cases isRefMut with
          | none => exact ⟨htc.1, ihbs _ htc.2⟩
          | some _ => exact htc
        | ref bt' r' bk' =>
          simp only [applySubstMoveType] at hlE ⊢
          cases isRefMut with
          | none => exact htc
          | some _ => exact ⟨htc.1, htc.2.1, ihbs _ htc.2.2⟩

/-- all_fresh_sites is preserved: if output sites are not in seL, they're not in seE. -/
private lemma all_fresh_sites_subsumes (σ : Aref → Aref)
    (envL env : TypeEnv) (as : List Site)
    (hse : SiteEnvSubstEquiv σ envL.siteEnv env.siteEnv)
    (hfresh : all_fresh_sites envL as) :
    all_fresh_sites env as := by
  unfold all_fresh_sites at hfresh ⊢
  induction as with
  | nil => trivial
  | cons a as' ihas =>
    simp only [List.all_cons, Bool.and_eq_true] at hfresh ⊢
    exact ⟨SiteEnvSubstEquiv_notIn σ _ _ _ hse hfresh.1, ihas hfresh.2⟩

/-- Semantic check_mutable_inputs_isolated transfers through subsumption:
    if envL's mutable inputs are isolated (all paths match only []) and env has fewer paths,
    then env's mutable inputs are also isolated. -/
private lemma check_mutable_inputs_isolated_subsumes
    (σ : Aref → Aref) (envL env : TypeEnv) (bs : List Site)
    (hse : SiteEnvSubstEquiv σ envL.siteEnv env.siteEnv)
    (hpaths : ∀ u v, u ∈ envL.pathEnv.refs → v ∈ envL.pathEnv.refs →
      ∀ path, interpret_regex (env.pathEnv.paths (σ u, σ v)) path →
              interpret_regex (envL.pathEnv.paths (u, v)) path)
    (hsite_tracked : ∀ s bt r bk, lookup envL.siteEnv s = some (.ref bt r bk) → r ∈ envL.pathEnv.refs)
    (hiso : check_mutable_inputs_isolated envL bs) :
    check_mutable_inputs_isolated env bs := by
  intro mi_site hmi mi_bt mi_ref hlookup_mi other_site hother other_bt other_ref bk hlookup_other hne
  have hse_mi := hse mi_site
  have hse_other := hse other_site
  cases hlL_mi : AssocMap.lookup envL.siteEnv mi_site with
  | none => simp [hlL_mi, hlookup_mi] at hse_mi
  | some τL_mi =>
    simp [hlL_mi, hlookup_mi] at hse_mi
    cases τL_mi with
    | basic _ =>
      -- applySubstMoveType σ (.basic _) = .ref ... is False
      simp [applySubstMoveType] at hse_mi
    | ref bt_L r_L bk_L =>
      simp only [applySubstMoveType, MoveType.ref.injEq] at hse_mi
      obtain ⟨_, hr_eq, hbk_eq⟩ := hse_mi
      subst hbk_eq; subst hr_eq
      -- Now mi_ref = σ r_L in context
      cases hlL_other : AssocMap.lookup envL.siteEnv other_site with
      | none => simp [hlL_other, hlookup_other] at hse_other
      | some τL_other =>
        simp [hlL_other, hlookup_other] at hse_other
        cases τL_other with
        | basic _ =>
          simp [applySubstMoveType] at hse_other
        | ref bt_L2 r_L2 bk_L2 =>
          simp only [applySubstMoveType, MoveType.ref.injEq] at hse_other
          obtain ⟨_, hr_eq2, _⟩ := hse_other
          subst hr_eq2
          -- Now other_ref = σ r_L2 in context
          have hiso_L := hiso mi_site hmi bt_L r_L hlL_mi other_site hother bt_L2 r_L2 bk_L2 hlL_other hne
          intro p hp
          exact hiso_L p (hpaths r_L r_L2 (hsite_tracked _ _ _ _ hlL_mi) (hsite_tracked _ _ _ _ hlL_other) p hp)

/-- populate_call_outputs preserves varEnv -/
private lemma populate_call_outputs_varEnv (env env' : TypeEnv) (as : List Site) (rets : List ParamType)
    (outRefs : List Aref)
    (hpop : populate_call_outputs env as rets outRefs = some env') :
    env'.varEnv = env.varEnv := by
  induction as generalizing env env' rets outRefs with
  | nil =>
    cases rets with
    | nil => simp only [populate_call_outputs] at hpop; split at hpop <;> simp_all
    | cons _ _ => simp [populate_call_outputs] at hpop
  | cons a as' ihas =>
    cases rets with
    | nil => simp [populate_call_outputs] at hpop
    | cons pt pts =>
      obtain ⟨bt, isRefMut⟩ := pt
      cases isRefMut with
      | none =>
        simp only [populate_call_outputs] at hpop
        have := ihas _ env' pts outRefs hpop
        simpa using this
      | some isRM =>
        cases isRM <;> (
          cases outRefs with
          | nil => simp [populate_call_outputs] at hpop
          | cons r outRefs' =>
            simp only [populate_call_outputs] at hpop
            have := ihas _ env' pts outRefs' hpop
            simpa using this)

/-- populate_call_outputs preserves funEnv -/
private lemma populate_call_outputs_funEnv (env env' : TypeEnv) (as : List Site) (rets : List ParamType)
    (outRefs : List Aref)
    (hpop : populate_call_outputs env as rets outRefs = some env') :
    env'.funEnv = env.funEnv := by
  induction as generalizing env env' rets outRefs with
  | nil =>
    cases rets with
    | nil => simp only [populate_call_outputs] at hpop; split at hpop <;> simp_all
    | cons _ _ => simp [populate_call_outputs] at hpop
  | cons a as' ihas =>
    cases rets with
    | nil => simp [populate_call_outputs] at hpop
    | cons pt pts =>
      obtain ⟨bt, isRefMut⟩ := pt
      cases isRefMut with
      | none =>
        simp only [populate_call_outputs] at hpop
        have := ihas _ env' pts outRefs hpop
        simpa using this
      | some isRM =>
        cases isRM <;> (
          cases outRefs with
          | nil => simp [populate_call_outputs] at hpop
          | cons r outRefs' =>
            simp only [populate_call_outputs] at hpop
            have := ihas _ env' pts outRefs' hpop
            simpa using this)

/-- call_connect_inputs_outputs preserves varEnv -/
private lemma call_connect_varEnv (env : TypeEnv) (as bs : List Site) :
    (call_connect_inputs_outputs env as bs).varEnv = env.varEnv := by
  simp [call_connect_inputs_outputs]

/-- call_connect_inputs_outputs preserves funEnv -/
private lemma call_connect_funEnv (env : TypeEnv) (as bs : List Site) :
    (call_connect_inputs_outputs env as bs).funEnv = env.funEnv := by
  simp [call_connect_inputs_outputs]

/-- call_connect_inputs_outputs preserves siteEnv -/
private lemma call_connect_siteEnv (env : TypeEnv) (as bs : List Site) :
    (call_connect_inputs_outputs env as bs).siteEnv = env.siteEnv := by
  simp [call_connect_inputs_outputs]

/-- populate_call_outputs succeeds for any env with same-length outRefs,
    as success depends only on the structure of as/rets/outRefs, not on env contents. -/
private lemma populate_call_outputs_exists' (env env0 : TypeEnv) (as : List Site)
    (rets : List ParamType) (outRefs outRefs0 : List Aref) (env0' : TypeEnv)
    (hpop0 : populate_call_outputs env0 as rets outRefs0 = some env0')
    (hlen : outRefs.length = outRefs0.length) :
    ∃ env', populate_call_outputs env as rets outRefs = some env' := by
  induction as generalizing env env0 env0' rets outRefs outRefs0 with
  | nil =>
    cases rets with
    | nil =>
      simp only [populate_call_outputs] at hpop0 ⊢
      split at hpop0
      · next h0 =>
        cases outRefs with
        | nil => exact ⟨env, by simp [List.isEmpty]⟩
        | cons _ _ =>
          cases outRefs0 with
          | nil => simp at hlen
          | cons _ _ => simp [List.isEmpty] at h0
      · simp at hpop0
    | cons _ _ => simp [populate_call_outputs] at hpop0
  | cons a as' ihas =>
    cases rets with
    | nil => simp [populate_call_outputs] at hpop0
    | cons pt pts =>
      obtain ⟨bt, isRefMut⟩ := pt
      cases isRefMut with
      | none =>
        simp only [populate_call_outputs] at hpop0 ⊢
        exact ihas _ _ _ _ _ _ hpop0 hlen
      | some isRM =>
        cases isRM <;> (
          cases outRefs0 with
          | nil => simp [populate_call_outputs] at hpop0
          | cons r0 outRefs0' =>
            cases outRefs with
            | nil => simp at hlen
            | cons r outRefs' =>
              simp only [populate_call_outputs] at hpop0 ⊢
              exact ihas _ _ _ _ _ _ hpop0 (by simpa using hlen))

-- ============================================================
-- populate/call_connect preservation helpers for weaken_call
-- ============================================================

/-- Generic foldl property preservation -/
private lemma foldl_preserves_prop {α β : Type} {P : α → Prop} (f : α → β → α) (init : α)
    (l : List β) (hinit : P init)
    (hstep : ∀ acc b, P acc → P (f acc b)) : P (l.foldl f init) := by
  induction l generalizing init with
  | nil => exact hinit
  | cons x xs ih => exact ih (f init x) (hstep init x hinit)

/-- SiteEnvSubstEquiv reverse lookup: from env to envL -/
private lemma SiteEnvSubstEquiv_lookup_some_inv (σ : Aref → Aref) (se1 se2 : SiteEnv)
    (k : Site) (τ2 : MoveType) :
    SiteEnvSubstEquiv σ se1 se2 →
    lookup se2 k = some τ2 →
    ∃ τ1, lookup se1 k = some τ1 ∧ applySubstMoveType σ τ1 = τ2 := by
  intro hse hlook2
  unfold SiteEnvSubstEquiv at hse
  specialize hse k
  simp only [hlook2] at hse
  cases hk1 : lookup se1 k with
  | none => simp only [hk1] at hse
  | some τ1 => simp only [hk1] at hse; exact ⟨τ1, rfl, hse⟩

/-- populate_call_outputs preserves self_loop_only_empty -/
private lemma populate_call_outputs_self_loop_only_empty
    (env env' : TypeEnv) (as : List Site) (rets : List ParamType) (outRefs : List Aref)
    (hsl : ∀ u p, interpret_regex (env.pathEnv.paths (u, u)) p → p = [])
    (hpop : populate_call_outputs env as rets outRefs = some env') :
    ∀ u p, interpret_regex (env'.pathEnv.paths (u, u)) p → p = [] := by
  induction as generalizing env rets outRefs with
  | nil =>
    cases rets with
    | nil =>
      simp only [populate_call_outputs] at hpop
      split at hpop
      · simp only [Option.some.injEq] at hpop; subst hpop; exact hsl
      · simp at hpop
    | cons _ _ => simp [populate_call_outputs] at hpop
  | cons site as' ih =>
    cases rets with
    | nil => simp [populate_call_outputs] at hpop
    | cons pt rets' =>
      obtain ⟨bt, isRefMut⟩ := pt
      cases isRefMut with
      | none =>
        simp only [populate_call_outputs] at hpop
        exact ih {env with siteEnv := insert env.siteEnv site (.basic bt)} _ _ hsl hpop
      | some b =>
        cases b <;> (
          cases outRefs with
          | nil => simp [populate_call_outputs] at hpop
          | cons r outRefs' =>
            simp only [populate_call_outputs] at hpop
            exact ih {env with siteEnv := insert env.siteEnv site (.ref bt r _),
                               pathEnv := update_with_epsilon r r env.pathEnv} _ _
              (update_with_extension_self_loop_only_empty r r [] env.pathEnv hsl) hpop)

/-- populate_call_outputs preserves paths_from_non_member -/
private lemma populate_call_outputs_paths_from_nm
    (env env' : TypeEnv) (as : List Site) (rets : List ParamType) (outRefs : List Aref)
    (h_from : ∀ u v p, u ∉ env.pathEnv.refs → u ≠ .root → u ≠ v →
      ¬interpret_regex (env.pathEnv.paths (u, v)) p)
    (hpop : populate_call_outputs env as rets outRefs = some env') :
    ∀ u v p, u ∉ env'.pathEnv.refs → u ≠ .root → u ≠ v →
    ¬interpret_regex (env'.pathEnv.paths (u, v)) p := by
  induction as generalizing env rets outRefs with
  | nil =>
    cases rets with
    | nil =>
      simp only [populate_call_outputs] at hpop
      split at hpop
      · simp only [Option.some.injEq] at hpop; subst hpop; exact h_from
      · simp at hpop
    | cons _ _ => simp [populate_call_outputs] at hpop
  | cons site as' ih =>
    cases rets with
    | nil => simp [populate_call_outputs] at hpop
    | cons pt rets' =>
      obtain ⟨bt, isRefMut⟩ := pt
      cases isRefMut with
      | none =>
        simp only [populate_call_outputs] at hpop
        exact ih {env with siteEnv := insert env.siteEnv site (.basic bt)} _ _ h_from hpop
      | some b =>
        cases b <;> (
          cases outRefs with
          | nil => simp [populate_call_outputs] at hpop
          | cons r outRefs' =>
            simp only [populate_call_outputs] at hpop
            exact ih {env with siteEnv := insert env.siteEnv site (.ref bt r _),
                               pathEnv := update_with_epsilon r r env.pathEnv} _ _
              (update_with_extension_paths_from_non_member r r [] env.pathEnv h_from (Or.inr rfl))
              hpop)

/-- populate_call_outputs preserves paths_to_non_member -/
private lemma populate_call_outputs_paths_to_nm
    (env env' : TypeEnv) (as : List Site) (rets : List ParamType) (outRefs : List Aref)
    (h_to : ∀ u v p, v ∉ env.pathEnv.refs → v ≠ .root → u ≠ v →
      ¬interpret_regex (env.pathEnv.paths (u, v)) p)
    (hpop : populate_call_outputs env as rets outRefs = some env') :
    ∀ u v p, v ∉ env'.pathEnv.refs → v ≠ .root → u ≠ v →
    ¬interpret_regex (env'.pathEnv.paths (u, v)) p := by
  induction as generalizing env rets outRefs with
  | nil =>
    cases rets with
    | nil =>
      simp only [populate_call_outputs] at hpop
      split at hpop
      · simp only [Option.some.injEq] at hpop; subst hpop; exact h_to
      · simp at hpop
    | cons _ _ => simp [populate_call_outputs] at hpop
  | cons site as' ih =>
    cases rets with
    | nil => simp [populate_call_outputs] at hpop
    | cons pt rets' =>
      obtain ⟨bt, isRefMut⟩ := pt
      cases isRefMut with
      | none =>
        simp only [populate_call_outputs] at hpop
        exact ih {env with siteEnv := insert env.siteEnv site (.basic bt)} _ _ h_to hpop
      | some b =>
        cases b <;> (
          cases outRefs with
          | nil => simp [populate_call_outputs] at hpop
          | cons r outRefs' =>
            simp only [populate_call_outputs] at hpop
            exact ih {env with siteEnv := insert env.siteEnv site (.ref bt r _),
                               pathEnv := update_with_epsilon r r env.pathEnv} _ _
              (update_with_extension_paths_to_non_member r r [] env.pathEnv h_to (Or.inr rfl))
              hpop)

/-- populate_call_outputs refs are monotone -/
private lemma populate_call_outputs_refs_mono
    (env env' : TypeEnv) (as : List Site) (rets : List ParamType) (outRefs : List Aref)
    (hpop : populate_call_outputs env as rets outRefs = some env') :
    ∀ r ∈ env.pathEnv.refs, r ∈ env'.pathEnv.refs := by
  induction as generalizing env rets outRefs with
  | nil =>
    cases rets with
    | nil =>
      simp only [populate_call_outputs] at hpop
      split at hpop
      · simp only [Option.some.injEq] at hpop; subst hpop; intro r hr; exact hr
      · simp at hpop
    | cons _ _ => simp [populate_call_outputs] at hpop
  | cons site as' ih =>
    cases rets with
    | nil => simp [populate_call_outputs] at hpop
    | cons pt rets' =>
      obtain ⟨bt, isRefMut⟩ := pt
      cases isRefMut with
      | none =>
        simp only [populate_call_outputs] at hpop
        exact ih {env with siteEnv := insert env.siteEnv site (.basic bt)} _ _ hpop
      | some b =>
        cases b <;> (
          cases outRefs with
          | nil => simp [populate_call_outputs] at hpop
          | cons r outRefs' =>
            simp only [populate_call_outputs] at hpop
            intro r' hr'
            exact ih {env with siteEnv := insert env.siteEnv site (.ref bt r _),
                               pathEnv := update_with_epsilon r r env.pathEnv} _ _ hpop r'
              (update_with_extension_refs_mono r r [] env.pathEnv r' hr'))

/-- populate_call_outputs preserves site_tracked -/
private lemma populate_call_outputs_site_tracked
    (env env' : TypeEnv) (as : List Site) (rets : List ParamType) (outRefs : List Aref)
    (hst : ∀ s bt r bk, lookup env.siteEnv s = some (.ref bt r bk) → r ∈ env.pathEnv.refs)
    (hpop : populate_call_outputs env as rets outRefs = some env') :
    ∀ s bt r bk, lookup env'.siteEnv s = some (.ref bt r bk) → r ∈ env'.pathEnv.refs := by
  induction as generalizing env rets outRefs with
  | nil =>
    cases rets with
    | nil =>
      simp only [populate_call_outputs] at hpop
      split at hpop
      · simp only [Option.some.injEq] at hpop; subst hpop; exact hst
      · simp at hpop
    | cons _ _ => simp [populate_call_outputs] at hpop
  | cons site as' ih =>
    cases rets with
    | nil => simp [populate_call_outputs] at hpop
    | cons pt rets' =>
      obtain ⟨bt, isRefMut⟩ := pt
      cases isRefMut with
      | none =>
        simp only [populate_call_outputs] at hpop
        apply ih {env with siteEnv := insert env.siteEnv site (.basic bt)} _ _ _ hpop
        intro s bt' r bk' hlook
        by_cases hs : s = site
        · rw [hs, lookup_insert_same] at hlook; cases hlook
        · rw [lookup_insert_ne _ _ _ _ hs] at hlook; exact hst s bt' r bk' hlook
      | some b =>
        cases b with
        | false =>
          cases outRefs with
          | nil => simp [populate_call_outputs] at hpop
          | cons r outRefs' =>
            simp only [populate_call_outputs] at hpop
            refine ih {env with siteEnv := insert env.siteEnv site (.ref bt r .siteBorrowImm),
                                pathEnv := update_with_epsilon r r env.pathEnv} _ _ ?_ hpop
            show ∀ s bt' r' bk', lookup (insert env.siteEnv site (.ref bt r .siteBorrowImm)) s =
                some (.ref bt' r' bk') → r' ∈ (update_with_epsilon r r env.pathEnv).refs
            intro s bt' r' bk' hlook
            by_cases hs : s = site
            · subst hs; rw [lookup_insert_same] at hlook; cases hlook
              exact update_with_extension_z_mem r r [] env.pathEnv
            · rw [lookup_insert_ne _ _ _ _ hs] at hlook
              exact update_with_extension_refs_mono r r [] env.pathEnv r' (hst s bt' r' bk' hlook)
        | true =>
          cases outRefs with
          | nil => simp [populate_call_outputs] at hpop
          | cons r outRefs' =>
            simp only [populate_call_outputs] at hpop
            refine ih {env with siteEnv := insert env.siteEnv site (.ref bt r .siteBorrowMut),
                                pathEnv := update_with_epsilon r r env.pathEnv} _ _ ?_ hpop
            show ∀ s bt' r' bk', lookup (insert env.siteEnv site (.ref bt r .siteBorrowMut)) s =
                some (.ref bt' r' bk') → r' ∈ (update_with_epsilon r r env.pathEnv).refs
            intro s bt' r' bk' hlook
            by_cases hs : s = site
            · subst hs; rw [lookup_insert_same] at hlook; cases hlook
              exact update_with_extension_z_mem r r [] env.pathEnv
            · rw [lookup_insert_ne _ _ _ _ hs] at hlook
              exact update_with_extension_refs_mono r r [] env.pathEnv r' (hst s bt' r' bk' hlook)

/-- populate_call_outputs preserves var_tracked -/
private lemma populate_call_outputs_var_tracked
    (env env' : TypeEnv) (as : List Site) (rets : List ParamType) (outRefs : List Aref)
    (hvt : ∀ x bt r bk ms, lookup env.varEnv x = some (.validVar, .ref bt r bk, ms) → r ∈ env.pathEnv.refs)
    (hpop : populate_call_outputs env as rets outRefs = some env') :
    ∀ x bt r bk ms, lookup env'.varEnv x = some (.validVar, .ref bt r bk, ms) → r ∈ env'.pathEnv.refs := by
  induction as generalizing env rets outRefs with
  | nil =>
    cases rets with
    | nil =>
      simp only [populate_call_outputs] at hpop
      split at hpop
      · simp only [Option.some.injEq] at hpop; subst hpop; exact hvt
      · simp at hpop
    | cons _ _ => simp [populate_call_outputs] at hpop
  | cons site as' ih =>
    cases rets with
    | nil => simp [populate_call_outputs] at hpop
    | cons pt rets' =>
      obtain ⟨bt, isRefMut⟩ := pt
      cases isRefMut with
      | none =>
        simp only [populate_call_outputs] at hpop
        exact ih {env with siteEnv := insert env.siteEnv site (.basic bt)} _ _ hvt hpop
      | some b =>
        cases b <;> (
          cases outRefs with
          | nil => simp [populate_call_outputs] at hpop
          | cons r outRefs' =>
            simp only [populate_call_outputs] at hpop
            apply ih {env with siteEnv := insert env.siteEnv site (.ref bt r _),
                               pathEnv := update_with_epsilon r r env.pathEnv} _ _ _ hpop
            intro x bt' r' bk' ms hlook
            exact update_with_extension_refs_mono r r [] env.pathEnv r' (hvt x bt' r' bk' ms hlook))

/-- Inserting a basic type into siteEnv preserves freshRefInEnvBool -/
private lemma freshRefInEnvBool_insert_basic (r : Aref) (env : TypeEnv) (site : Site) (bt : BasicMoveType)
    (hfresh : freshRefInEnvBool r env = true) :
    freshRefInEnvBool r {env with siteEnv := insert env.siteEnv site (.basic bt)} = true := by
  simp only [freshRefInEnvBool, Bool.and_eq_true, Bool.not_eq_true',
             List.contains_eq_any_beq] at hfresh ⊢
  obtain ⟨⟨⟨hpe, hve⟩, hse⟩, hnv⟩ := hfresh
  refine ⟨⟨⟨hpe, hve⟩, ?_⟩, hnv⟩
  simp only [collectSiteEnvRefs, AssocMap.insert, List.filterMap_cons, getTypeRef]
  rw [List.any_eq_false]; intro x hx
  rw [List.mem_filterMap] at hx
  obtain ⟨⟨_, τ⟩, hmem, hgt⟩ := hx
  rw [List.mem_filter] at hmem
  have : x ∈ collectSiteEnvRefs env.siteEnv := by
    simp only [collectSiteEnvRefs]
    exact List.mem_filterMap.mpr ⟨(_, τ), hmem.1, hgt⟩
  rw [List.any_eq_false] at hse
  exact hse x this

/-- Inserting a ref type + update_with_epsilon preserves freshRefInEnvBool for different refs -/
private lemma freshRefInEnvBool_insert_ref_update_epsilon (r' r : Aref) (env : TypeEnv)
    (site : Site) (bt : BasicMoveType) (bk : BorrowingKind)
    (hfresh : freshRefInEnvBool r' env = true) (hne : r' ≠ r) :
    freshRefInEnvBool r'
      {env with siteEnv := insert env.siteEnv site (.ref bt r bk),
                pathEnv := update_with_epsilon r r env.pathEnv} = true := by
  simp only [freshRefInEnvBool, Bool.and_eq_true, Bool.not_eq_true',
             List.contains_eq_any_beq] at hfresh ⊢
  obtain ⟨⟨⟨hpe, hve⟩, hse⟩, hnv⟩ := hfresh
  refine ⟨⟨⟨?_, hve⟩, ?_⟩, hnv⟩
  · -- freshRefBool r' (update_with_epsilon r r env.pathEnv)
    simp only [freshRefBool, Bool.not_eq_true', List.contains_eq_any_beq] at hpe ⊢
    simp only [update_with_epsilon, update_with_extension]
    split
    · -- r ∉ pe.refs: refs' = r :: pe.refs
      rw [List.any_cons, show (r' == r) = false from beq_false_of_ne hne, Bool.false_or]
      exact hpe
    · exact hpe
  · -- r' ∉ collectSiteEnvRefs (insert env.siteEnv site (.ref bt r bk))
    simp only [collectSiteEnvRefs, AssocMap.insert, List.filterMap_cons, getTypeRef]
    rw [List.any_eq_false]; intro x hx
    simp only [List.mem_cons] at hx
    cases hx with
    | inl heq => rw [heq]; simp only [beq_iff_eq]; exact hne
    | inr hmem =>
      rw [List.mem_filterMap] at hmem
      obtain ⟨⟨_, τ⟩, hmem', hgt⟩ := hmem
      rw [List.mem_filter] at hmem'
      have : x ∈ collectSiteEnvRefs env.siteEnv := by
        simp only [collectSiteEnvRefs]
        exact List.mem_filterMap.mpr ⟨(_, τ), hmem'.1, hgt⟩
      rw [List.any_eq_false] at hse
      exact hse x this

/-- populate_call_outputs preserves RefsUnique -/
private lemma populate_call_outputs_RefsUnique
    (env env' : TypeEnv) (as : List Site) (rets : List ParamType) (outRefs : List Aref)
    (huniq : RefsUnique env.varEnv env.siteEnv)
    (hfresh : all_refs_fresh_in_env env outRefs)
    (hnodup : List.Nodup outRefs)
    (hpop : populate_call_outputs env as rets outRefs = some env') :
    RefsUnique env'.varEnv env'.siteEnv := by
  induction as generalizing env rets outRefs with
  | nil =>
    cases rets with
    | nil =>
      simp only [populate_call_outputs] at hpop
      split at hpop
      · simp only [Option.some.injEq] at hpop; subst hpop; exact huniq
      · simp at hpop
    | cons _ _ => simp [populate_call_outputs] at hpop
  | cons site as' ih =>
    cases rets with
    | nil => simp [populate_call_outputs] at hpop
    | cons pt rets' =>
      obtain ⟨bt, isRefMut⟩ := pt
      cases isRefMut with
      | none =>
        simp only [populate_call_outputs] at hpop
        exact ih {env with siteEnv := insert env.siteEnv site (.basic bt)} _ _
          (RefsUnique_insert_basic env.varEnv env.siteEnv site bt huniq)
          (fun r hr =>
            let hb := freshRefInEnvBool_insert_basic r env site bt
              ((freshRefInEnv_iff_freshRefInEnvBool r env).mp (hfresh r hr))
            (freshRefInEnv_iff_freshRefInEnvBool r _).mpr hb)
          hnodup hpop
      | some b =>
        cases b <;> (
          cases outRefs with
          | nil => simp [populate_call_outputs] at hpop
          | cons r outRefs' =>
            simp only [populate_call_outputs] at hpop
            have hr_fresh := hfresh r (List.mem_cons.mpr (Or.inl rfl))
            exact ih _ _ _
              (RefsUnique_insert_fresh_ref env.varEnv env.siteEnv site bt r _ huniq
                (fun x bt' r' bk' ms hlook =>
                  (freshRefInEnv_ne_varEnv_ref r env x .validVar bt' r' bk' ms hr_fresh hlook).symm)
                (fun s bt' r' bk' hlook =>
                  (freshRefInEnv_ne_siteEnv_ref r env s bt' r' bk' hr_fresh hlook).symm))
              (fun r' hr' =>
                let hb := freshRefInEnvBool_insert_ref_update_epsilon r' r env site bt _
                  ((freshRefInEnv_iff_freshRefInEnvBool r' env).mp (hfresh r' (List.mem_cons.mpr (Or.inr hr'))))
                  (fun heq => (List.nodup_cons.mp hnodup).1 (heq ▸ hr'))
                (freshRefInEnv_iff_freshRefInEnvBool r' _).mpr hb)
              ((List.nodup_cons.mp hnodup).2)
              hpop)

/-- Specialized foldl lemma: if each step preserves refs membership, then foldl does too -/
private lemma foldl_refs_mono {β : Type} (f : PathEnv → β → PathEnv) (pe : PathEnv)
    (l : List β) (r : Aref) (hr : r ∈ pe.refs)
    (hstep : ∀ (acc : PathEnv) (b : β), r ∈ acc.refs → r ∈ (f acc b).refs) :
    r ∈ (l.foldl f pe).refs := by
  induction l generalizing pe with
  | nil => exact hr
  | cons x xs ih => exact ih (f pe x) (hstep pe x hr)

/-- Specialized foldl lemma: if each step preserves self_loop_only_empty, then foldl does too -/
private lemma foldl_self_loop {β : Type} (f : PathEnv → β → PathEnv) (pe : PathEnv)
    (l : List β)
    (hsl : ∀ u p, interpret_regex (pe.paths (u, u)) p → p = [])
    (hstep : ∀ (acc : PathEnv) (b : β),
      (∀ u p, interpret_regex (acc.paths (u, u)) p → p = []) →
      (∀ u p, interpret_regex ((f acc b).paths (u, u)) p → p = [])) :
    ∀ u p, interpret_regex ((l.foldl f pe).paths (u, u)) p → p = [] := by
  induction l generalizing pe with
  | nil => exact hsl
  | cons x xs ih => exact ih (f pe x) (hstep pe x hsl)

/-- Specialized foldl lemma: if each step preserves paths_to_nm, then foldl does too -/
private lemma foldl_paths_to_nm {β : Type} (f : PathEnv → β → PathEnv) (pe : PathEnv)
    (l : List β)
    (h_to : ∀ u v p, v ∉ pe.refs → v ≠ .root → u ≠ v → ¬interpret_regex (pe.paths (u, v)) p)
    (hstep : ∀ (acc : PathEnv) (b : β),
      (∀ u v p, v ∉ acc.refs → v ≠ .root → u ≠ v → ¬interpret_regex (acc.paths (u, v)) p) →
      (∀ u v p, v ∉ (f acc b).refs → v ≠ .root → u ≠ v → ¬interpret_regex ((f acc b).paths (u, v)) p)) :
    ∀ u v p, v ∉ (l.foldl f pe).refs → v ≠ .root → u ≠ v →
      ¬interpret_regex ((l.foldl f pe).paths (u, v)) p := by
  induction l generalizing pe with
  | nil => exact h_to
  | cons x xs ih => exact ih (f pe x) (hstep pe x h_to)

/-- Specialized foldl lemma: if each step preserves paths_from_nm, then foldl does too -/
private lemma foldl_paths_from_nm {β : Type} (f : PathEnv → β → PathEnv) (pe : PathEnv)
    (l : List β)
    (h_from : ∀ u v p, u ∉ pe.refs → u ≠ .root → u ≠ v → ¬interpret_regex (pe.paths (u, v)) p)
    (hstep : ∀ (acc : PathEnv) (b : β),
      (∀ u v p, u ∉ acc.refs → u ≠ .root → u ≠ v → ¬interpret_regex (acc.paths (u, v)) p) →
      (∀ u v p, u ∉ (f acc b).refs → u ≠ .root → u ≠ v → ¬interpret_regex ((f acc b).paths (u, v)) p)) :
    ∀ u v p, u ∉ (l.foldl f pe).refs → u ≠ .root → u ≠ v →
      ¬interpret_regex ((l.foldl f pe).paths (u, v)) p := by
  induction l generalizing pe with
  | nil => exact h_from
  | cons x xs ih => exact ih (f pe x) (hstep pe x h_from)

/-- call_connect refs are monotone -/
private lemma call_connect_refs_mono
    (env : TypeEnv) (as bs : List Site) :
    ∀ r ∈ env.pathEnv.refs, r ∈ (call_connect_inputs_outputs env as bs).pathEnv.refs := by
  intro r hr
  unfold call_connect_inputs_outputs
  dsimp only []
  -- Rule 3 (outermost foldl)
  apply foldl_refs_mono _ _ _ _ ?_ fun acc io1 hacc =>
    foldl_refs_mono _ _ _ _ hacc fun acc' io2 hacc' => by
      simp only [ne_eq]; split
      · exact extend_with_star_refs_mono io1 io2 acc' r hacc'
      · exact hacc'
  -- Rule 2
  apply foldl_refs_mono _ _ _ _ ?_ fun acc mout hacc =>
    foldl_refs_mono _ _ _ _ hacc fun acc' minput hacc' =>
      extend_with_star_refs_mono mout minput acc' r hacc'
  -- Rule 1
  exact foldl_refs_mono _ _ _ _ hr fun acc iout hacc =>
    foldl_refs_mono _ _ _ _ hacc fun acc' input hacc' =>
      extend_with_star_refs_mono iout input acc' r hacc'

/-- call_connect preserves self_loop_only_empty -/
private lemma call_connect_self_loop_only_empty
    (env : TypeEnv) (as bs : List Site)
    (hsl : ∀ u p, interpret_regex (env.pathEnv.paths (u, u)) p → p = []) :
    ∀ u p, interpret_regex ((call_connect_inputs_outputs env as bs).pathEnv.paths (u, u)) p → p = [] := by
  unfold call_connect_inputs_outputs
  dsimp only []
  -- Rule 3 (outermost)
  apply foldl_self_loop _ _ _ ?_ fun acc io1 hacc =>
    foldl_self_loop _ _ _ hacc fun acc' io2 hacc' => by
      simp only [ne_eq]; split
      · exact extend_with_star_self_loop_only_empty io1 io2 acc' hacc'
      · exact hacc'
  -- Rule 2
  apply foldl_self_loop _ _ _ ?_ fun acc mout hacc =>
    foldl_self_loop _ _ _ hacc fun acc' minput hacc' =>
      extend_with_star_self_loop_only_empty mout minput acc' hacc'
  -- Rule 1
  exact foldl_self_loop _ _ _ hsl fun acc iout hacc =>
    foldl_self_loop _ _ _ hacc fun acc' input hacc' =>
      extend_with_star_self_loop_only_empty iout input acc' hacc'

/-- Inner foldl of unconditional extend_with_star preserves paths_to_nm with refs monotonicity -/
private lemma inner_foldl_ews_paths_to_nm (target : Aref) (sources : List Aref) (pe : PathEnv)
    (h_to : ∀ u v p, v ∉ pe.refs → v ≠ .root → u ≠ v → ¬interpret_regex (pe.paths (u, v)) p)
    (hsources : ∀ s ∈ sources, s ∈ pe.refs) :
    (∀ u v p, v ∉ (sources.foldl (fun acc source => extend_with_star target source acc) pe).refs →
      v ≠ .root → u ≠ v →
      ¬interpret_regex ((sources.foldl (fun acc source => extend_with_star target source acc) pe).paths (u, v)) p) ∧
    (∀ r ∈ pe.refs, r ∈ (sources.foldl (fun acc source => extend_with_star target source acc) pe).refs) := by
  induction sources generalizing pe with
  | nil => exact ⟨h_to, fun r hr => hr⟩
  | cons s ss ih =>
    simp only [List.foldl_cons]
    have hsrc : s ∈ pe.refs := hsources s (List.mem_cons.mpr (Or.inl rfl))
    have ⟨ih_to, ih_mono⟩ := ih (extend_with_star target s pe)
      (extend_with_star_paths_to_non_member target s pe h_to (Or.inl hsrc))
      (fun s' hs' => extend_with_star_refs_mono target s pe s'
        (hsources s' (List.mem_cons.mpr (Or.inr hs'))))
    exact ⟨ih_to, fun r hr => ih_mono r (extend_with_star_refs_mono target s pe r hr)⟩

/-- Outer foldl of unconditional extend_with_star preserves paths_to_nm with refs monotonicity -/
private lemma outer_foldl_ews_paths_to_nm (targets sources : List Aref) (pe : PathEnv)
    (h_to : ∀ u v p, v ∉ pe.refs → v ≠ .root → u ≠ v → ¬interpret_regex (pe.paths (u, v)) p)
    (hsources : ∀ s ∈ sources, s ∈ pe.refs)
    (htargets : ∀ t ∈ targets, t ∈ pe.refs) :
    (∀ u v p, v ∉ (targets.foldl (fun acc target =>
      sources.foldl (fun acc' source => extend_with_star target source acc') acc) pe).refs →
      v ≠ .root → u ≠ v →
      ¬interpret_regex ((targets.foldl (fun acc target =>
        sources.foldl (fun acc' source => extend_with_star target source acc') acc) pe).paths (u, v)) p) ∧
    (∀ r ∈ pe.refs, r ∈ (targets.foldl (fun acc target =>
      sources.foldl (fun acc' source => extend_with_star target source acc') acc) pe).refs) := by
  induction targets generalizing pe with
  | nil => exact ⟨h_to, fun r hr => hr⟩
  | cons t ts ih =>
    simp only [List.foldl_cons]
    have ⟨h1_to, h1_mono⟩ := inner_foldl_ews_paths_to_nm t sources pe h_to hsources
    have ⟨ih_to, ih_mono⟩ := ih (sources.foldl (fun acc' source => extend_with_star t source acc') pe) h1_to
      (fun s hs => h1_mono s (hsources s hs))
      (fun t' ht' => h1_mono t' (htargets t' (List.mem_cons.mpr (Or.inr ht'))))
    exact ⟨ih_to, fun r hr => ih_mono r (h1_mono r hr)⟩

/-- Inner foldl of conditional extend_with_star preserves paths_to_nm with refs monotonicity -/
private lemma inner_foldl_cond_ews_paths_to_nm (target : Aref) (sources : List Aref) (pe : PathEnv)
    (h_to : ∀ u v p, v ∉ pe.refs → v ≠ .root → u ≠ v → ¬interpret_regex (pe.paths (u, v)) p)
    (hsources : ∀ s ∈ sources, s ∈ pe.refs) :
    (∀ u v p, v ∉ (sources.foldl (fun acc source =>
      if target ≠ source then extend_with_star target source acc else acc) pe).refs →
      v ≠ .root → u ≠ v →
      ¬interpret_regex ((sources.foldl (fun acc source =>
        if target ≠ source then extend_with_star target source acc else acc) pe).paths (u, v)) p) ∧
    (∀ r ∈ pe.refs, r ∈ (sources.foldl (fun acc source =>
      if target ≠ source then extend_with_star target source acc else acc) pe).refs) := by
  induction sources generalizing pe with
  | nil => exact ⟨h_to, fun r hr => hr⟩
  | cons s ss ih =>
    simp only [List.foldl_cons]
    by_cases h : target ≠ s
    · rw [if_pos h]
      have hsrc : s ∈ pe.refs := hsources s (List.mem_cons.mpr (Or.inl rfl))
      have ⟨ih_to, ih_mono⟩ := ih (extend_with_star target s pe)
        (extend_with_star_paths_to_non_member target s pe h_to (Or.inl hsrc))
        (fun s' hs' => extend_with_star_refs_mono target s pe s'
          (hsources s' (List.mem_cons.mpr (Or.inr hs'))))
      exact ⟨ih_to, fun r hr => ih_mono r (extend_with_star_refs_mono target s pe r hr)⟩
    · rw [if_neg h]
      exact ih pe h_to (fun s' hs' => hsources s' (List.mem_cons.mpr (Or.inr hs')))

/-- Outer foldl of conditional extend_with_star preserves paths_to_nm with refs monotonicity -/
private lemma outer_foldl_cond_ews_paths_to_nm (targets sources : List Aref) (pe : PathEnv)
    (h_to : ∀ u v p, v ∉ pe.refs → v ≠ .root → u ≠ v → ¬interpret_regex (pe.paths (u, v)) p)
    (hsources : ∀ s ∈ sources, s ∈ pe.refs)
    (htargets : ∀ t ∈ targets, t ∈ pe.refs) :
    (∀ u v p, v ∉ (targets.foldl (fun acc target =>
      sources.foldl (fun acc' source =>
        if target ≠ source then extend_with_star target source acc' else acc') acc) pe).refs →
      v ≠ .root → u ≠ v →
      ¬interpret_regex ((targets.foldl (fun acc target =>
        sources.foldl (fun acc' source =>
          if target ≠ source then extend_with_star target source acc' else acc') acc) pe).paths (u, v)) p) ∧
    (∀ r ∈ pe.refs, r ∈ (targets.foldl (fun acc target =>
      sources.foldl (fun acc' source =>
        if target ≠ source then extend_with_star target source acc' else acc') acc) pe).refs) := by
  induction targets generalizing pe with
  | nil => exact ⟨h_to, fun r hr => hr⟩
  | cons t ts ih =>
    simp only [List.foldl_cons]
    have ⟨h1_to, h1_mono⟩ := inner_foldl_cond_ews_paths_to_nm t sources pe h_to hsources
    have ⟨ih_to, ih_mono⟩ := ih (sources.foldl (fun acc' source =>
        if t ≠ source then extend_with_star t source acc' else acc') pe) h1_to
      (fun s hs => h1_mono s (hsources s hs))
      (fun t' ht' => h1_mono t' (htargets t' (List.mem_cons.mpr (Or.inr ht'))))
    exact ⟨ih_to, fun r hr => ih_mono r (h1_mono r hr)⟩

/-- Inner foldl of unconditional extend_with_star preserves paths_from_nm with refs monotonicity -/
private lemma inner_foldl_ews_paths_from_nm (target : Aref) (sources : List Aref) (pe : PathEnv)
    (h_from : ∀ u v p, u ∉ pe.refs → u ≠ .root → u ≠ v → ¬interpret_regex (pe.paths (u, v)) p)
    (hsources : ∀ s ∈ sources, s ∈ pe.refs) :
    (∀ u v p, u ∉ (sources.foldl (fun acc source => extend_with_star target source acc) pe).refs →
      u ≠ .root → u ≠ v →
      ¬interpret_regex ((sources.foldl (fun acc source => extend_with_star target source acc) pe).paths (u, v)) p) ∧
    (∀ r ∈ pe.refs, r ∈ (sources.foldl (fun acc source => extend_with_star target source acc) pe).refs) := by
  induction sources generalizing pe with
  | nil => exact ⟨h_from, fun r hr => hr⟩
  | cons s ss ih =>
    simp only [List.foldl_cons]
    have hsrc : s ∈ pe.refs := hsources s (List.mem_cons.mpr (Or.inl rfl))
    have ⟨ih_from, ih_mono⟩ := ih (extend_with_star target s pe)
      (extend_with_star_paths_from_non_member target s pe h_from (Or.inl hsrc))
      (fun s' hs' => extend_with_star_refs_mono target s pe s'
        (hsources s' (List.mem_cons.mpr (Or.inr hs'))))
    exact ⟨ih_from, fun r hr => ih_mono r (extend_with_star_refs_mono target s pe r hr)⟩

/-- Outer foldl of unconditional extend_with_star preserves paths_from_nm with refs monotonicity -/
private lemma outer_foldl_ews_paths_from_nm (targets sources : List Aref) (pe : PathEnv)
    (h_from : ∀ u v p, u ∉ pe.refs → u ≠ .root → u ≠ v → ¬interpret_regex (pe.paths (u, v)) p)
    (hsources : ∀ s ∈ sources, s ∈ pe.refs)
    (htargets : ∀ t ∈ targets, t ∈ pe.refs) :
    (∀ u v p, u ∉ (targets.foldl (fun acc target =>
      sources.foldl (fun acc' source => extend_with_star target source acc') acc) pe).refs →
      u ≠ .root → u ≠ v →
      ¬interpret_regex ((targets.foldl (fun acc target =>
        sources.foldl (fun acc' source => extend_with_star target source acc') acc) pe).paths (u, v)) p) ∧
    (∀ r ∈ pe.refs, r ∈ (targets.foldl (fun acc target =>
      sources.foldl (fun acc' source => extend_with_star target source acc') acc) pe).refs) := by
  induction targets generalizing pe with
  | nil => exact ⟨h_from, fun r hr => hr⟩
  | cons t ts ih =>
    simp only [List.foldl_cons]
    have ⟨h1_from, h1_mono⟩ := inner_foldl_ews_paths_from_nm t sources pe h_from hsources
    have ⟨ih_from, ih_mono⟩ := ih (sources.foldl (fun acc' source => extend_with_star t source acc') pe) h1_from
      (fun s hs => h1_mono s (hsources s hs))
      (fun t' ht' => h1_mono t' (htargets t' (List.mem_cons.mpr (Or.inr ht'))))
    exact ⟨ih_from, fun r hr => ih_mono r (h1_mono r hr)⟩

/-- Inner foldl of conditional extend_with_star preserves paths_from_nm with refs monotonicity -/
private lemma inner_foldl_cond_ews_paths_from_nm (target : Aref) (sources : List Aref) (pe : PathEnv)
    (h_from : ∀ u v p, u ∉ pe.refs → u ≠ .root → u ≠ v → ¬interpret_regex (pe.paths (u, v)) p)
    (hsources : ∀ s ∈ sources, s ∈ pe.refs) :
    (∀ u v p, u ∉ (sources.foldl (fun acc source =>
      if target ≠ source then extend_with_star target source acc else acc) pe).refs →
      u ≠ .root → u ≠ v →
      ¬interpret_regex ((sources.foldl (fun acc source =>
        if target ≠ source then extend_with_star target source acc else acc) pe).paths (u, v)) p) ∧
    (∀ r ∈ pe.refs, r ∈ (sources.foldl (fun acc source =>
      if target ≠ source then extend_with_star target source acc else acc) pe).refs) := by
  induction sources generalizing pe with
  | nil => exact ⟨h_from, fun r hr => hr⟩
  | cons s ss ih =>
    simp only [List.foldl_cons]
    by_cases h : target ≠ s
    · rw [if_pos h]
      have hsrc : s ∈ pe.refs := hsources s (List.mem_cons.mpr (Or.inl rfl))
      have ⟨ih_from, ih_mono⟩ := ih (extend_with_star target s pe)
        (extend_with_star_paths_from_non_member target s pe h_from (Or.inl hsrc))
        (fun s' hs' => extend_with_star_refs_mono target s pe s'
          (hsources s' (List.mem_cons.mpr (Or.inr hs'))))
      exact ⟨ih_from, fun r hr => ih_mono r (extend_with_star_refs_mono target s pe r hr)⟩
    · rw [if_neg h]
      exact ih pe h_from (fun s' hs' => hsources s' (List.mem_cons.mpr (Or.inr hs')))

/-- Outer foldl of conditional extend_with_star preserves paths_from_nm with refs monotonicity -/
private lemma outer_foldl_cond_ews_paths_from_nm (targets sources : List Aref) (pe : PathEnv)
    (h_from : ∀ u v p, u ∉ pe.refs → u ≠ .root → u ≠ v → ¬interpret_regex (pe.paths (u, v)) p)
    (hsources : ∀ s ∈ sources, s ∈ pe.refs)
    (htargets : ∀ t ∈ targets, t ∈ pe.refs) :
    (∀ u v p, u ∉ (targets.foldl (fun acc target =>
      sources.foldl (fun acc' source =>
        if target ≠ source then extend_with_star target source acc' else acc') acc) pe).refs →
      u ≠ .root → u ≠ v →
      ¬interpret_regex ((targets.foldl (fun acc target =>
        sources.foldl (fun acc' source =>
          if target ≠ source then extend_with_star target source acc' else acc') acc) pe).paths (u, v)) p) ∧
    (∀ r ∈ pe.refs, r ∈ (targets.foldl (fun acc target =>
      sources.foldl (fun acc' source =>
        if target ≠ source then extend_with_star target source acc' else acc') acc) pe).refs) := by
  induction targets generalizing pe with
  | nil => exact ⟨h_from, fun r hr => hr⟩
  | cons t ts ih =>
    simp only [List.foldl_cons]
    have ⟨h1_from, h1_mono⟩ := inner_foldl_cond_ews_paths_from_nm t sources pe h_from hsources
    have ⟨ih_from, ih_mono⟩ := ih (sources.foldl (fun acc' source =>
        if t ≠ source then extend_with_star t source acc' else acc') pe) h1_from
      (fun s hs => h1_mono s (hsources s hs))
      (fun t' ht' => h1_mono t' (htargets t' (List.mem_cons.mpr (Or.inr ht'))))
    exact ⟨ih_from, fun r hr => ih_mono r (h1_mono r hr)⟩

/-- call_connect preserves paths_to_non_member given site_tracked -/
private lemma call_connect_paths_to_nm
    (env : TypeEnv) (as bs : List Site)
    (h_to : ∀ u v p, v ∉ env.pathEnv.refs → v ≠ .root → u ≠ v →
      ¬interpret_regex (env.pathEnv.paths (u, v)) p)
    (hst : ∀ s bt r bk, lookup env.siteEnv s = some (.ref bt r bk) → r ∈ env.pathEnv.refs) :
    ∀ u v p, v ∉ (call_connect_inputs_outputs env as bs).pathEnv.refs → v ≠ .root → u ≠ v →
    ¬interpret_regex ((call_connect_inputs_outputs env as bs).pathEnv.paths (u, v)) p := by
  -- Extract tracked source lists
  have hinputs_tracked : ∀ s ∈ List.filterMap (fun a => match lookup env.siteEnv a with
      | some (.ref _ r _) => some r | _ => none) bs, s ∈ env.pathEnv.refs := by
    intro r hr; rw [List.mem_filterMap] at hr; obtain ⟨a, _, ha⟩ := hr
    revert ha; cases hlook : lookup env.siteEnv a with
    | none => simp
    | some τ => cases τ with
      | basic _ => simp
      | ref bt' r' bk' => simp only [Option.some.injEq]; intro h; subst h; exact hst a bt' r' bk' hlook
  have hio_tracked : ∀ s ∈ List.filterMap (fun a => match lookup env.siteEnv a with
      | some (.ref _ r .siteBorrowImm) => some r | _ => none) as, s ∈ env.pathEnv.refs := by
    intro r hr; rw [List.mem_filterMap] at hr; obtain ⟨a, _, ha⟩ := hr
    revert ha; cases hlook : lookup env.siteEnv a with
    | none => simp
    | some τ => cases τ with
      | basic _ => simp
      | ref bt' r' bk' => cases bk' with
          | siteBorrowImm => simp only [Option.some.injEq]; intro h; subst h; exact hst a bt' r' _ hlook
          | siteBorrowMut => simp
  have hmi_tracked : ∀ s ∈ List.filterMap (fun a => match lookup env.siteEnv a with
      | some (.ref _ r .siteBorrowMut) => some r | _ => none) bs, s ∈ env.pathEnv.refs := by
    intro r hr; rw [List.mem_filterMap] at hr; obtain ⟨a, _, ha⟩ := hr
    revert ha; cases hlook : lookup env.siteEnv a with
    | none => simp
    | some τ => cases τ with
      | basic _ => simp
      | ref bt' r' bk' => cases bk' with
          | siteBorrowImm => simp
          | siteBorrowMut => simp only [Option.some.injEq]; intro h; subst h; exact hst a bt' r' _ hlook
  have hmo_tracked : ∀ s ∈ List.filterMap (fun a => match lookup env.siteEnv a with
      | some (.ref _ r .siteBorrowMut) => some r | _ => none) as, s ∈ env.pathEnv.refs := by
    intro r hr; rw [List.mem_filterMap] at hr; obtain ⟨a, _, ha⟩ := hr
    revert ha; cases hlook : lookup env.siteEnv a with
    | none => simp
    | some τ => cases τ with
      | basic _ => simp
      | ref bt' r' bk' => cases bk' with
          | siteBorrowImm => simp
          | siteBorrowMut => simp only [Option.some.injEq]; intro h; subst h; exact hst a bt' r' _ hlook
  -- Unfold and apply Rules 1-3
  unfold call_connect_inputs_outputs
  dsimp only []
  -- Rule 1
  have ⟨h1_to, h1_mono⟩ := outer_foldl_ews_paths_to_nm _ _ env.pathEnv h_to
    hinputs_tracked hio_tracked
  -- Rule 2
  have ⟨h2_to, h2_mono⟩ := outer_foldl_ews_paths_to_nm _ _ _ h1_to
    (fun s hs => h1_mono s (hmi_tracked s hs))
    (fun t ht => h1_mono t (hmo_tracked t ht))
  -- Rule 3 (conditional)
  exact (outer_foldl_cond_ews_paths_to_nm _ _ _ h2_to
    (fun s hs => h2_mono s (h1_mono s (hio_tracked s hs)))
    (fun t ht => h2_mono t (h1_mono t (hio_tracked t ht)))).1

/-- call_connect preserves paths_from_non_member given site_tracked -/
private lemma call_connect_paths_from_nm
    (env : TypeEnv) (as bs : List Site)
    (h_from : ∀ u v p, u ∉ env.pathEnv.refs → u ≠ .root → u ≠ v →
      ¬interpret_regex (env.pathEnv.paths (u, v)) p)
    (hst : ∀ s bt r bk, lookup env.siteEnv s = some (.ref bt r bk) → r ∈ env.pathEnv.refs) :
    ∀ u v p, u ∉ (call_connect_inputs_outputs env as bs).pathEnv.refs → u ≠ .root → u ≠ v →
    ¬interpret_regex ((call_connect_inputs_outputs env as bs).pathEnv.paths (u, v)) p := by
  -- Extract tracked source lists
  have hinputs_tracked : ∀ s ∈ List.filterMap (fun a => match lookup env.siteEnv a with
      | some (.ref _ r _) => some r | _ => none) bs, s ∈ env.pathEnv.refs := by
    intro r hr; rw [List.mem_filterMap] at hr; obtain ⟨a, _, ha⟩ := hr
    revert ha; cases hlook : lookup env.siteEnv a with
    | none => simp
    | some τ => cases τ with
      | basic _ => simp
      | ref bt' r' bk' => simp only [Option.some.injEq]; intro h; subst h; exact hst a bt' r' bk' hlook
  have hio_tracked : ∀ s ∈ List.filterMap (fun a => match lookup env.siteEnv a with
      | some (.ref _ r .siteBorrowImm) => some r | _ => none) as, s ∈ env.pathEnv.refs := by
    intro r hr; rw [List.mem_filterMap] at hr; obtain ⟨a, _, ha⟩ := hr
    revert ha; cases hlook : lookup env.siteEnv a with
    | none => simp
    | some τ => cases τ with
      | basic _ => simp
      | ref bt' r' bk' => cases bk' with
          | siteBorrowImm => simp only [Option.some.injEq]; intro h; subst h; exact hst a bt' r' _ hlook
          | siteBorrowMut => simp
  have hmi_tracked : ∀ s ∈ List.filterMap (fun a => match lookup env.siteEnv a with
      | some (.ref _ r .siteBorrowMut) => some r | _ => none) bs, s ∈ env.pathEnv.refs := by
    intro r hr; rw [List.mem_filterMap] at hr; obtain ⟨a, _, ha⟩ := hr
    revert ha; cases hlook : lookup env.siteEnv a with
    | none => simp
    | some τ => cases τ with
      | basic _ => simp
      | ref bt' r' bk' => cases bk' with
          | siteBorrowImm => simp
          | siteBorrowMut => simp only [Option.some.injEq]; intro h; subst h; exact hst a bt' r' _ hlook
  have hmo_tracked : ∀ s ∈ List.filterMap (fun a => match lookup env.siteEnv a with
      | some (.ref _ r .siteBorrowMut) => some r | _ => none) as, s ∈ env.pathEnv.refs := by
    intro r hr; rw [List.mem_filterMap] at hr; obtain ⟨a, _, ha⟩ := hr
    revert ha; cases hlook : lookup env.siteEnv a with
    | none => simp
    | some τ => cases τ with
      | basic _ => simp
      | ref bt' r' bk' => cases bk' with
          | siteBorrowImm => simp
          | siteBorrowMut => simp only [Option.some.injEq]; intro h; subst h; exact hst a bt' r' _ hlook
  -- Unfold and apply Rules 1-3
  unfold call_connect_inputs_outputs
  dsimp only []
  -- Rule 1
  have ⟨h1_from, h1_mono⟩ := outer_foldl_ews_paths_from_nm _ _ env.pathEnv h_from
    hinputs_tracked hio_tracked
  -- Rule 2
  have ⟨h2_from, h2_mono⟩ := outer_foldl_ews_paths_from_nm _ _ _ h1_from
    (fun s hs => h1_mono s (hmi_tracked s hs))
    (fun t ht => h1_mono t (hmo_tracked t ht))
  -- Rule 3 (conditional)
  exact (outer_foldl_cond_ews_paths_from_nm _ _ _ h2_from
    (fun s hs => h2_mono s (h1_mono s (hio_tracked s hs)))
    (fun t ht => h2_mono t (h1_mono t (hio_tracked t ht)))).1

/-- extend_with_star doesn't change refs when target is already tracked -/
private lemma extend_with_star_refs_eq (target source : Aref) (pe : PathEnv)
    (h : target ∈ pe.refs) :
    (extend_with_star target source pe).refs = pe.refs := by
  simp only [extend_with_star, h, not_true_eq_false, ↓reduceIte]

/-- Inner foldl of extend_with_star preserves refs exactly -/
private lemma inner_foldl_ews_refs_eq (target : Aref) (sources : List Aref) (pe : PathEnv)
    (h : target ∈ pe.refs) :
    (sources.foldl (fun acc source => extend_with_star target source acc) pe).refs = pe.refs := by
  induction sources generalizing pe with
  | nil => rfl
  | cons s ss ih =>
    simp only [List.foldl_cons]
    rw [ih (extend_with_star target s pe) (by rw [extend_with_star_refs_eq target s pe h]; exact h)]
    exact extend_with_star_refs_eq target s pe h

/-- Outer foldl of extend_with_star preserves refs exactly -/
private lemma outer_foldl_ews_refs_eq (targets sources : List Aref) (pe : PathEnv)
    (htargets : ∀ t ∈ targets, t ∈ pe.refs) :
    (targets.foldl (fun acc target =>
      sources.foldl (fun acc' source => extend_with_star target source acc') acc) pe).refs = pe.refs := by
  induction targets generalizing pe with
  | nil => rfl
  | cons t ts ih =>
    simp only [List.foldl_cons]
    have h1 := inner_foldl_ews_refs_eq t sources pe (htargets t (List.mem_cons.mpr (Or.inl rfl)))
    rw [ih _ (fun t' ht' => by rw [h1]; exact htargets t' (List.mem_cons.mpr (Or.inr ht')))]
    exact h1

/-- Inner conditional foldl of extend_with_star preserves refs exactly -/
private lemma inner_foldl_cond_ews_refs_eq (target : Aref) (sources : List Aref) (pe : PathEnv)
    (h : target ∈ pe.refs) :
    (sources.foldl (fun acc source =>
      if target ≠ source then extend_with_star target source acc else acc) pe).refs = pe.refs := by
  induction sources generalizing pe with
  | nil => rfl
  | cons s ss ih =>
    simp only [List.foldl_cons]
    by_cases hne : target ≠ s
    · rw [if_pos hne]
      rw [ih _ (by rw [extend_with_star_refs_eq target s pe h]; exact h)]
      exact extend_with_star_refs_eq target s pe h
    · rw [if_neg hne]; exact ih pe h

/-- Outer conditional foldl of extend_with_star preserves refs exactly -/
private lemma outer_foldl_cond_ews_refs_eq (targets sources : List Aref) (pe : PathEnv)
    (htargets : ∀ t ∈ targets, t ∈ pe.refs) :
    (targets.foldl (fun acc target =>
      sources.foldl (fun acc' source =>
        if target ≠ source then extend_with_star target source acc' else acc') acc) pe).refs = pe.refs := by
  induction targets generalizing pe with
  | nil => rfl
  | cons t ts ih =>
    simp only [List.foldl_cons]
    have h1 := inner_foldl_cond_ews_refs_eq t sources pe (htargets t (List.mem_cons.mpr (Or.inl rfl)))
    rw [ih _ (fun t' ht' => by rw [h1]; exact htargets t' (List.mem_cons.mpr (Or.inr ht')))]
    exact h1

/-- call_connect preserves refs exactly when site_tracked holds -/
private lemma call_connect_refs_eq
    (env : TypeEnv) (as bs : List Site)
    (hst : ∀ s bt r bk, lookup env.siteEnv s = some (.ref bt r bk) → r ∈ env.pathEnv.refs) :
    (call_connect_inputs_outputs env as bs).pathEnv.refs = env.pathEnv.refs := by
  -- Define the filterMap lists to match call_connect_inputs_outputs internals
  let inputs := List.filterMap (fun a => match lookup env.siteEnv a with
      | some (.ref _ r _) => some r | _ => none) bs
  let io := List.filterMap (fun a => match lookup env.siteEnv a with
      | some (.ref _ r .siteBorrowImm) => some r | _ => none) as
  let mi := List.filterMap (fun a => match lookup env.siteEnv a with
      | some (.ref _ r .siteBorrowMut) => some r | _ => none) bs
  let mo := List.filterMap (fun a => match lookup env.siteEnv a with
      | some (.ref _ r .siteBorrowMut) => some r | _ => none) as
  -- Show all output targets are tracked
  have hio_tracked : ∀ t ∈ io, t ∈ env.pathEnv.refs := by
    intro r hr; simp only [io, List.mem_filterMap] at hr; obtain ⟨a, _, ha⟩ := hr
    revert ha; cases hlook : lookup env.siteEnv a with
    | none => simp
    | some τ => cases τ with
      | basic _ => simp
      | ref bt' r' bk' => cases bk' with
        | siteBorrowImm => simp only [Option.some.injEq]; intro h; subst h; exact hst a bt' r' _ hlook
        | siteBorrowMut => simp
  have hmo_tracked : ∀ t ∈ mo, t ∈ env.pathEnv.refs := by
    intro r hr; simp only [mo, List.mem_filterMap] at hr; obtain ⟨a, _, ha⟩ := hr
    revert ha; cases hlook : lookup env.siteEnv a with
    | none => simp
    | some τ => cases τ with
      | basic _ => simp
      | ref bt' r' bk' => cases bk' with
        | siteBorrowImm => simp
        | siteBorrowMut => simp only [Option.some.injEq]; intro h; subst h; exact hst a bt' r' _ hlook
  unfold call_connect_inputs_outputs
  dsimp only []
  -- Rule 1: io targets, inputs sources
  have hR1 := outer_foldl_ews_refs_eq io inputs env.pathEnv hio_tracked
  -- Rule 2: mo targets, mi sources
  have hR2 := outer_foldl_ews_refs_eq mo mi _ (fun t ht => by rw [hR1]; exact hmo_tracked t ht)
  -- Rule 3 (conditional): io targets, io sources
  have hR3 := outer_foldl_cond_ews_refs_eq io io _ (fun t ht => by rw [hR2, hR1]; exact hio_tracked t ht)
  exact hR3.trans (hR2.trans hR1)

/-- extend_with_star preserves path inclusion under a substitution σ.
    If interpret(peE.paths(σu, σv), p) → interpret(peL.paths(u,v), p) for all u,v ∈ refsL,
    and both sides apply extend_with_star with σ-related targets/sources,
    then the path inclusion is preserved. -/
private lemma extend_with_star_path_inclusion (σ : Aref → Aref)
    (targetL sourceL : Aref) (peL peE : PathEnv)
    (hincl : ∀ u v, u ∈ peL.refs → v ∈ peL.refs →
      ∀ path, interpret_regex (peE.paths (σ u, σ v)) path →
              interpret_regex (peL.paths (u, v)) path)
    (htgt_mem : targetL ∈ peL.refs) (hsrc_mem : sourceL ∈ peL.refs)
    (hinj : ∀ u v, u ∈ peL.refs → v ∈ peL.refs → σ u = σ v → u = v) :
    ∀ u v, u ∈ (extend_with_star targetL sourceL peL).refs →
           v ∈ (extend_with_star targetL sourceL peL).refs →
      ∀ path, interpret_regex ((extend_with_star (σ targetL) (σ sourceL) peE).paths (σ u, σ v)) path →
              interpret_regex ((extend_with_star targetL sourceL peL).paths (u, v)) path := by
  -- Since target ∈ refs, extend_with_star doesn't add new refs
  have hrefs_eq : (extend_with_star targetL sourceL peL).refs = peL.refs :=
    extend_with_star_refs_eq targetL sourceL peL htgt_mem
  intro u v hu hv path hp
  rw [hrefs_eq] at hu hv
  simp only [extend_with_star] at hp ⊢
  -- Case analysis on u, v vs target
  by_cases huv_tgt : u = targetL ∧ v = targetL
  · -- Both u and v are target: paths are ε on both sides
    rw [if_pos huv_tgt] at ⊢
    rw [if_pos ⟨congrArg σ huv_tgt.1, congrArg σ huv_tgt.2⟩] at hp
    exact hp
  · -- Not both are target
    have hσuv_neg : ¬(σ u = σ targetL ∧ σ v = σ targetL) :=
      fun ⟨h1, h2⟩ => huv_tgt ⟨hinj u targetL hu htgt_mem h1, hinj v targetL hv htgt_mem h2⟩
    rw [if_neg huv_tgt] at ⊢
    rw [if_neg hσuv_neg] at hp
    by_cases hv_tgt : v = targetL
    · -- v = targetL, u ≠ targetL
      have hu_ne : u ≠ targetL := fun h => huv_tgt ⟨h, hv_tgt⟩
      have hσu_ne : σ u ≠ σ targetL := fun h => hu_ne (hinj u targetL hu htgt_mem h)
      have hσv_tgt : σ v = σ targetL := congrArg σ hv_tgt
      rw [if_pos hv_tgt] at ⊢
      rw [if_pos hσv_tgt] at hp
      -- hp : interpret (G_E(σu, σ sourceL) · .*) path
      -- Goal: interpret (G_L(u, sourceL) · .*) path
      simp only [interpret_regex] at hp ⊢
      obtain ⟨p1, p2, rfl, hp1, hp2⟩ := hp
      exact ⟨p1, p2, rfl, hincl u sourceL hu hsrc_mem p1 hp1, hp2⟩
    · -- v ≠ targetL
      have hσv_ne : σ v ≠ σ targetL := fun h => hv_tgt (hinj v targetL hv htgt_mem h)
      rw [if_neg hv_tgt] at ⊢
      rw [if_neg hσv_ne] at hp
      by_cases hu_tgt : u = targetL
      · -- u = targetL, v ≠ targetL
        have hσu_tgt : σ u = σ targetL := congrArg σ hu_tgt
        rw [if_pos hu_tgt] at ⊢
        rw [if_pos hσu_tgt] at hp
        -- hp : interpret (.* · G_E(σ sourceL, σ v)) path
        -- Goal: interpret (.* · G_L(sourceL, v)) path
        simp only [interpret_regex] at hp ⊢
        obtain ⟨p1, p2, rfl, hp1, hp2⟩ := hp
        exact ⟨p1, p2, rfl, hp1, hincl sourceL v hsrc_mem hv p2 hp2⟩
      · -- Neither u nor v is target: use base path
        have hσu_ne : σ u ≠ σ targetL := fun h => hu_tgt (hinj u targetL hu htgt_mem h)
        rw [if_neg hu_tgt] at ⊢
        rw [if_neg hσu_ne] at hp
        exact hincl u v hu hv path hp

-- ============================================================
-- Subsumes through populate_call_outputs
-- ============================================================

/-- Path inclusion is preserved through update_with_epsilon when both sides add a fresh ref.
    The key insight: mixed paths (involving the fresh ref and old refs) have empty antecedent
    on the E side (from hpaths_to/from_nm), so inclusion is vacuously true. -/
private lemma update_with_epsilon_path_inclusion (σ : Aref → Aref)
    (rL rE : Aref) (peL peE : PathEnv)
    (hincl : ∀ u v, u ∈ peL.refs → v ∈ peL.refs →
      ∀ path, interpret_regex (peE.paths (σ u, σ v)) path →
              interpret_regex (peL.paths (u, v)) path)
    (hrL_fresh : rL ∉ peL.refs) (hrE_fresh : rE ∉ peE.refs)
    (_ : ∀ u v, u ∈ peL.refs → v ∈ peL.refs → σ u = σ v → u = v)
    (hrefs_map : peL.refs.map σ = peE.refs)
    (hrE_ne_root : rE ≠ .root)
    (hpaths_to_nm : ∀ u v p, v ∉ peE.refs → v ≠ .root → u ≠ v →
      ¬interpret_regex (peE.paths (u, v)) p)
    (hpaths_from_nm : ∀ u v p, u ∉ peE.refs → u ≠ .root → u ≠ v →
      ¬interpret_regex (peE.paths (u, v)) p) :
    let σ' := extendSubst σ rL rE
    ∀ u v, u ∈ (update_with_epsilon rL rL peL).refs →
           v ∈ (update_with_epsilon rL rL peL).refs →
      ∀ path, interpret_regex ((update_with_epsilon rE rE peE).paths (σ' u, σ' v)) path →
              interpret_regex ((update_with_epsilon rL rL peL).paths (u, v)) path := by
  intro σ'
  -- Characterize refs after update
  have hrefsL : (update_with_epsilon rL rL peL).refs = rL :: peL.refs :=
    uwe_epsilon_refs_fresh rL rL peL hrL_fresh
  have hrefsE : (update_with_epsilon rE rE peE).refs = rE :: peE.refs :=
    uwe_epsilon_refs_fresh rE rE peE hrE_fresh
  -- σ maps old refs to env refs, so σ u ≠ rE for old u
  have hσ_old_ne_rE : ∀ u, u ∈ peL.refs → σ u ≠ rE := by
    intro u hu heq; exact hrE_fresh (heq ▸ hrefs_map ▸ List.mem_map.mpr ⟨u, hu, rfl⟩)
  intro u v hu hv path hp
  rw [hrefsL] at hu hv
  simp only [update_with_epsilon, update_with_extension] at hp ⊢
  -- Simplify extend/der with empty path: extend re [] = re, der re [] = re
  simp only [extend, der, List.foldl_nil] at hp ⊢
  rcases List.mem_cons.mp hu with hu_eq | hu'
  · -- u = rL
    have hσu : σ' u = rE := if_pos hu_eq
    rcases List.mem_cons.mp hv with hv_eq | hv'
    · -- u = rL, v = rL: both sides ε
      have hσv : σ' v = rE := if_pos hv_eq
      rw [hσu, hσv] at hp; rw [hu_eq, hv_eq]
      rw [if_pos ⟨rfl, rfl⟩] at hp; rw [if_pos ⟨rfl, rfl⟩]
      exact hp
    · -- u = rL, v ∈ old: E side has paths(rE, σ v) = G_E(rE, σ v) which is empty
      have hv_ne : v ≠ rL := fun h => hrL_fresh (h ▸ hv')
      have hσv : σ' v = σ v := if_neg hv_ne
      rw [hσu, hσv] at hp
      have hσv_ne_rE : σ v ≠ rE := hσ_old_ne_rE v hv'
      have hnotboth : ¬(rE = rE ∧ σ v = rE) := fun ⟨_, h⟩ => hσv_ne_rE h
      rw [if_neg hnotboth, if_neg hσv_ne_rE, if_pos rfl] at hp
      exact absurd hp (hpaths_from_nm rE (σ v) path hrE_fresh hrE_ne_root hσv_ne_rE.symm)
  · -- u ∈ old
    have hu_ne : u ≠ rL := fun h => hrL_fresh (h ▸ hu')
    have hσu : σ' u = σ u := if_neg hu_ne
    rcases List.mem_cons.mp hv with hv_eq | hv'
    · -- u ∈ old, v = rL: E side has paths(σ u, rE) = G_E(σ u, rE) which is empty
      have hσv : σ' v = rE := if_pos hv_eq
      rw [hσu, hσv] at hp
      have hσu_ne_rE : σ u ≠ rE := hσ_old_ne_rE u hu'
      have hnotboth : ¬(σ u = rE ∧ rE = rE) := fun ⟨h, _⟩ => hσu_ne_rE h
      rw [if_neg hnotboth, if_pos rfl] at hp
      exact absurd hp (hpaths_to_nm (σ u) rE path hrE_fresh hrE_ne_root hσu_ne_rE)
    · -- u ∈ old, v ∈ old: unchanged paths, use original inclusion
      have hv_ne : v ≠ rL := fun h => hrL_fresh (h ▸ hv')
      have hσv : σ' v = σ v := if_neg hv_ne
      rw [hσu, hσv] at hp
      have hσu_ne_rE : σ u ≠ rE := hσ_old_ne_rE u hu'
      have hσv_ne_rE : σ v ≠ rE := hσ_old_ne_rE v hv'
      have hnotbothE : ¬(σ u = rE ∧ σ v = rE) := fun ⟨h, _⟩ => hσu_ne_rE h
      rw [if_neg hnotbothE, if_neg hσv_ne_rE, if_neg hσu_ne_rE] at hp
      have hnotbothL : ¬(u = rL ∧ v = rL) := fun ⟨h, _⟩ => hu_ne h
      rw [if_neg hnotbothL, if_neg hv_ne, if_neg hu_ne]
      exact hincl u v hu' hv' path hp

/-- Subsumes is preserved through populate_call_outputs.
    Given subsumes σ between envL and envE, after populating both with σ-related fresh refs,
    subsumes holds between the results with an extended σ. -/
private lemma populate_call_outputs_subsumes
    (envL envE envL' envE' : TypeEnv) (as : List Site) (rets : List ParamType)
    (outRefsL outRefsE : List Aref) (σ : Aref → Aref)
    (hid : ∀ r, (∀ n, r ≠ .refid n) → σ r = r)
    (hve : VarEnvSubstEquiv σ envL.varEnv envE.varEnv)
    (hse : SiteEnvSubstEquiv σ envL.siteEnv envE.siteEnv)
    (hrefs : envL.pathEnv.refs.map σ = envE.pathEnv.refs)
    (hinj : ∀ u v, u ∈ envL.pathEnv.refs → v ∈ envL.pathEnv.refs → σ u = σ v → u = v)
    (hnonroot : ∀ r, r ≠ .root → σ r ≠ .root)
    (hpaths : ∀ u v, u ∈ envL.pathEnv.refs → v ∈ envL.pathEnv.refs →
      ∀ path, interpret_regex (envE.pathEnv.paths (σ u, σ v)) path →
              interpret_regex (envL.pathEnv.paths (u, v)) path)
    (hfreshL : all_refs_fresh_in_env envL outRefsL)
    (hfreshE : all_refs_fresh_in_env envE outRefsE)
    (hnodupL : List.Nodup outRefsL) (hnodupE : List.Nodup outRefsE)
    (hlen : outRefsL.length = outRefsE.length)
    (hnotRootL : ∀ r ∈ outRefsL, r ≠ .root)
    (hnotRootE : ∀ r ∈ outRefsE, r ≠ .root)
    (hpaths_to_nm : ∀ u v p, v ∉ envE.pathEnv.refs → v ≠ .root → u ≠ v →
      ¬interpret_regex (envE.pathEnv.paths (u, v)) p)
    (hpaths_from_nm : ∀ u v p, u ∉ envE.pathEnv.refs → u ≠ .root → u ≠ v →
      ¬interpret_regex (envE.pathEnv.paths (u, v)) p)
    (hfuneq : envL.funEnv = envE.funEnv)
    (hpopL : populate_call_outputs envL as rets outRefsL = some envL')
    (hpopE : populate_call_outputs envE as rets outRefsE = some envE') :
    TypeEnv.subsumes envL' envE' := by
  induction as generalizing envL envE σ rets outRefsL outRefsE with
  | nil =>
    cases rets with
    | nil =>
      simp only [populate_call_outputs] at hpopL hpopE
      split at hpopL
      · split at hpopE
        · simp only [Option.some.injEq] at hpopL hpopE; subst hpopL; subst hpopE
          exact ⟨σ, hid, hve, hse, hrefs, hinj, hnonroot, hpaths⟩
        · simp at hpopE
      · simp at hpopL
    | cons _ _ => simp [populate_call_outputs] at hpopL
  | cons site as' ih_as =>
    cases rets with
    | nil => simp [populate_call_outputs] at hpopL
    | cons pt rets' =>
      obtain ⟨bt, isRefMut⟩ := pt
      cases isRefMut with
      | none =>
        -- Basic output: insert (.basic bt) into siteEnv, no pathEnv change
        simp only [populate_call_outputs] at hpopL hpopE
        exact ih_as
          {envL with siteEnv := insert envL.siteEnv site (.basic bt)}
          {envE with siteEnv := insert envE.siteEnv site (.basic bt)}
          _ _ _ _ hid hve
          (SiteEnvSubstEquiv_insert σ _ _ site (.basic bt) (.basic bt) hse
            (by simp [applySubstMoveType]))
          hrefs hinj hnonroot hpaths
          (fun r hr =>
            let hb := freshRefInEnvBool_insert_basic r envL site bt
              ((freshRefInEnv_iff_freshRefInEnvBool r envL).mp (hfreshL r hr))
            (freshRefInEnv_iff_freshRefInEnvBool r _).mpr hb)
          (fun r hr =>
            let hb := freshRefInEnvBool_insert_basic r envE site bt
              ((freshRefInEnv_iff_freshRefInEnvBool r envE).mp (hfreshE r hr))
            (freshRefInEnv_iff_freshRefInEnvBool r _).mpr hb)
          hnodupL hnodupE hlen
          hnotRootL hnotRootE hpaths_to_nm hpaths_from_nm hfuneq hpopL hpopE
      | some b =>
        cases b <;> (
          cases outRefsL with
          | nil => simp [populate_call_outputs] at hpopL
          | cons rL outRefsL' =>
            cases outRefsE with
            | nil => simp at hlen
            | cons rE outRefsE' =>
              simp only [populate_call_outputs] at hpopL hpopE
              -- Fresh refs are not in pathEnv.refs
              have hrL_fresh := hfreshL rL (List.mem_cons.mpr (Or.inl rfl))
              have hrL_fresh_pe : rL ∉ envL.pathEnv.refs :=
                freshRefInEnv_implies_freshRef rL envL hrL_fresh
              have hrE_fresh := hfreshE rE (List.mem_cons.mpr (Or.inl rfl))
              have hrE_fresh_pe : rE ∉ envE.pathEnv.refs :=
                freshRefInEnv_implies_freshRef rE envE hrE_fresh
              have hrL_ne_root := hnotRootL rL (List.mem_cons.mpr (Or.inl rfl))
              have hrE_ne_root := hnotRootE rE (List.mem_cons.mpr (Or.inl rfl))
              -- rL is a refid (from freshRefInEnv includes not_varRef + not_root)
              have hrL_not_varRef : ∀ v, rL ≠ .varRef v := (hrL_fresh.2.2 : _ ∧ _).2
              have hrL_refid : ∃ n, rL = .refid n := by
                cases rL with
                | root => exact absurd rfl hrL_ne_root
                | refid n => exact ⟨n, rfl⟩
                | varRef v => exact absurd rfl (hrL_not_varRef v)
              have hrE_not_mapped : rE ∉ envL.pathEnv.refs.map σ := by
                rw [hrefs]; exact hrE_fresh_pe
              -- Extended σ
              let σ' := extendSubst σ rL rE
              exact ih_as
                { envL with siteEnv := insert envL.siteEnv site (.ref bt rL _),
                            pathEnv := update_with_epsilon rL rL envL.pathEnv }
                { envE with siteEnv := insert envE.siteEnv site (.ref bt rE _),
                            pathEnv := update_with_epsilon rE rE envE.pathEnv }
                _ _ _ σ'
                (extendSubst_id σ rL rE hid hrL_refid)
                (VarEnvSubstEquiv_extend σ rL rE _ _ hve
                  (fun x' bt' s' bk' ms' hlook' =>
                    Ne.symm (freshRefInEnv_ne_varEnv_ref rL _ x' .validVar bt' s' bk' ms'
                      hrL_fresh hlook')))
                (SiteEnvSubstEquiv_extend_insert_ref σ rL rE _ _ site bt _
                  hse
                  (fun k bt' ref bk' hlook' =>
                    Ne.symm (freshRefInEnv_ne_siteEnv_ref rL _ k bt' ref bk'
                      hrL_fresh hlook')))
                (by simp only [uwe_epsilon_refs_fresh rL rL envL.pathEnv hrL_fresh_pe,
                        uwe_epsilon_refs_fresh rE rE envE.pathEnv hrE_fresh_pe]
                    simp only [List.map_cons, show σ' rL = rE from if_pos rfl]
                    congr 1
                    exact (map_extendSubst_eq_map_σ σ rL rE _ hrL_fresh_pe).trans hrefs)
                (extendSubst_injective σ rL rE _ hinj hrL_fresh_pe hrE_not_mapped)
                (extendSubst_nonroot σ rL rE hnonroot hrE_ne_root)
                (update_with_epsilon_path_inclusion σ rL rE envL.pathEnv envE.pathEnv
                  hpaths hrL_fresh_pe hrE_fresh_pe hinj hrefs hrE_ne_root
                  hpaths_to_nm hpaths_from_nm)
                (fun r hr =>
                  let hb := freshRefInEnvBool_insert_ref_update_epsilon r rL envL site bt _
                    ((freshRefInEnv_iff_freshRefInEnvBool r envL).mp
                      (hfreshL r (List.mem_cons.mpr (Or.inr hr))))
                    (fun (h : r = rL) => (List.nodup_cons.mp hnodupL).1 (h ▸ hr))
                  (freshRefInEnv_iff_freshRefInEnvBool r _).mpr hb)
                (fun r hr =>
                  let hb := freshRefInEnvBool_insert_ref_update_epsilon r rE envE site bt _
                    ((freshRefInEnv_iff_freshRefInEnvBool r envE).mp
                      (hfreshE r (List.mem_cons.mpr (Or.inr hr))))
                    (fun (h : r = rE) => (List.nodup_cons.mp hnodupE).1 (h ▸ hr))
                  (freshRefInEnv_iff_freshRefInEnvBool r _).mpr hb)
                ((List.nodup_cons.mp hnodupL).2) ((List.nodup_cons.mp hnodupE).2)
                (by simpa using hlen)
                (fun r hr => hnotRootL r (List.mem_cons.mpr (Or.inr hr)))
                (fun r hr => hnotRootE r (List.mem_cons.mpr (Or.inr hr)))
                (update_with_extension_paths_to_non_member rE rE [] envE.pathEnv
                  hpaths_to_nm (Or.inr rfl))
                (update_with_extension_paths_from_non_member rE rE [] envE.pathEnv
                  hpaths_from_nm (Or.inr rfl))
                hfuneq hpopL hpopE)

-- ============================================================
-- Path inclusion through call_connect_inputs_outputs
-- ============================================================

/-- Filter lists from siteEnv are σ-related under SiteEnvSubstEquiv:
    extracting ref arefs from siteEnv via filterMap preserves the σ relationship. -/
private lemma filterMap_ref_map_σ (σ : Aref → Aref)
    (seL seE : SiteEnv) (sites : List Site)
    (hse : SiteEnvSubstEquiv σ seL seE)
    (f : BorrowingKind → Bool) :
    (sites.filterMap (fun a => match lookup seL a with
      | some (.ref _ r bk) => if f bk then some r else none
      | _ => none)).map σ =
    sites.filterMap (fun a => match lookup seE a with
      | some (.ref _ r bk) => if f bk then some r else none
      | _ => none) := by
  induction sites with
  | nil => rfl
  | cons s ss ih =>
    simp only [List.filterMap_cons]
    have hse_s := hse s
    cases hlL : lookup seL s with
    | none =>
      simp only [hlL] at hse_s ⊢
      cases hlE : lookup seE s with
      | none => simp only [hlE] at hse_s ⊢; exact ih
      | some _ => simp only [hlE] at hse_s
    | some τL =>
      simp only [hlL] at hse_s ⊢
      cases hlE : lookup seE s with
      | none => simp only [hlE] at hse_s
      | some τE =>
        simp only [hlE] at hse_s ⊢
        cases τL with
        | basic bt => simp [applySubstMoveType] at hse_s; rw [← hse_s]; simp; exact ih
        | ref bt r bk =>
          simp only [applySubstMoveType] at hse_s
          rw [← hse_s]; simp only
          cases f bk with
          | true => simp only [↓reduceIte, List.map_cons]; exact congrArg _ ih
          | false => exact ih

/-- Inner foldl of extend_with_star preserves path inclusion. -/
private lemma inner_foldl_ews_path_incl (σ : Aref → Aref)
    (target_L : Aref) (sources_L : List Aref) (peL peE : PathEnv)
    (hincl : ∀ u v, u ∈ peL.refs → v ∈ peL.refs →
      ∀ path, interpret_regex (peE.paths (σ u, σ v)) path →
              interpret_regex (peL.paths (u, v)) path)
    (htgt : target_L ∈ peL.refs)
    (hsrc : ∀ s ∈ sources_L, s ∈ peL.refs)
    (hinj : ∀ u v, u ∈ peL.refs → v ∈ peL.refs → σ u = σ v → u = v) :
    let result_L := sources_L.foldl (fun acc s => extend_with_star target_L s acc) peL
    let result_E := (sources_L.map σ).foldl (fun acc s => extend_with_star (σ target_L) s acc) peE
    ∀ u v, u ∈ result_L.refs → v ∈ result_L.refs →
      ∀ path, interpret_regex (result_E.paths (σ u, σ v)) path →
              interpret_regex (result_L.paths (u, v)) path := by
  induction sources_L generalizing peL peE with
  | nil => exact hincl
  | cons s ss ih =>
    simp only [List.map, List.foldl_cons]
    have hs_mem := hsrc s (List.mem_cons.mpr (Or.inl rfl))
    have hrefsL := extend_with_star_refs_eq target_L s peL htgt
    exact ih (extend_with_star target_L s peL) (extend_with_star (σ target_L) (σ s) peE)
      (extend_with_star_path_inclusion σ target_L s peL peE hincl htgt hs_mem hinj)
      (hrefsL ▸ htgt) (fun s' hs' => hrefsL ▸ hsrc s' (List.mem_cons.mpr (Or.inr hs')))
      (fun u v hu hv => hinj u v (hrefsL ▸ hu) (hrefsL ▸ hv))

/-- Outer foldl of extend_with_star preserves path inclusion. -/
private lemma outer_foldl_ews_path_incl (σ : Aref → Aref)
    (targets_L sources_L : List Aref) (peL peE : PathEnv)
    (hincl : ∀ u v, u ∈ peL.refs → v ∈ peL.refs →
      ∀ path, interpret_regex (peE.paths (σ u, σ v)) path →
              interpret_regex (peL.paths (u, v)) path)
    (htgt : ∀ t ∈ targets_L, t ∈ peL.refs)
    (hsrc : ∀ s ∈ sources_L, s ∈ peL.refs)
    (hinj : ∀ u v, u ∈ peL.refs → v ∈ peL.refs → σ u = σ v → u = v) :
    let result_L := targets_L.foldl (fun acc t =>
      sources_L.foldl (fun acc' s => extend_with_star t s acc') acc) peL
    let result_E := (targets_L.map σ).foldl (fun acc t =>
      (sources_L.map σ).foldl (fun acc' s => extend_with_star t s acc') acc) peE
    ∀ u v, u ∈ result_L.refs → v ∈ result_L.refs →
      ∀ path, interpret_regex (result_E.paths (σ u, σ v)) path →
              interpret_regex (result_L.paths (u, v)) path := by
  induction targets_L generalizing peL peE with
  | nil => exact hincl
  | cons t ts ih =>
    simp only [List.map, List.foldl_cons]
    have ht_mem := htgt t (List.mem_cons.mpr (Or.inl rfl))
    have hrefsL := inner_foldl_ews_refs_eq t sources_L peL ht_mem
    exact ih
      (sources_L.foldl (fun acc' s => extend_with_star t s acc') peL)
      ((sources_L.map σ).foldl (fun acc' s => extend_with_star (σ t) s acc') peE)
      (inner_foldl_ews_path_incl σ t sources_L peL peE hincl ht_mem hsrc hinj)
      (fun t' ht' => hrefsL ▸ htgt t' (List.mem_cons.mpr (Or.inr ht')))
      (fun s' hs' => hrefsL ▸ hsrc s' hs')
      (fun u v hu hv => hinj u v (hrefsL ▸ hu) (hrefsL ▸ hv))

/-- Inner conditional foldl of extend_with_star preserves path inclusion. -/
private lemma inner_foldl_cond_ews_path_incl (σ : Aref → Aref)
    (target_L : Aref) (sources_L : List Aref) (peL peE : PathEnv)
    (hincl : ∀ u v, u ∈ peL.refs → v ∈ peL.refs →
      ∀ path, interpret_regex (peE.paths (σ u, σ v)) path →
              interpret_regex (peL.paths (u, v)) path)
    (htgt : target_L ∈ peL.refs)
    (hsrc : ∀ s ∈ sources_L, s ∈ peL.refs)
    (hinj : ∀ u v, u ∈ peL.refs → v ∈ peL.refs → σ u = σ v → u = v) :
    let result_L := sources_L.foldl (fun acc s =>
      if target_L ≠ s then extend_with_star target_L s acc else acc) peL
    let result_E := (sources_L.map σ).foldl (fun acc s =>
      if σ target_L ≠ s then extend_with_star (σ target_L) s acc else acc) peE
    ∀ u v, u ∈ result_L.refs → v ∈ result_L.refs →
      ∀ path, interpret_regex (result_E.paths (σ u, σ v)) path →
              interpret_regex (result_L.paths (u, v)) path := by
  induction sources_L generalizing peL peE with
  | nil => exact hincl
  | cons s ss ih =>
    simp only [List.map, List.foldl_cons]
    have hs_mem := hsrc s (List.mem_cons.mpr (Or.inl rfl))
    by_cases hne : target_L ≠ s
    · -- Condition true on both sides (injectivity)
      have hne_E : σ target_L ≠ σ s := fun h => hne (hinj _ _ htgt hs_mem h)
      rw [if_pos hne, if_pos hne_E]
      have hrefsL := extend_with_star_refs_eq target_L s peL htgt
      exact ih (extend_with_star target_L s peL) (extend_with_star (σ target_L) (σ s) peE)
        (extend_with_star_path_inclusion σ target_L s peL peE hincl htgt hs_mem hinj)
        (hrefsL ▸ htgt) (fun s' hs' => hrefsL ▸ hsrc s' (List.mem_cons.mpr (Or.inr hs')))
        (fun u v hu hv => hinj u v (hrefsL ▸ hu) (hrefsL ▸ hv))
    · -- Condition false on both sides
      simp only [ne_eq, Decidable.not_not] at hne; subst hne
      rw [if_neg (not_not.mpr rfl), if_neg (not_not.mpr rfl)]
      exact ih peL peE hincl htgt (fun s' hs' => hsrc s' (List.mem_cons.mpr (Or.inr hs'))) hinj

/-- Outer conditional foldl of extend_with_star preserves path inclusion. -/
private lemma outer_foldl_cond_ews_path_incl (σ : Aref → Aref)
    (targets_L sources_L : List Aref) (peL peE : PathEnv)
    (hincl : ∀ u v, u ∈ peL.refs → v ∈ peL.refs →
      ∀ path, interpret_regex (peE.paths (σ u, σ v)) path →
              interpret_regex (peL.paths (u, v)) path)
    (htgt : ∀ t ∈ targets_L, t ∈ peL.refs)
    (hsrc : ∀ s ∈ sources_L, s ∈ peL.refs)
    (hinj : ∀ u v, u ∈ peL.refs → v ∈ peL.refs → σ u = σ v → u = v) :
    let result_L := targets_L.foldl (fun acc t =>
      sources_L.foldl (fun acc' s =>
        if t ≠ s then extend_with_star t s acc' else acc') acc) peL
    let result_E := (targets_L.map σ).foldl (fun acc t =>
      (sources_L.map σ).foldl (fun acc' s =>
        if t ≠ s then extend_with_star t s acc' else acc') acc) peE
    ∀ u v, u ∈ result_L.refs → v ∈ result_L.refs →
      ∀ path, interpret_regex (result_E.paths (σ u, σ v)) path →
              interpret_regex (result_L.paths (u, v)) path := by
  induction targets_L generalizing peL peE with
  | nil => exact hincl
  | cons t ts ih =>
    simp only [List.map, List.foldl_cons]
    have ht_mem := htgt t (List.mem_cons.mpr (Or.inl rfl))
    have hrefsL := inner_foldl_cond_ews_refs_eq t sources_L peL ht_mem
    exact ih
      (sources_L.foldl (fun acc' s =>
        if t ≠ s then extend_with_star t s acc' else acc') peL)
      ((sources_L.map σ).foldl (fun acc' s =>
        if σ t ≠ s then extend_with_star (σ t) s acc' else acc') peE)
      (inner_foldl_cond_ews_path_incl σ t sources_L peL peE hincl ht_mem hsrc hinj)
      (fun t' ht' => hrefsL ▸ htgt t' (List.mem_cons.mpr (Or.inr ht')))
      (fun s' hs' => hrefsL ▸ hsrc s' hs')
      (fun u v hu hv => hinj u v (hrefsL ▸ hu) (hrefsL ▸ hv))

/-- filterMap for immutable refs preserves σ-relationship across SiteEnvSubstEquiv. -/
private lemma filterMap_immRef_map_σ (σ : Aref → Aref)
    (seL seE : SiteEnv) (sites : List Site)
    (hse : SiteEnvSubstEquiv σ seL seE) :
    (sites.filterMap (fun a => match lookup seL a with
      | some (.ref _ r .siteBorrowImm) => some r | _ => none)).map σ =
    sites.filterMap (fun a => match lookup seE a with
      | some (.ref _ r .siteBorrowImm) => some r | _ => none) := by
  induction sites with
  | nil => rfl
  | cons s ss ih =>
    simp only [List.filterMap_cons]
    have hse_s := hse s
    cases hlL : lookup seL s with
    | none =>
      simp only [hlL] at hse_s ⊢
      cases hlE : lookup seE s with
      | none => simp only [hlE] at hse_s ⊢; exact ih
      | some _ => simp only [hlE] at hse_s
    | some τL =>
      simp only [hlL] at hse_s ⊢
      cases hlE : lookup seE s with
      | none => simp only [hlE] at hse_s
      | some τE =>
        simp only [hlE] at hse_s ⊢
        cases τL with
        | basic bt => simp [applySubstMoveType] at hse_s; rw [← hse_s]; simp; exact ih
        | ref bt r bk =>
          simp only [applySubstMoveType] at hse_s; rw [← hse_s]
          cases bk with
          | siteBorrowImm => simp only [List.map_cons]; exact congrArg _ ih
          | siteBorrowMut => exact ih

/-- filterMap for mutable refs preserves σ-relationship across SiteEnvSubstEquiv. -/
private lemma filterMap_mutRef_map_σ (σ : Aref → Aref)
    (seL seE : SiteEnv) (sites : List Site)
    (hse : SiteEnvSubstEquiv σ seL seE) :
    (sites.filterMap (fun a => match lookup seL a with
      | some (.ref _ r .siteBorrowMut) => some r | _ => none)).map σ =
    sites.filterMap (fun a => match lookup seE a with
      | some (.ref _ r .siteBorrowMut) => some r | _ => none) := by
  induction sites with
  | nil => rfl
  | cons s ss ih =>
    simp only [List.filterMap_cons]
    have hse_s := hse s
    cases hlL : lookup seL s with
    | none =>
      simp only [hlL] at hse_s ⊢
      cases hlE : lookup seE s with
      | none => simp only [hlE] at hse_s ⊢; exact ih
      | some _ => simp only [hlE] at hse_s
    | some τL =>
      simp only [hlL] at hse_s ⊢
      cases hlE : lookup seE s with
      | none => simp only [hlE] at hse_s
      | some τE =>
        simp only [hlE] at hse_s ⊢
        cases τL with
        | basic bt => simp [applySubstMoveType] at hse_s; rw [← hse_s]; simp; exact ih
        | ref bt r bk =>
          simp only [applySubstMoveType] at hse_s; rw [← hse_s]
          cases bk with
          | siteBorrowImm => exact ih
          | siteBorrowMut => simp only [List.map_cons]; exact congrArg _ ih

/-- filterMap for all refs preserves σ-relationship across SiteEnvSubstEquiv. -/
private lemma filterMap_allRef_map_σ (σ : Aref → Aref)
    (seL seE : SiteEnv) (sites : List Site)
    (hse : SiteEnvSubstEquiv σ seL seE) :
    (sites.filterMap (fun a => match lookup seL a with
      | some (.ref _ r _) => some r | _ => none)).map σ =
    sites.filterMap (fun a => match lookup seE a with
      | some (.ref _ r _) => some r | _ => none) := by
  induction sites with
  | nil => rfl
  | cons s ss ih =>
    simp only [List.filterMap_cons]
    have hse_s := hse s
    cases hlL : lookup seL s with
    | none =>
      simp only [hlL] at hse_s ⊢
      cases hlE : lookup seE s with
      | none => simp only [hlE] at hse_s ⊢; exact ih
      | some _ => simp only [hlE] at hse_s
    | some τL =>
      simp only [hlL] at hse_s ⊢
      cases hlE : lookup seE s with
      | none => simp only [hlE] at hse_s
      | some τE =>
        simp only [hlE] at hse_s ⊢
        cases τL with
        | basic bt => simp [applySubstMoveType] at hse_s; rw [← hse_s]; simp; exact ih
        | ref bt r bk =>
          simp only [applySubstMoveType] at hse_s; rw [← hse_s]
          cases bk <;> (simp only [List.map_cons]; exact congrArg _ ih)

/-- Triple foldl of extend_with_star preserves path inclusion.
    Takes filter lists as parameters with σ-mapping equalities, then uses subst
    to convert E-side lists to .map σ form and composes the three foldl lemmas.
    This avoids match-compilation mismatch issues between different definitions. -/
private lemma path_inclusion_via_triple_foldl
    (σ : Aref → Aref) (peL peE : PathEnv)
    (io_L inputs_L mo_L mi_L io_E inputs_E mo_E mi_E : List Aref)
    (hio_map : io_L.map σ = io_E)
    (hinputs_map : inputs_L.map σ = inputs_E)
    (hmo_map : mo_L.map σ = mo_E)
    (hmi_map : mi_L.map σ = mi_E)
    (hio_tracked : ∀ r ∈ io_L, r ∈ peL.refs)
    (hinputs_tracked : ∀ r ∈ inputs_L, r ∈ peL.refs)
    (hmo_tracked : ∀ r ∈ mo_L, r ∈ peL.refs)
    (hmi_tracked : ∀ r ∈ mi_L, r ∈ peL.refs)
    (hpaths : ∀ u v, u ∈ peL.refs → v ∈ peL.refs →
      ∀ path, interpret_regex (peE.paths (σ u, σ v)) path →
              interpret_regex (peL.paths (u, v)) path)
    (hinj : ∀ u v, u ∈ peL.refs → v ∈ peL.refs → σ u = σ v → u = v)
    (u v : Aref) (hu : u ∈ peL.refs) (hv : v ∈ peL.refs) :
    ∀ path,
    interpret_regex ((io_E.foldl (fun acc io1 =>
      io_E.foldl (fun acc' io2 =>
        if io1 ≠ io2 then extend_with_star io1 io2 acc' else acc') acc)
      (mo_E.foldl (fun acc mout =>
        mi_E.foldl (fun acc' minput => extend_with_star mout minput acc') acc)
        (io_E.foldl (fun acc iout =>
          inputs_E.foldl (fun acc' input => extend_with_star iout input acc') acc) peE))).paths (σ u, σ v)) path →
    interpret_regex ((io_L.foldl (fun acc io1 =>
      io_L.foldl (fun acc' io2 =>
        if io1 ≠ io2 then extend_with_star io1 io2 acc' else acc') acc)
      (mo_L.foldl (fun acc mout =>
        mi_L.foldl (fun acc' minput => extend_with_star mout minput acc') acc)
        (io_L.foldl (fun acc iout =>
          inputs_L.foldl (fun acc' input => extend_with_star iout input acc') acc) peL))).paths (u, v)) path := by
  subst hio_map hinputs_map hmo_map hmi_map
  -- Rule 1: io over inputs
  have hR1_refs := outer_foldl_ews_refs_eq io_L inputs_L peL hio_tracked
  have hR1 := outer_foldl_ews_path_incl σ io_L inputs_L peL peE
    hpaths hio_tracked hinputs_tracked hinj
  -- Rule 2: mo over mi
  have hR2_refs := outer_foldl_ews_refs_eq mo_L mi_L _
    (fun t ht => hR1_refs ▸ hmo_tracked t ht)
  have hR2 := outer_foldl_ews_path_incl σ mo_L mi_L _ _ hR1
    (fun t ht => hR1_refs ▸ hmo_tracked t ht)
    (fun s hs => hR1_refs ▸ hmi_tracked s hs)
    (fun u v hu hv => hinj u v (hR1_refs ▸ hu) (hR1_refs ▸ hv))
  -- Rule 3: io conditional over io
  have hR3 := outer_foldl_cond_ews_path_incl σ io_L io_L _ _ hR2
    (fun t ht => hR2_refs ▸ hR1_refs ▸ hio_tracked t ht)
    (fun s hs => hR2_refs ▸ hR1_refs ▸ hio_tracked s hs)
    (fun u v hu hv => hinj u v ((hR2_refs.trans hR1_refs) ▸ hu) ((hR2_refs.trans hR1_refs) ▸ hv))
  have hR12_refs := hR2_refs.trans hR1_refs
  have hR3_refs := outer_foldl_cond_ews_refs_eq io_L io_L _
    (fun t ht => hR2_refs ▸ hR1_refs ▸ hio_tracked t ht)
  exact hR3 u v
    (by rw [hR3_refs, hR2_refs, hR1_refs]; exact hu)
    (by rw [hR3_refs, hR2_refs, hR1_refs]; exact hv)

/-- call_connect_inputs_outputs preserves subsumes.
    Since call_connect only changes pathEnv, conditions 1-6 carry over from the input subsumes.
    Condition 7 (path inclusion) follows from composing extend_with_star_path_inclusion
    through the triple foldl, using the fact that filter lists are σ-related. -/
private lemma call_connect_subsumes
    (envL envE : TypeEnv) (as bs : List Site)
    (hsub : TypeEnv.subsumes envL envE)
    (hstL : ∀ s bt r bk, lookup envL.siteEnv s = some (.ref bt r bk) → r ∈ envL.pathEnv.refs)
    (hstE : ∀ s bt r bk, lookup envE.siteEnv s = some (.ref bt r bk) → r ∈ envE.pathEnv.refs) :
    TypeEnv.subsumes (call_connect_inputs_outputs envL as bs)
                     (call_connect_inputs_outputs envE as bs) := by
  obtain ⟨σ, hid, hve, hse, hrefs, hinj, hnonroot, hpaths⟩ := hsub
  -- call_connect preserves varEnv, siteEnv
  refine ⟨σ, hid, ?_, ?_, ?_, ?_, hnonroot, ?_⟩
  · rw [call_connect_varEnv, call_connect_varEnv]; exact hve
  · rw [call_connect_siteEnv, call_connect_siteEnv]; exact hse
  · rw [call_connect_refs_eq envL as bs hstL, call_connect_refs_eq envE as bs hstE]; exact hrefs
  · intro u v hu hv
    rw [call_connect_refs_eq envL as bs hstL] at hu hv
    exact hinj u v hu hv
  · -- Path inclusion through the triple foldl
    intro u v hu hv
    rw [call_connect_refs_eq envL as bs hstL] at hu hv
    simp only [call_connect_inputs_outputs]
    -- Apply path_inclusion_via_triple_foldl; exact uses definitional equality
    -- to bridge between match compilations in the lemma vs the unfolded definition
    exact path_inclusion_via_triple_foldl σ envL.pathEnv envE.pathEnv
      _ _ _ _ _ _ _ _
      (filterMap_immRef_map_σ σ envL.siteEnv envE.siteEnv as hse)
      (filterMap_allRef_map_σ σ envL.siteEnv envE.siteEnv bs hse)
      (filterMap_mutRef_map_σ σ envL.siteEnv envE.siteEnv as hse)
      (filterMap_mutRef_map_σ σ envL.siteEnv envE.siteEnv bs hse)
      (by -- io_tracked (immutable outputs)
          intro r hr; simp only [List.mem_filterMap] at hr; obtain ⟨a, _, ha⟩ := hr
          revert ha; cases hlook : lookup envL.siteEnv a with
          | none => simp
          | some τ => cases τ with
            | basic _ => simp
            | ref bt rr bk => cases bk with
              | siteBorrowImm => simp only [Option.some.injEq]; intro h; subst h; exact hstL _ _ _ _ hlook
              | siteBorrowMut => simp)
      (by -- inputs_tracked (all refs)
          intro r hr; simp only [List.mem_filterMap] at hr; obtain ⟨a, _, ha⟩ := hr
          revert ha; cases hlook : lookup envL.siteEnv a with
          | none => simp
          | some τ => cases τ with
            | basic _ => simp
            | ref bt rr bk => simp only [Option.some.injEq]; intro h; subst h; exact hstL _ _ _ _ hlook)
      (by -- mo_tracked (mutable outputs)
          intro r hr; simp only [List.mem_filterMap] at hr; obtain ⟨a, _, ha⟩ := hr
          revert ha; cases hlook : lookup envL.siteEnv a with
          | none => simp
          | some τ => cases τ with
            | basic _ => simp
            | ref bt rr bk => cases bk with
              | siteBorrowImm => simp
              | siteBorrowMut => simp only [Option.some.injEq]; intro h; subst h; exact hstL _ _ _ _ hlook)
      (by -- mi_tracked (mutable inputs)
          intro r hr; simp only [List.mem_filterMap] at hr; obtain ⟨a, _, ha⟩ := hr
          revert ha; cases hlook : lookup envL.siteEnv a with
          | none => simp
          | some τ => cases τ with
            | basic _ => simp
            | ref bt rr bk => cases bk with
              | siteBorrowImm => simp
              | siteBorrowMut => simp only [Option.some.injEq]; intro h; subst h; exact hstL _ _ _ _ hlook)
      hpaths hinj u v hu hv

private theorem weaken_call
    (lenv : LabelEnv) (envL env : TypeEnv)
    (fnName : Id) (as bs : List Site) (params rets : List ParamType)
    (outRefsL : List Aref) (envL' : TypeEnv)
    (cont : Stmt) (retTypes : List ParamType)
    (hfunL : lookup envL.funEnv fnName = some ⟨params, rets⟩)
    (htcL : types_conform envL.siteEnv bs params)
    (hfreshSitesL : all_fresh_sites envL as)
    (hfreshRefsL : all_refs_fresh_in_env envL outRefsL)
    (hnodupL : List.Nodup outRefsL)
    (hpopL : populate_call_outputs envL as rets outRefsL = some envL')
    (hisoL : check_mutable_inputs_isolated envL bs)
    (hsub : TypeEnv.subsumes envL env)
    (hfuneq : envL.funEnv = env.funEnv)
    (hwfL : TypeEnv.WellFormed envL) (hwfE : TypeEnv.WellFormed env)
    (hsite_tracked : ∀ s bt r bk, lookup envL.siteEnv s = some (.ref bt r bk) → r ∈ envL.pathEnv.refs)
    (hvar_tracked : ∀ x bt r bk ms, lookup envL.varEnv x = some (.validVar, .ref bt r bk, ms) → r ∈ envL.pathEnv.refs)
    (huniq : RefsUnique envL.varEnv envL.siteEnv)
    (hpaths_to_nm : ∀ u v p, v ∉ env.pathEnv.refs → v ≠ .root → u ≠ v →
      ¬interpret_regex (env.pathEnv.paths (u, v)) p)
    (hpaths_from_nm : ∀ u v p, u ∉ env.pathEnv.refs → u ≠ .root → u ≠ v →
      ¬interpret_regex (env.pathEnv.paths (u, v)) p)
    (hself_loop_only_empty : ∀ u p, interpret_regex (env.pathEnv.paths (u, u)) p → p = [])
    (hroot : Aref.root ∈ envL.pathEnv.refs)
    (ih : WeakenIH lenv (call_connect_inputs_outputs envL' as bs) cont retTypes) :
    typecheck_stmt lenv env (.call as fnName bs cont) retTypes := by
  obtain ⟨σ, hid, hve, hse, hrefs, hinj, hnonroot, hpaths_incl⟩ := hsub
  -- Transfer preconditions to env
  have hfunE : lookup env.funEnv fnName = some ⟨params, rets⟩ := hfuneq ▸ hfunL
  have htcE := types_conform_SiteEnvSubstEquiv σ envL.siteEnv env.siteEnv bs params hse htcL
  have hfreshSitesE := all_fresh_sites_subsumes σ envL env as hse hfreshSitesL
  have hisoE := check_mutable_inputs_isolated_subsumes σ envL env bs hse hpaths_incl hsite_tracked hisoL
  -- Generate fresh refs for env
  let outRefsE := makeFreshRefs env outRefsL.length
  have hlenE : outRefsE.length = outRefsL.length := makeFreshRefs_length env outRefsL.length
  have hfreshRefsE : all_refs_fresh_in_env env outRefsE := makeFreshRefs_fresh env outRefsL.length
  have hnodupE : List.Nodup outRefsE := makeFreshRefs_nodup env outRefsL.length
  -- Show populate succeeds for env
  obtain ⟨envE', hpopE⟩ := populate_call_outputs_exists' env envL as rets outRefsE outRefsL envL' hpopL hlenE
  -- Derive not_root for outRefsL from freshness
  have hout_not_root_L : ∀ r ∈ outRefsL, r ≠ Aref.root := fun r hr => by
    have hfr := freshRefInEnv_implies_freshRef r envL (hfreshRefsL r hr)
    exact fun heq => hfr (heq ▸ hroot)
  -- WF for intermediate environments
  have hwfL' : TypeEnv.WellFormed envL' :=
    populate_call_outputs_wf envL envL' as rets outRefsL hwfL hout_not_root_L hpopL
  have hwfE' : TypeEnv.WellFormed envE' :=
    populate_call_outputs_wf env envE' as rets outRefsE hwfE
      (makeFreshRefs_not_root env outRefsL.length) hpopE
  -- WF for final environments (after call_connect)
  have hwfL_cc := call_connect_inputs_outputs_wf envL' as bs hwfL'
  have hwfE_cc := call_connect_inputs_outputs_wf envE' as bs hwfE'
  -- Derive intermediate properties for envL' and envE'
  have hst_L' := populate_call_outputs_site_tracked envL envL' as rets outRefsL hsite_tracked hpopL
  have hvt_L' := populate_call_outputs_var_tracked envL envL' as rets outRefsL hvar_tracked hpopL
  have huniq_L' := populate_call_outputs_RefsUnique envL envL' as rets outRefsL huniq hfreshRefsL hnodupL hpopL
  -- site_tracked for env (derived from subsumes + site_tracked for envL)
  have hst_E : ∀ s bt r bk, lookup env.siteEnv s = some (.ref bt r bk) → r ∈ env.pathEnv.refs := by
    intro s bt r bk hlook
    obtain ⟨τ1, hlook1, hsubst1⟩ := SiteEnvSubstEquiv_lookup_some_inv σ _ _ _ _ hse hlook
    cases τ1 with
    | basic _ => simp [applySubstMoveType] at hsubst1
    | ref bt' r' bk' =>
      simp only [applySubstMoveType, MoveType.ref.injEq] at hsubst1
      obtain ⟨_, rfl, _⟩ := hsubst1
      rw [← hrefs]
      exact List.mem_map.mpr ⟨r', hsite_tracked s bt' r' bk' hlook1, rfl⟩
  have hst_E' := populate_call_outputs_site_tracked env envE' as rets outRefsE hst_E hpopE
  have hsl_E' := populate_call_outputs_self_loop_only_empty env envE' as rets outRefsE
      hself_loop_only_empty hpopE
  have hto_E' := populate_call_outputs_paths_to_nm env envE' as rets outRefsE hpaths_to_nm hpopE
  have hfrom_E' := populate_call_outputs_paths_from_nm env envE' as rets outRefsE hpaths_from_nm hpopE
  -- Apply call rule
  exact typecheck_stmt.call lenv env fnName as bs params rets outRefsE envE' cont retTypes
    hfunE htcE hfreshSitesE hfreshRefsE hnodupE hpopE hisoE
    (ih (call_connect_inputs_outputs envE' as bs)
      (call_connect_subsumes envL' envE' as bs
        (populate_call_outputs_subsumes envL env envL' envE' as rets outRefsL outRefsE σ
          hid hve hse hrefs hinj hnonroot hpaths_incl
          hfreshRefsL hfreshRefsE hnodupL hnodupE hlenE.symm
          hout_not_root_L (makeFreshRefs_not_root env outRefsL.length)
          hpaths_to_nm hpaths_from_nm hfuneq hpopL hpopE)
        hst_L' hst_E')
      (by rw [call_connect_funEnv, populate_call_outputs_funEnv _ _ _ _ _ hpopL, hfuneq,
              ← populate_call_outputs_funEnv _ _ _ _ _ hpopE, ← call_connect_funEnv])
      hwfL_cc
      hwfE_cc
      -- site_tracked for call_connect envL' as bs
      (by intro s bt' r' bk' hlook
          rw [call_connect_siteEnv] at hlook
          exact call_connect_refs_mono envL' as bs r' (hst_L' s bt' r' bk' hlook))
      -- var_tracked for call_connect envL' as bs
      (by intro x bt' r' bk' ms hlook
          rw [call_connect_varEnv] at hlook
          exact call_connect_refs_mono envL' as bs r' (hvt_L' x bt' r' bk' ms hlook))
      -- RefsUnique for call_connect envL' as bs
      (by rw [call_connect_varEnv, call_connect_siteEnv]; exact huniq_L')
      -- paths_to_nm for call_connect envE' as bs
      (call_connect_paths_to_nm envE' as bs hto_E' hst_E')
      -- paths_from_nm for call_connect envE' as bs
      (call_connect_paths_from_nm envE' as bs hfrom_E' hst_E')
      -- self_loop_only_empty for call_connect envE' as bs
      (call_connect_self_loop_only_empty envE' as bs hsl_E')
      hwfL_cc.pathEnv_wf.root_in_refs
    )

/-- Weakening: if a statement type-checks under envL, and envL.subsumes env,
    then it also type-checks under env.
    Requires both environments to be well-formed and refs tracked (always holds in practice). -/
theorem typecheck_stmt_weaken (lenv : LabelEnv) (envL env : TypeEnv) (s : Stmt) (retTypes : List ParamType)
    (htyped : typecheck_stmt lenv envL s retTypes)
    (hsub : TypeEnv.subsumes envL env)
    (hfuneq : envL.funEnv = env.funEnv)
    (hwfL : TypeEnv.WellFormed envL)
    (hwfE : TypeEnv.WellFormed env)
    (hsite_tracked : ∀ s bt r bk, lookup envL.siteEnv s = some (.ref bt r bk) → r ∈ envL.pathEnv.refs)
    (hvar_tracked : ∀ x bt r bk ms, lookup envL.varEnv x = some (.validVar, .ref bt r bk, ms) → r ∈ envL.pathEnv.refs)
    (huniq : RefsUnique envL.varEnv envL.siteEnv)
    (hpaths_to_nm : ∀ u v p, v ∉ env.pathEnv.refs → v ≠ .root → u ≠ v →
      ¬interpret_regex (env.pathEnv.paths (u, v)) p)
    (hpaths_from_nm : ∀ u v p, u ∉ env.pathEnv.refs → u ≠ .root → u ≠ v →
      ¬interpret_regex (env.pathEnv.paths (u, v)) p)
    (hself_loop_only_empty : ∀ u p, interpret_regex (env.pathEnv.paths (u, u)) p → p = []) :
    typecheck_stmt lenv env s retTypes := by
  have hroot : Aref.root ∈ envL.pathEnv.refs := hwfL.pathEnv_wf.root_in_refs
  induction htyped generalizing env with
  -- ==================== Terminal cases ====================
  | skip => exact typecheck_stmt.skip ..
  | jump _ _ _ _ hlookup_j hsubJ =>
    exact typecheck_stmt.jump lenv env _ _ _ hlookup_j
      (TypeEnv.subsumes_trans _ _ _ hsubJ hsub)
  | branch envL' a _ _ _ _ _ hsite hl1 hl2 hs1 hs2 =>
    obtain ⟨σ, hid, hve, hse, hrefs, hinj, hnonroot, hpaths⟩ := hsub
    have hsite_env : lookup env.siteEnv a = some (.basic .tbool) := by
      have := SiteEnvSubstEquiv_lookup_some σ _ _ _ _ hse hsite
      simp only [applySubstMoveType] at this; exact this
    have hdel_sub : TypeEnv.subsumes
        {envL' with siteEnv := delete envL'.siteEnv a}
        {env with siteEnv := delete env.siteEnv a} :=
      ⟨σ, hid, hve, SiteEnvSubstEquiv_delete σ _ _ a hse, hrefs, hinj, hnonroot, hpaths⟩
    exact typecheck_stmt.branch lenv env _ _ _ _ _ _ hsite_env hl1 hl2
      (TypeEnv.subsumes_trans _ _ _ hs1 hdel_sub)
      (TypeEnv.subsumes_trans _ _ _ hs2 hdel_sub)
  | ret _ _ _ hconf _ _ _ =>
    obtain ⟨σ, _, _, hse, _, _, _, _⟩ := hsub
    exact typecheck_stmt.ret lenv env _ _
      (types_conform_SiteEnvSubstEquiv σ _ _ _ _ hse hconf)
      (by sorry) -- no local borrowing: anti-monotone in paths
      (by sorry) -- writability: anti-monotone in paths
      (by sorry) -- no aliasing: anti-monotone in paths
  | abort _ _ _ _ hlook =>
    obtain ⟨σ, _, _, hse, _, _, _⟩ := hsub
    exact typecheck_stmt.abort lenv env _ _ _
      (SiteEnvSubstEquiv_lookup_some σ _ _ _ _ hse hlook)
  -- ==================== Non-terminal, no pathEnv change ====================
  | let_bind_intLit _ _ _ _ _ hnotIn _ ih =>
    exact weaken_let_bind_intLit lenv _ env _ _ _ _ hnotIn
      hsub hfuneq hwfL hwfE hsite_tracked hvar_tracked huniq
      hpaths_to_nm hpaths_from_nm hself_loop_only_empty hroot ih
  | let_bind_copy_val _ _ _ _ _ _ _ hlookup hnotIn _ ih =>
    exact weaken_let_bind_copy_val lenv _ env _ _ _ _ _ _ hlookup hnotIn
      hsub hfuneq hwfL hwfE hsite_tracked hvar_tracked huniq
      hpaths_to_nm hpaths_from_nm hself_loop_only_empty hroot ih
  | let_bind_move _ _ _ _ _ _ _ hlookup hnb hnotIn _ ih =>
    exact weaken_let_bind_move lenv _ env _ _ _ _ _ _ hlookup hnb hnotIn
      hsub hfuneq hwfL hwfE hsite_tracked hvar_tracked huniq
      hpaths_to_nm hpaths_from_nm hself_loop_only_empty hroot ih
  | let_bind_binop _ _ _ _ _ sa sb sc _ _ hlook_a hlook_b hbinop hnotIn _ ih =>
    exact weaken_let_bind_binop lenv _ env _ _ _ _ sa sb sc _ _
      hlook_a hlook_b hbinop hnotIn
      hsub hfuneq hwfL hwfE hsite_tracked hvar_tracked huniq
      hpaths_to_nm hpaths_from_nm hself_loop_only_empty hroot ih
  | var_assign_invalid _ _ _ _ _ _ _ hlook_x hlook_a hcompat _ ih =>
    exact weaken_var_assign_invalid lenv _ env _ _ _ _ _ _
      hlook_x hlook_a hcompat
      hsub hfuneq hwfL hwfE hsite_tracked hvar_tracked huniq
      hpaths_to_nm hpaths_from_nm hself_loop_only_empty hroot ih
  -- ==================== Cases with pathEnv changes =============================
  | let_bind_readRef _ a c r _ _ _ _ hlook_a hnotIn _ ih =>
    exact weaken_let_bind_readRef lenv _ env a c r _ _ _ _ hlook_a hnotIn
      hsub hfuneq hwfL hwfE hsite_tracked hvar_tracked huniq
      hpaths_to_nm hpaths_from_nm hself_loop_only_empty hroot ih
  | write_ref _ a b τ r _ _ hlook_a hlook_b houtbound _ ih =>
    exact weaken_write_ref lenv _ env a b τ r _ _ hlook_a hlook_b houtbound
      hsub hfuneq hwfL hwfE hsite_tracked hvar_tracked huniq
      hpaths_to_nm hpaths_from_nm hself_loop_only_empty hroot ih
  | release _ a _ r _ _ _ hlook_a _ ih =>
    exact weaken_release lenv _ env a _ r _ _ _ hlook_a
      hsub hfuneq hwfL hwfE hsite_tracked hvar_tracked huniq
      hpaths_to_nm hpaths_from_nm hself_loop_only_empty hroot ih
  | let_bind_copy_ref envL a _ _ _ s t _ _ _ hlookup hnotIn hfresh _ ih =>
    exact weaken_let_bind_copy_ref lenv envL env a _ _ _ s t _ _ _ hlookup hnotIn hfresh
      hsub hfuneq hwfL hwfE hsite_tracked hvar_tracked huniq
      hpaths_to_nm hpaths_from_nm hself_loop_only_empty hroot ih
  | let_bind_borrowImm envL a x_var τ ms r cont retTypes hlookup hnotIn hfresh _ ih =>
    exact weaken_let_bind_borrowImm lenv envL env a x_var τ ms r _ _
      hlookup hnotIn hfresh
      hsub hfuneq hwfL hwfE hsite_tracked hvar_tracked huniq
      hpaths_to_nm hpaths_from_nm hself_loop_only_empty hroot ih
  | let_bind_borrowMut envL a x_var _ _ r _ _ hle hlookup hnotIn hfresh _ ih =>
    exact weaken_let_bind_borrowMut lenv envL env a x_var _ _ r _ _
      hle hlookup hnotIn hfresh
      hsub hfuneq hwfL hwfE hsite_tracked hvar_tracked huniq
      hpaths_to_nm hpaths_from_nm hself_loop_only_empty hroot ih
  | let_bind_borrowField envL a af f _ _ _ _ s rf _ _ hlookup_a hbt hlookup_f hnotIn hfresh _ ih =>
    exact weaken_let_bind_borrowField lenv envL env a af f _ _ _ _ s rf _ _
      hlookup_a hbt hlookup_f hnotIn hfresh
      hsub hfuneq hwfL hwfE hsite_tracked hvar_tracked huniq
      hpaths_to_nm hpaths_from_nm hself_loop_only_empty hroot ih
  | let_bind_borrowMutField envL a af f _ _ _ s rf _ _ hlookup_a hbt hlookup_f hnotIn hfresh _ ih =>
    exact weaken_let_bind_borrowMutField lenv envL env a af f _ _ _ s rf _ _
      hlookup_a hbt hlookup_f hnotIn hfresh
      hsub hfuneq hwfL hwfE hsite_tracked hvar_tracked huniq
      hpaths_to_nm hpaths_from_nm hself_loop_only_empty hroot ih
  | let_bind_freeze envL a c τ r r' isBor cont retTypes hlook hnotIn hfresh _ ih =>
    exact weaken_let_bind_freeze lenv envL env a c τ r r' isBor _ _
      hlook hnotIn hfresh
      hsub hfuneq hwfL hwfE hsite_tracked hvar_tracked huniq
      hpaths_to_nm hpaths_from_nm hself_loop_only_empty hroot ih
  | var_assign_valid envL x a ax τ ms r _ _ hms hlook_x hlook_a hnotIn hfresh _ ih =>
    exact weaken_var_assign_valid lenv envL env x a ax τ ms r _ _
      hms hlook_x hlook_a hnotIn hfresh
      hsub hfuneq hwfL hwfE hsite_tracked hvar_tracked huniq
      hpaths_to_nm hpaths_from_nm hself_loop_only_empty hroot ih
  | call envL fnName as bs params rets outRefsL envL' cont retTypes
      hfunL htcL hfreshSitesL hfreshRefsL hnodupL hpopL hisoL _ ih =>
    exact weaken_call lenv envL env fnName as bs params rets outRefsL envL' cont retTypes
      hfunL htcL hfreshSitesL hfreshRefsL hnodupL hpopL hisoL
      hsub hfuneq hwfL hwfE hsite_tracked hvar_tracked huniq
      hpaths_to_nm hpaths_from_nm hself_loop_only_empty hroot ih
  -- ==================== Complex non-pathEnv cases ====================
  | let_bind_pack _ _ _ _ _ _ _ hnotIn hft hfc hfi _ ih =>
    exact weaken_let_bind_pack lenv _ env _ _ _ _ _ _ hnotIn hft hfc hfi
      hsub hfuneq hwfL hwfE hsite_tracked hvar_tracked huniq
      hpaths_to_nm hpaths_from_nm hself_loop_only_empty hroot ih
  | unpack _ _ _ _ _ _ hlook_b hfresh hinj_f hexist _ ih =>
    exact weaken_unpack lenv _ env _ _ _ _ _ hlook_b hfresh hinj_f hexist
      hsub hfuneq hwfL hwfE hsite_tracked hvar_tracked huniq
      hpaths_to_nm hpaths_from_nm hself_loop_only_empty hroot ih

end LeanMove.Typing.TypeSoundness
