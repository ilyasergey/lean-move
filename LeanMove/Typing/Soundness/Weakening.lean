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

/-- MoveType.compatible is preserved by applySubstMoveType when σ doesn't create roots -/
private lemma MoveType_compatible_subst (σ : Aref → Aref) (τ retType : MoveType)
    (hcompat : MoveType.compatible τ retType)
    (hσroot : σ .root = .root)
    (hσ : ∀ r, r ≠ .root → σ r ≠ .root) :
    MoveType.compatible (applySubstMoveType σ τ) retType := by
  cases τ with
  | basic bt =>
    simp [applySubstMoveType]
    exact hcompat
  | ref bt r bk =>
    cases retType with
    | basic _ => exact hcompat
    | ref bt' r' bk' =>
      simp only [MoveType.compatible, applySubstMoveType] at hcompat ⊢
      exact ⟨hcompat.1, Aref_Compatible_subst hcompat.2.1 hσroot (hσ r), hcompat.2.2⟩

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
-- Main weakening theorem
-- ============================================================

/-- Weakening: if a statement type-checks under envL, and envL.subsumes env,
    then it also type-checks under env.
    Requires both environments to be well-formed (always holds in practice). -/
theorem typecheck_stmt_weaken (lenv : LabelEnv) (envL env : TypeEnv) (s : Stmt) (retType : MoveType)
    (htyped : typecheck_stmt lenv envL s retType)
    (hsub : TypeEnv.subsumes envL env)
    (hwfL : TypeEnv.WellFormed envL)
    (hwfE : TypeEnv.WellFormed env) :
    typecheck_stmt lenv env s retType := by
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
  | ret _ _ _ hret =>
    obtain ⟨σ, hid, _, hse, _, _, hnonroot, _⟩ := hsub
    apply typecheck_stmt.ret
    intro a ha
    obtain ⟨τ, hlook, hcompat⟩ := hret a ha
    have hlook_env := SiteEnvSubstEquiv_lookup_some σ _ _ _ _ hse hlook
    refine ⟨applySubstMoveType σ τ, hlook_env, ?_⟩
    have hσroot : σ .root = .root := hid .root (fun n h => by cases h)
    exact MoveType_compatible_subst σ τ _ hcompat hσroot hnonroot
  | abort _ _ _ _ hlook =>
    obtain ⟨σ, _, _, hse, _, _, _⟩ := hsub
    exact typecheck_stmt.abort lenv env _ _ _
      (SiteEnvSubstEquiv_lookup_some σ _ _ _ _ hse hlook)
  -- ==================== Non-terminal, no pathEnv change ====================
  | let_bind_intLit _ _ _ _ _ hnotIn _ ih =>
    obtain ⟨σ, hid, hve, hse, hrefs, hinj, hnonroot, hpaths⟩ := hsub
    apply typecheck_stmt.let_bind_intLit
    · exact SiteEnvSubstEquiv_notIn σ _ _ _ hse hnotIn
    · apply ih
      · exact ⟨σ, hid, hve,
          SiteEnvSubstEquiv_insert σ _ _ _ _ _ hse (applySubstMoveType_basic σ _),
          hrefs, hinj, hnonroot, hpaths⟩
      · exact TypeEnv.insert_siteEnv_wf _ _ _ hwfL trivial
      · exact TypeEnv.insert_siteEnv_wf _ _ _ hwfE trivial
      · exact hroot
  | let_bind_copy_val _ _ _ _ _ _ _ hlookup hnotIn _ ih =>
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
    · exact TypeEnv.insert_siteEnv_wf _ _ _ hwfL trivial
    · exact TypeEnv.insert_siteEnv_wf _ _ _ hwfE trivial
    · exact hroot
  | let_bind_move _ _ _ _ _ _ _ hlookup hnb hnotIn _ ih =>
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
    · exact ⟨hwfL.pathEnv_wf,
            SiteEnv.insert_refs_not_root _ _ _ hwfL.siteEnv_wf hτ_nr,
            VarEnv.update_refs_not_root _ _ _ hwfL.varEnv_wf hτ_nr⟩
    · exact ⟨hwfE.pathEnv_wf,
            SiteEnv.insert_refs_not_root _ _ _ hwfE.siteEnv_wf
              (moveTypeRefNotRoot_applySubst σ _ hτ_nr hnonroot),
            VarEnv.update_refs_not_root _ _ _ hwfE.varEnv_wf
              (moveTypeRefNotRoot_applySubst σ _ hτ_nr hnonroot)⟩
    · exact hroot
  | let_bind_binop _ _ _ _ _ sa sb sc _ _ hlook_a hlook_b hbinop hnotIn _ ih =>
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
      · exact TypeEnv.delete_delete_insert_wf _ _ _ _ _ hwfL trivial
      · exact TypeEnv.delete_delete_insert_wf _ _ _ _ _ hwfE trivial
      · exact hroot
  | var_assign_invalid _ _ _ _ _ _ _ hlook_x hlook_a hcompat _ ih =>
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
      · exact ⟨hwfL.pathEnv_wf,
              SiteEnv.delete_refs_not_root _ _ hwfL.siteEnv_wf,
              VarEnv.update_refs_not_root _ _ _ hwfL.varEnv_wf hτ'_nr⟩
      · exact ⟨hwfE.pathEnv_wf,
              SiteEnv.delete_refs_not_root _ _ hwfE.siteEnv_wf,
              VarEnv.update_refs_not_root _ _ _ hwfE.varEnv_wf
                (moveTypeRefNotRoot_applySubst σ _ hτ'_nr hnonroot)⟩
      · exact hroot
  -- ==================== Cases with pathEnv changes (sorry for now) ====================
  | let_bind_copy_ref => sorry
  | let_bind_borrowImm => sorry
  | let_bind_borrowMut => sorry
  | let_bind_borrowField => sorry
  | let_bind_borrowMutField => sorry
  | let_bind_readRef => sorry
  | let_bind_freeze => sorry
  | write_ref => sorry
  | var_assign_valid => sorry
  | release => sorry
  | call => sorry
  -- ==================== Complex non-pathEnv cases ====================
  | let_bind_pack => sorry
  | unpack => sorry

end LeanMove.Typing.TypeSoundness
