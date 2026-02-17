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

/-- Weakening: if a statement type-checks under envL, and envL.subsumes env,
    then it also type-checks under env.
    Requires both environments to be well-formed and refs tracked (always holds in practice). -/
theorem typecheck_stmt_weaken (lenv : LabelEnv) (envL env : TypeEnv) (s : Stmt) (retType : MoveType)
    (htyped : typecheck_stmt lenv envL s retType)
    (hsub : TypeEnv.subsumes envL env)
    (hwfL : TypeEnv.WellFormed envL)
    (hwfE : TypeEnv.WellFormed env)
    (hsite_tracked : ∀ s bt r bk, lookup envL.siteEnv s = some (.ref bt r bk) → r ∈ envL.pathEnv.refs)
    (hvar_tracked : ∀ x bt r bk ms, lookup envL.varEnv x = some (.validVar, .ref bt r bk, ms) → r ∈ envL.pathEnv.refs)
    (huniq : RefsUnique envL.varEnv envL.siteEnv) :
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
      · exact site_tracked_insert_basic _ _ _ _ hsite_tracked
      · exact hvar_tracked
      · exact RefsUnique_insert_basic _ _ _ _ huniq
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
    · exact site_tracked_insert_basic _ _ _ _ hsite_tracked
    · exact hvar_tracked
    · exact RefsUnique_insert_basic _ _ _ _ huniq
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
    · exact site_tracked_insert_from_var _ _ _ _ _ _ _ hlookup hsite_tracked hvar_tracked
    · exact var_tracked_update_invalid _ _ _ _ _ hvar_tracked
    · exact RefsUnique_move_to_site _ _ _ _ _ _ hlookup huniq
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
      · exact site_tracked_insert_basic _ _ _ _
          (site_tracked_delete _ _ sb (site_tracked_delete _ _ sa hsite_tracked))
      · exact hvar_tracked
      · exact RefsUnique_insert_basic _ _ _ _
          (RefsUnique_delete_site _ _ _ (RefsUnique_delete_site _ _ _ huniq))
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
      · exact site_tracked_delete _ _ _ hsite_tracked
      · exact var_tracked_update_valid_from_site _ _ _ _ _ _ _ hlook_a hsite_tracked hvar_tracked
      · exact RefsUnique_assign_from_site _ _ _ _ _ _ hlook_a huniq
      · exact hroot
  -- ==================== Cases with pathEnv changes =============================
  | let_bind_readRef _ a c r _ _ _ _ hlook_a hnotIn _ ih =>
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
        rw [if_neg (not_or.mpr ⟨hu.2, hv.2⟩)]
        rw [if_neg (not_or.mpr ⟨hσu_ne, hσv_ne⟩)] at hinterp
        exact hpaths u v hu.1 hv.1 path hinterp
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
    · simp only [delete_ref_node, List.mem_filter, decide_eq_true_eq]
      exact ⟨hroot, Ne.symm hr_ne_root⟩
  | write_ref _ a b τ r _ _ hlook_a hlook_b houtbound _ ih =>
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
        rw [if_neg (not_or.mpr ⟨hu.2, hv.2⟩)]
        rw [if_neg (not_or.mpr ⟨hσu_ne, hσv_ne⟩)] at hinterp
        exact hpaths u v hu.1 hv.1 path hinterp
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
    · simp only [garbage_collect, List.mem_filter, decide_eq_true_eq]
      exact ⟨hroot, Ne.symm hr_ne_root⟩
  | release _ a _ r _ _ _ hlook_a _ ih =>
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
        rw [if_neg (not_or.mpr ⟨hu.2, hv.2⟩)]
        rw [if_neg (not_or.mpr ⟨hσu_ne, hσv_ne⟩)] at hinterp
        exact hpaths u v hu.1 hv.1 path hinterp
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
    · simp only [delete_ref_node, List.mem_filter, decide_eq_true_eq]
      exact ⟨hroot, Ne.symm hr_ne_root⟩
  | let_bind_copy_ref envL a _ _ _ s t _ _ _ hlookup hnotIn hfresh ht_not_varRef _ ih =>
    obtain ⟨σ, hid, hve, hse, hrefs, hinj, hnonroot, hpaths⟩ := hsub
    have hlook_env := VarEnvSubstEquiv_lookup_valid σ _ _ _ _ _ hve hlookup
    simp only [applySubstMoveType] at hlook_env
    -- Freshness of t in envL
    have ht_fresh_pe : t ∉ envL.pathEnv.refs := by
      have := freshRefInEnvBool_implies_freshRefBool t _ hfresh
      exact (freshRef_iff_freshRefBool t envL.pathEnv).mpr this
    have ht_ne_root : t ≠ .root := fun h => ht_fresh_pe (h ▸ hroot)
    -- t is a refid (from ht_ne_root + ht_not_varRef)
    have ht_refid : ∃ n, t = .refid n := by
      cases t with
      | root => exact absurd rfl ht_ne_root
      | refid n => exact ⟨n, rfl⟩
      | varRef v => exact absurd rfl (ht_not_varRef v)
    -- Pick fresh t' for env
    let t' := nextFreshRefInEnv env
    have ht'_fresh := nextFreshRefInEnv_fresh env
    have ht'_fresh_pe := nextFreshRefInEnv_not_in_pathEnv env
    have ht'_not_root := nextFreshRefInEnv_not_root env
    have ht'_not_varRef := nextFreshRefInEnv_not_varRef env
    have ht'_not_mapped : t' ∉ envL.pathEnv.refs.map σ := by rw [hrefs]; exact ht'_fresh_pe
    -- s ∈ envL.pathEnv.refs (from var_tracked)
    have hs_mem := hvar_tracked _ _ _ _ _ hlookup
    -- Apply the copy_ref rule
    apply typecheck_stmt.let_bind_copy_ref lenv env _ _ _ _ (σ s) t' _ _ _
      hlook_env
      (SiteEnvSubstEquiv_notIn σ _ _ _ hse hnotIn)
      ht'_fresh
      (fun v => ht'_not_varRef v)
    -- IH: need subsumes for modified envs
    apply ih
    · -- subsumes with extendSubst σ t t'
      refine ⟨extendSubst σ t t',
        extendSubst_id σ t t' hid ht_refid,
        VarEnvSubstEquiv_extend σ t t' _ _ hve
          (fun x' bt' s' bk' ms' hlook' =>
            Ne.symm (freshRefInEnvBool_ne_varEnv_ref t _ x' .validVar bt' s' bk' ms' hfresh hlook')),
        SiteEnvSubstEquiv_extend_insert_ref σ t t' _ _ _ _ _ hse
          (fun k bt r bk hlook' =>
            Ne.symm (freshRefInEnvBool_ne_siteEnv_ref t _ k bt r bk hfresh hlook')),
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
    · -- WellFormed envL'
      exact ⟨update_with_epsilon_wellformed t s envL.pathEnv hwfL.pathEnv_wf ht_ne_root ht_not_varRef,
             SiteEnv.insert_refs_not_root _ _ _ hwfL.siteEnv_wf ht_ne_root,
             hwfL.varEnv_wf⟩
    · -- WellFormed env'
      exact ⟨update_with_epsilon_wellformed t' (σ s) env.pathEnv hwfE.pathEnv_wf ht'_not_root (fun v => ht'_not_varRef v),
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
          Ne.symm (freshRefInEnvBool_ne_varEnv_ref t _ x' .validVar bt' r bk' ms' hfresh hlook'))
        (fun s' bt' r bk' hlook' =>
          Ne.symm (freshRefInEnvBool_ne_siteEnv_ref t _ s' bt' r bk' hfresh hlook'))
    · -- root ∈ updated refs
      simp only [uwe_epsilon_refs_fresh t s envL.pathEnv ht_fresh_pe]
      exact .tail _ hroot
  | let_bind_borrowImm envL a x_var _ _ r _ _ hlookup hnotIn hfresh hr_not_varRef _ ih =>
    obtain ⟨σ, hid, hve, hse, hrefs, hinj, hnonroot, hpaths⟩ := hsub
    have hlook_env := VarEnvSubstEquiv_lookup_valid σ _ _ _ _ _ hve hlookup
    simp only [applySubstMoveType] at hlook_env
    -- Freshness of r in envL
    have hr_fresh_pe : r ∉ envL.pathEnv.refs := by
      have := freshRefInEnvBool_implies_freshRefBool r _ hfresh
      exact (freshRef_iff_freshRefBool r envL.pathEnv).mpr this
    have hr_ne_root : r ≠ .root := fun h => hr_fresh_pe (h ▸ hroot)
    have hr_refid : ∃ n, r = .refid n := by
      cases r with
      | root => exact absurd rfl hr_ne_root
      | refid n => exact ⟨n, rfl⟩
      | varRef v => exact absurd rfl (hr_not_varRef v)
    have hσ_root : σ .root = .root := hid .root (fun n => Aref.noConfusion)
    -- Pick fresh r' for env
    let r' := nextFreshRefInEnv env
    have hr'_fresh := nextFreshRefInEnv_fresh env
    have hr'_fresh_pe := nextFreshRefInEnv_not_in_pathEnv env
    have hr'_not_root := nextFreshRefInEnv_not_root env
    have hr'_not_varRef := nextFreshRefInEnv_not_varRef env
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
      hr'_fresh
      (fun v => hr'_not_varRef v)
    -- IH: need subsumes for modified envs
    apply ih
    · -- subsumes: simplify compound pathEnvs via absorb lemma
      rw [uwe_absorbs_epsilon r .root _ envL.pathEnv hr_fresh_pe (Ne.symm hr_ne_root),
          uwe_absorbs_epsilon r' .root _ env.pathEnv hr'_fresh_pe (Ne.symm hr'_not_root)]
      refine ⟨extendSubst σ r r',
        extendSubst_id σ r r' hid hr_refid,
        VarEnvSubstEquiv_extend σ r r' _ _ hve
          (fun x' bt' s' bk' ms' hlook' =>
            Ne.symm (freshRefInEnvBool_ne_varEnv_ref r _ x' .validVar bt' s' bk' ms' hfresh hlook')),
        SiteEnvSubstEquiv_extend_insert_ref σ r r' _ _ _ _ _ hse
          (fun k bt ref bk hlook' =>
            Ne.symm (freshRefInEnvBool_ne_siteEnv_ref r _ k bt ref bk hfresh hlook')),
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
    · -- WellFormed envL'
      exact ⟨update_with_extension_wellformed r .root [.root_to_var x_var]
              (update_with_epsilon r r envL.pathEnv)
              (update_with_epsilon_wellformed r r envL.pathEnv hwfL.pathEnv_wf hr_ne_root hr_not_varRef)
              hr_ne_root hr_not_varRef,
             SiteEnv.insert_refs_not_root _ _ _ hwfL.siteEnv_wf hr_ne_root,
             hwfL.varEnv_wf⟩
    · -- WellFormed env'
      exact ⟨update_with_extension_wellformed r' .root [.root_to_var x_var]
              (update_with_epsilon r' r' env.pathEnv)
              (update_with_epsilon_wellformed r' r' env.pathEnv hwfE.pathEnv_wf hr'_not_root
                (fun v => hr'_not_varRef v))
              hr'_not_root (fun v => hr'_not_varRef v),
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
          Ne.symm (freshRefInEnvBool_ne_varEnv_ref r _ x' .validVar bt' ref bk' ms' hfresh hlook'))
        (fun s' bt' ref bk' hlook' =>
          Ne.symm (freshRefInEnvBool_ne_siteEnv_ref r _ s' bt' ref bk' hfresh hlook'))
    · -- root ∈ updated refs
      simp only [h_compound_refs]
      exact .tail _ hroot
  | let_bind_borrowMut envL a x_var _ _ r _ _ hle hlookup hnotIn hfresh hr_not_varRef _ ih =>
    obtain ⟨σ, hid, hve, hse, hrefs, hinj, hnonroot, hpaths⟩ := hsub
    have hlook_env := VarEnvSubstEquiv_lookup_valid σ _ _ _ _ _ hve hlookup
    simp only [applySubstMoveType] at hlook_env
    have hr_fresh_pe : r ∉ envL.pathEnv.refs := by
      have := freshRefInEnvBool_implies_freshRefBool r _ hfresh
      exact (freshRef_iff_freshRefBool r envL.pathEnv).mpr this
    have hr_ne_root : r ≠ .root := fun h => hr_fresh_pe (h ▸ hroot)
    have hr_refid : ∃ n, r = .refid n := by
      cases r with
      | root => exact absurd rfl hr_ne_root
      | refid n => exact ⟨n, rfl⟩
      | varRef v => exact absurd rfl (hr_not_varRef v)
    have hσ_root : σ .root = .root := hid .root (fun n => Aref.noConfusion)
    let r' := nextFreshRefInEnv env
    have hr'_fresh := nextFreshRefInEnv_fresh env
    have hr'_fresh_pe := nextFreshRefInEnv_not_in_pathEnv env
    have hr'_not_root := nextFreshRefInEnv_not_root env
    have hr'_not_varRef := nextFreshRefInEnv_not_varRef env
    have hr'_not_mapped : r' ∉ envL.pathEnv.refs.map σ := by rw [hrefs]; exact hr'_fresh_pe
    have h_compound_refs :
        (update_with_extension r .root [.root_to_var x_var]
          (update_with_epsilon r r envL.pathEnv)).refs = r :: envL.pathEnv.refs := by
      rw [uwe_absorbs_epsilon r .root _ envL.pathEnv hr_fresh_pe (Ne.symm hr_ne_root),
          uwe_refs_fresh r .root _ envL.pathEnv hr_fresh_pe]
    apply typecheck_stmt.let_bind_borrowMut lenv env _ _ _ _ r' _ _
      hle hlook_env
      (SiteEnvSubstEquiv_notIn σ _ _ _ hse hnotIn)
      hr'_fresh
      (fun v => hr'_not_varRef v)
    apply ih
    · -- subsumes
      rw [uwe_absorbs_epsilon r .root _ envL.pathEnv hr_fresh_pe (Ne.symm hr_ne_root),
          uwe_absorbs_epsilon r' .root _ env.pathEnv hr'_fresh_pe (Ne.symm hr'_not_root)]
      refine ⟨extendSubst σ r r',
        extendSubst_id σ r r' hid hr_refid,
        VarEnvSubstEquiv_extend σ r r' _ _ hve
          (fun x' bt' s' bk' ms' hlook' =>
            Ne.symm (freshRefInEnvBool_ne_varEnv_ref r _ x' .validVar bt' s' bk' ms' hfresh hlook')),
        SiteEnvSubstEquiv_extend_insert_ref σ r r' _ _ _ _ _ hse
          (fun k bt ref bk hlook' =>
            Ne.symm (freshRefInEnvBool_ne_siteEnv_ref r _ k bt ref bk hfresh hlook')),
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
    · exact ⟨update_with_extension_wellformed r .root [.root_to_var x_var]
              (update_with_epsilon r r envL.pathEnv)
              (update_with_epsilon_wellformed r r envL.pathEnv hwfL.pathEnv_wf hr_ne_root hr_not_varRef)
              hr_ne_root hr_not_varRef,
             SiteEnv.insert_refs_not_root _ _ _ hwfL.siteEnv_wf hr_ne_root,
             hwfL.varEnv_wf⟩
    · exact ⟨update_with_extension_wellformed r' .root [.root_to_var x_var]
              (update_with_epsilon r' r' env.pathEnv)
              (update_with_epsilon_wellformed r' r' env.pathEnv hwfE.pathEnv_wf hr'_not_root
                (fun v => hr'_not_varRef v))
              hr'_not_root (fun v => hr'_not_varRef v),
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
          Ne.symm (freshRefInEnvBool_ne_varEnv_ref r _ x' .validVar bt' ref bk' ms' hfresh hlook'))
        (fun s' bt' ref bk' hlook' =>
          Ne.symm (freshRefInEnvBool_ne_siteEnv_ref r _ s' bt' ref bk' hfresh hlook'))
    · simp only [h_compound_refs]
      exact .tail _ hroot
  | let_bind_borrowField envL a af f _ _ _ _ s rf _ _ hlookup_a hbt hlookup_f hnotIn hfresh hrf_not_varRef _ ih =>
    obtain ⟨σ, hid, hve, hse, hrefs, hinj, hnonroot, hpaths⟩ := hsub
    -- Site lookup in env
    have hlook_a_env := SiteEnvSubstEquiv_lookup_some σ _ _ _ _ hse hlookup_a
    simp only [applySubstMoveType] at hlook_a_env
    -- Freshness of rf in envL
    have hrf_fresh_pe : rf ∉ envL.pathEnv.refs := freshRefInEnv_implies_freshRef rf envL hfresh
    have hrf_ne_root : rf ≠ .root := fun h => hrf_fresh_pe (h ▸ hroot)
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
    have hrf'_not_varRef := nextFreshRefInEnv_not_varRef env
    have hrf'_not_mapped : rf' ∉ envL.pathEnv.refs.map σ := by rw [hrefs]; exact hrf'_fresh_pe
    -- s ∈ envL.pathEnv.refs (from site_tracked)
    have hs_mem := hsite_tracked _ _ _ _ hlookup_a
    -- Apply borrowField rule
    apply typecheck_stmt.let_bind_borrowField lenv env a af f _ _ _ _ (σ s) rf' _ _
      hlook_a_env hbt hlookup_f
      (SiteEnvSubstEquiv_notIn σ _ _ _ hse hnotIn)
      hrf'_fresh_prop
      (fun v => hrf'_not_varRef v)
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
    · -- WellFormed envL'
      exact ⟨update_with_extension_wellformed rf s [.field f] envL.pathEnv
              hwfL.pathEnv_wf hrf_ne_root hrf_not_varRef,
             SiteEnv.insert_refs_not_root _ _ _
              (SiteEnv.delete_refs_not_root _ _ hwfL.siteEnv_wf) hrf_ne_root,
             hwfL.varEnv_wf⟩
    · -- WellFormed env'
      exact ⟨update_with_extension_wellformed rf' (σ s) [.field f] env.pathEnv
              hwfE.pathEnv_wf hrf'_not_root (fun v => hrf'_not_varRef v),
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
    · -- root ∈ updated refs
      simp only [uwe_refs_fresh rf s _ envL.pathEnv hrf_fresh_pe]
      exact .tail _ hroot
  | let_bind_borrowMutField envL a af f _ _ _ s rf _ _ hlookup_a hbt hlookup_f hnotIn hfresh hrf_not_varRef _ ih =>
    obtain ⟨σ, hid, hve, hse, hrefs, hinj, hnonroot, hpaths⟩ := hsub
    have hlook_a_env := SiteEnvSubstEquiv_lookup_some σ _ _ _ _ hse hlookup_a
    simp only [applySubstMoveType] at hlook_a_env
    have hrf_fresh_pe : rf ∉ envL.pathEnv.refs := freshRefInEnv_implies_freshRef rf envL hfresh
    have hrf_ne_root : rf ≠ .root := fun h => hrf_fresh_pe (h ▸ hroot)
    have hrf_refid : ∃ n, rf = .refid n := by
      cases rf with
      | root => exact absurd rfl hrf_ne_root
      | refid n => exact ⟨n, rfl⟩
      | varRef v => exact absurd rfl (hrf_not_varRef v)
    let rf' := nextFreshRefInEnv env
    have hrf'_fresh_prop := nextFreshRefInEnv_fresh_prop env
    have hrf'_fresh_pe := nextFreshRefInEnv_not_in_pathEnv env
    have hrf'_not_root := nextFreshRefInEnv_not_root env
    have hrf'_not_varRef := nextFreshRefInEnv_not_varRef env
    have hrf'_not_mapped : rf' ∉ envL.pathEnv.refs.map σ := by rw [hrefs]; exact hrf'_fresh_pe
    have hs_mem := hsite_tracked _ _ _ _ hlookup_a
    apply typecheck_stmt.let_bind_borrowMutField lenv env a af f _ _ _ (σ s) rf' _ _
      hlook_a_env hbt hlookup_f
      (SiteEnvSubstEquiv_notIn σ _ _ _ hse hnotIn)
      hrf'_fresh_prop
      (fun v => hrf'_not_varRef v)
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
    · exact ⟨update_with_extension_wellformed rf s [.field f] envL.pathEnv
              hwfL.pathEnv_wf hrf_ne_root hrf_not_varRef,
             SiteEnv.insert_refs_not_root _ _ _
              (SiteEnv.delete_refs_not_root _ _ hwfL.siteEnv_wf) hrf_ne_root,
             hwfL.varEnv_wf⟩
    · exact ⟨update_with_extension_wellformed rf' (σ s) [.field f] env.pathEnv
              hwfE.pathEnv_wf hrf'_not_root (fun v => hrf'_not_varRef v),
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
    · simp only [uwe_refs_fresh rf s _ envL.pathEnv hrf_fresh_pe]
      exact .tail _ hroot
  | let_bind_freeze => sorry
  | var_assign_valid => sorry
  | call => sorry
  -- ==================== Complex non-pathEnv cases ====================
  | let_bind_pack _ _ _ _ _ _ _ hnotIn hft hfc hfi _ ih =>
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
      · exact TypeEnv.deleteAll_insert_wf _ _ _ _ hwfL trivial
      · exact TypeEnv.deleteAll_insert_wf _ _ _ _ hwfE trivial
      · exact site_tracked_insert_basic _ _ _ _
          (site_tracked_deleteAll _ _ _ hsite_tracked)
      · exact hvar_tracked
      · exact RefsUnique_insert_basic _ _ _ _ (RefsUnique_deleteAll _ _ _ huniq)
      · exact hroot
  | unpack _ _ _ _ _ _ hlook_b hfresh hinj_f hexist _ ih =>
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
      · exact hroot

end LeanMove.Typing.TypeSoundness
