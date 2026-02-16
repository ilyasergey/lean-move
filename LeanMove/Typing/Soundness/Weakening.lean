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

/-- applySubstMoveType distributes over composition -/
private lemma applySubstMoveType_comp (σ1 σ2 : Aref → Aref) (τ : MoveType) :
    applySubstMoveType (fun r => σ2 (σ1 r)) τ = applySubstMoveType σ2 (applySubstMoveType σ1 τ) := by
  cases τ with
  | basic _ => rfl
  | ref _ _ _ => rfl

/-- MoveType.baseCompatible is transitive -/
private lemma baseCompatible_trans (τ1 τ2 τ3 : MoveType) :
    MoveType.baseCompatible τ1 τ2 → MoveType.baseCompatible τ2 τ3 → MoveType.baseCompatible τ1 τ3 := by
  intro h12 h23
  cases τ1 <;> cases τ2 <;> cases τ3 <;> simp_all [MoveType.baseCompatible]

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

/-- Transitivity of TypeEnv.subsumes:
    if envL1.subsumes envL2 and envL2.subsumes env, then envL1.subsumes env. -/
theorem TypeEnv.subsumes_trans (envL1 envL2 env : TypeEnv) :
    TypeEnv.subsumes envL1 envL2 →
    TypeEnv.subsumes envL2 env →
    TypeEnv.subsumes envL1 env := by
  intro hsub1 hsub2
  obtain ⟨σ1, hid1, hve1, hse1, hrefs1, hinj1, hpaths1⟩ := hsub1
  obtain ⟨σ2, hid2, hve2, hse2, hrefs2, hinj2, hpaths2⟩ := hsub2
  refine ⟨fun r => σ2 (σ1 r), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- σ2 ∘ σ1 is identity on non-refid arefs
    intro r hr
    show σ2 (σ1 r) = r
    rw [hid1 r hr]; exact hid2 r hr
  · -- VarEnvSubstEquiv
    exact VarEnvSubstEquiv_trans σ1 σ2 _ _ _ hve1 hve2
  · -- SiteEnvSubstEquiv
    exact SiteEnvSubstEquiv_trans σ1 σ2 _ _ _ hse1 hse2
  · -- refs map: fun r => σ2 (σ1 r) = σ2 ∘ σ1
    have hcomp : (fun r => σ2 (σ1 r)) = (σ2 ∘ σ1) := rfl
    rw [hcomp, ← List.map_map, hrefs1, hrefs2]
  · -- σ2 ∘ σ1 is injective on envL1.pathEnv.refs
    intro u v hu hv huv
    have hσ1u : σ1 u ∈ envL2.pathEnv.refs := by
      rw [← hrefs1]; exact List.mem_map_of_mem (f := σ1) hu
    have hσ1v : σ1 v ∈ envL2.pathEnv.refs := by
      rw [← hrefs1]; exact List.mem_map_of_mem (f := σ1) hv
    exact hinj1 u v hu hv (hinj2 (σ1 u) (σ1 v) hσ1u hσ1v huv)
  · -- Path inclusion
    intro u v hu hv path hinterp
    have hσ1u : σ1 u ∈ envL2.pathEnv.refs := by
      rw [← hrefs1]; exact List.mem_map_of_mem (f := σ1) hu
    have hσ1v : σ1 v ∈ envL2.pathEnv.refs := by
      rw [← hrefs1]; exact List.mem_map_of_mem (f := σ1) hv
    exact hpaths1 u v hu hv path (hpaths2 (σ1 u) (σ1 v) hσ1u hσ1v path hinterp)

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

/-- Weakening: if a statement type-checks under envL, and envL.subsumes env,
    then it also type-checks under env. -/
theorem typecheck_stmt_weaken (lenv : LabelEnv) (envL env : TypeEnv) (s : Stmt) (retType : MoveType) :
    typecheck_stmt lenv envL s retType →
    TypeEnv.subsumes envL env →
    typecheck_stmt lenv env s retType := by
  intro htyped hsub
  induction htyped
  case skip =>
    exact typecheck_stmt.skip lenv env _
  case jump envJ _ envL' _ hlookup hsubJ =>
    exact typecheck_stmt.jump lenv env _ envL' _ hlookup
      (TypeEnv.subsumes_trans envL' envJ env hsubJ hsub)
  case branch envB a _ _ envL1 envL2 _ hsite hl1 hl2 hs1 hs2 =>
    obtain ⟨σ, hid, hve, hse, hrefs, hinj, hpaths⟩ := hsub
    have hsite_env : lookup env.siteEnv a = some (.basic .tbool) := by
      have := SiteEnvSubstEquiv_lookup_some σ _ _ _ _ hse hsite
      simp only [applySubstMoveType] at this
      exact this
    have hdel_sub : TypeEnv.subsumes
        {envB with siteEnv := delete envB.siteEnv a}
        {env with siteEnv := delete env.siteEnv a} :=
      ⟨σ, hid, hve, SiteEnvSubstEquiv_delete σ _ _ _ hse, hrefs, hinj, hpaths⟩
    exact typecheck_stmt.branch lenv env a _ _ envL1 envL2 _ hsite_env hl1 hl2
      (TypeEnv.subsumes_trans envL1 _ _ hs1 hdel_sub)
      (TypeEnv.subsumes_trans envL2 _ _ hs2 hdel_sub)
  all_goals sorry

end LeanMove.Typing.TypeSoundness
