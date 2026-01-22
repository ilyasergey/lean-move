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

import LeanMove.Checker.TypeChecking

/-!
# Type Checking Proofs for MoveLight

This file contains soundness proofs for the algorithmic type checking functions
defined in `TypeChecking.lean`.

## Contents
- `PathEnv.WellFormed` - Well-formedness predicate for PathEnv
- `PathEnv.init_wellformed` - Proof that initial PathEnv is well-formed
- `not_borrowed_bool_implies_not_borrowed` - Soundness of boolean borrow check
- `check_usage_sound` - Soundness of algorithmic usage checking
-/

namespace LeanMove.Checker

open Lang
open Lang.MoveLight
open AssocMap
open Regex

/-- Helper: not_borrowed_bool being true implies not_borrowed for refs in pathEnv.refs
    when the regex has a simple form (empty, ε, or char). -/
lemma not_borrowed_bool_implies_not_borrowed_for_simple_regex (x : Var) (env : TypeEnv) :
    not_borrowed_bool x env = true →
    ∀ r ∈ env.pathEnv.refs,
      let regex := env.pathEnv.paths (.root, r)
      ¬interpret_regex regex [.root_to_var x] := by
  intro hbool r hr
  simp only [not_borrowed_bool, List.all_eq_true] at hbool
  have h := hbool r hr
  simp only at h
  split at h
  · -- regex = .empty
    rename_i heq
    simp only [heq, Regex.interpret_regex]
    exact fun a => a
  · -- regex = .ε
    rename_i heq
    simp only [heq, Regex.interpret_regex]
    intro hcontra
    cases hcontra
  · -- regex = .char c where c ≠ .root_to_var x
    rename_i c heq
    simp only [bne_iff_ne, ne_eq] at h
    simp only [heq, Regex.interpret_regex]
    intro hcontra
    -- hcontra : [.root_to_var x] = [c], so .root_to_var x = c
    have heq' : PathElement.root_to_var x = c := by
      injection hcontra
    exact h heq'.symm
  · -- complex regex - not_borrowed_bool returns false, contradiction
    simp at h

/-- A PathEnv is well-formed if refs not in the refs list have paths that don't accept
    any single-element path from root. This holds for PathEnvs constructed via the
    standard operations (init, update_with_extension, update_with_epsilon, etc.). -/
def PathEnv.WellFormed (pe : PathEnv) : Prop :=
  ∀ r, r ∉ pe.refs → ∀ p : PathElement, ¬interpret_regex (pe.paths (.root, r)) [p]

/-- PathEnv.init is well-formed: the only ref is .root, and paths from root to
    non-root refs are empty (which doesn't accept any path). -/
lemma PathEnv.init_wellformed : PathEnv.WellFormed PathEnv.init := by
  intro r hr p
  simp only [PathEnv.init, List.mem_singleton] at hr
  -- r ≠ .root, so paths (.root, r) = empty
  simp only [PathEnv.init]
  have hne : Aref.root ≠ r := fun h => hr h.symm
  simp only [hne, ↓reduceIte, Regex.interpret_regex]
  exact fun a => a

/-- For well-formed PathEnvs, not_borrowed_bool = true implies not_borrowed. -/
lemma not_borrowed_bool_implies_not_borrowed (x : Var) (env : TypeEnv)
    (hwf : PathEnv.WellFormed env.pathEnv) :
    not_borrowed_bool x env = true → not_borrowed x env := by
  intro hbool r
  by_cases hr : r ∈ env.pathEnv.refs
  · -- r is in refs: use the simple regex lemma
    exact not_borrowed_bool_implies_not_borrowed_for_simple_regex x env hbool r hr
  · -- r not in refs: use well-formedness
    exact hwf r hr (.root_to_var x)

/-- Soundness: if check_usage returns some env', then the typecheck_usage relation holds.
    Requires the PathEnv to be well-formed (refs not in pathEnv.refs have empty/ε paths). -/
theorem check_usage_sound (env env' : TypeEnv) (u : Usage) (a : Site) (τ : MoveType)
    (hwf : PathEnv.WellFormed env.pathEnv) :
    check_usage env u a τ = some env' →
    typecheck_usage env u env' a τ := by
  intro h
  unfold check_usage at h
  split at h
  · -- notIn check failed
    simp at h
  · -- notIn check passed
    rename_i hnotIn
    simp only [Bool.not_eq_true, Bool.not_eq_false] at hnotIn
    cases u with
    | move x =>
      simp only at h
      split at h
      · simp at h  -- not_borrowed_bool check failed
      · rename_i hnb
        simp only [Bool.not_eq_true, Bool.not_eq_false] at hnb
        split at h
        · rename_i hlookup
          split at h
          · rename_i hbeq
            simp only [Option.some.injEq] at h
            subst h
            have hτ := MoveType.eq_of_beq τ _ hbeq
            subst hτ
            have hnb' := not_borrowed_bool_implies_not_borrowed x env hwf hnb
            exact typecheck_usage.t_umove env _ x _ _ a hlookup hnb' hnotIn rfl
          · simp at h
        · simp at h
    | copy x =>
      simp only at h
      split at h
      · -- basic type case
        rename_i bt ms hlookup
        split at h
        · rename_i hbeq
          simp only [Option.some.injEq] at h
          subst h
          have hτ : τ = .basic bt := MoveType.eq_of_beq τ (.basic bt) hbeq
          subst hτ
          apply typecheck_usage.t_ucopy_val
          · exact hlookup
          · exact hnotIn
          · rfl
        · simp at h
      · -- reference type case
        rename_i innerτ s isBor ms hlookup
        split at h
        · rename_i innerτ' t isBor'
          split at h
          · rename_i hcond
            simp only [Bool.and_eq_true, beq_iff_eq] at hcond
            obtain ⟨⟨hbt, hisBor⟩, hfresh⟩ := hcond
            simp only [Option.some.injEq] at h
            subst h hisBor
            have hbt' := BasicMoveType.eq_of_beq innerτ innerτ' hbt
            subst hbt'
            apply typecheck_usage.t_ucopy_ref
            · exact hlookup
            · exact hnotIn
            · exact hfresh
            · rfl
          · simp at h
        · simp at h
      · simp at h
    | borrowImm x =>
      simp only at h
      split at h
      · rename_i bt ms hlookup
        split at h
        · rename_i bt' r
          split at h
          · rename_i hcond
            simp only [Bool.and_eq_true] at hcond
            obtain ⟨hbt, hfresh⟩ := hcond
            simp only [Option.some.injEq] at h
            subst h
            have hbt' := BasicMoveType.eq_of_beq bt bt' hbt
            subst hbt'
            apply typecheck_usage.t_uborrowImm_val
            · exact hlookup
            · exact hnotIn
            · exact hfresh
            · rfl
          · simp at h
        · simp at h
      · simp at h
    | borrowMut x =>
      simp only at h
      split at h
      · -- lookup succeeded with (.validVar, .basic bt, .mutable)
        rename_i _discr ms hlookup
        split at h
        · -- τ = .ref bt' r .siteBorrowMut (bt' is BasicMoveType, r is Aref)
          rename_i _ theAref  -- first is bt', second is r (Aref)
          split at h
          · -- condition is true
            rename_i hcond
            simp only [Bool.and_eq_true] at hcond
            obtain ⟨hbt, hfresh⟩ := hcond
            simp only [Option.some.injEq] at h
            subst h
            have hms_eq := BasicMoveType.eq_of_beq ms _ hbt
            subst hms_eq
            exact typecheck_usage.t_uborrowMut_val env _ x ms .mutable a theAref
              (by simp only [LE.le, Mut.le]) hlookup hnotIn hfresh rfl
          · simp at h
        · simp at h
      · simp at h

end LeanMove.Checker
