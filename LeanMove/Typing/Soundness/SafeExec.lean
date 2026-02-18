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

import LeanMove.Typing.Soundness.Progress
import LeanMove.Typing.Soundness.Preservation

/-!
# Type Soundness: Safe Execution

Defines `SafeExecState` and proves that safety is preserved by `step` and `run`.
-/

namespace LeanMove.Typing.TypeSoundness

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Typing
open LeanMove.Semantics
open AssocMap
open Regex

-- ============================================================
-- Part 9: Safe Execution State
-- ============================================================

/-- An exec state is "safe" if running states are well-typed (with stack safety)
    and error states are not danglingRef errors. -/
def SafeExecState (state : ExecState) : Prop :=
  match state with
  | .running m => ∃ env lenv retTypes rmap,
      WellTypedState m env lenv retTypes rmap ∧
      StackSafe m.stack m.frame.returnInfo m.heap
  | .halted _ => True
  | .error (.danglingRef _) => False
  | .error _ => True

/-- A safe exec state steps to a safe exec state.
    Uses no_danglingRef_progress (to rule out danglingRef errors)
    and preservation (to maintain WellTypedState for running states). -/
theorem safe_step (state : ExecState)
    (hsafe : SafeExecState state) :
    SafeExecState (step state) := by
  cases state with
  | halted v => simp [step, SafeExecState]
  | error e => simp only [step]; exact hsafe
  | running m =>
    obtain ⟨env, lenv, retTypes, rmap, hwt, hss⟩ := hsafe
    show SafeExecState (step (.running m))
    generalize hres : step (.running m) = result
    cases result with
    | running m' =>
      simp only [SafeExecState]
      exact preservation m m' env lenv retTypes rmap hwt hss hres
    | halted v => simp [SafeExecState]
    | error e =>
      cases e with
      | danglingRef loc =>
        exact absurd hres (no_danglingRef_progress m env lenv retTypes rmap hwt loc)
      | uninitializedVar _ => simp [SafeExecState]
      | uninitializedSite _ => simp [SafeExecState]
      | typeMismatch _ => simp [SafeExecState]
      | unknownFunction _ => simp [SafeExecState]
      | unknownLabel _ => simp [SafeExecState]
      | invalidFieldAccess _ => simp [SafeExecState]
      | divisionByZero => simp [SafeExecState]
      | outOfFuel => simp [SafeExecState]
      | arityMismatch _ => simp [SafeExecState]

/-- A SafeExecState is never a danglingRef error -/
theorem SafeExecState.not_danglingRef {state : ExecState}
    (hsafe : SafeExecState state) :
    ∀ loc, state ≠ .error (.danglingRef loc) := by
  intro loc h; subst h; exact hsafe

-- ============================================================
-- Part 10: Iterated Safety
-- ============================================================

/-- A safe exec state remains danglingRef-free after any number of steps.
    By induction on fuel, using safe_step at each iteration. -/
theorem safe_run_no_danglingRef (state : ExecState)
    (hsafe : SafeExecState state) :
    ∀ n loc, Semantics.run n state ≠ .error (.danglingRef loc) := by
  intro n
  induction n generalizing state with
  | zero =>
    intro loc h
    unfold Semantics.run at h
    injection h with h'
    exact nomatch h'
  | succ n ih =>
    intro loc h
    unfold Semantics.run at h
    match state, hsafe with
    | .running m, hsafe =>
      exact ih (step (.running m)) (safe_step (.running m) hsafe) loc h
    | .halted _, _ =>
      exact absurd h (by intro h'; cases h')
    | .error _, hsafe =>
      exact SafeExecState.not_danglingRef hsafe loc h

end LeanMove.Typing.TypeSoundness
