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
An execution state is safe if running states are well-typed, halted states are
trivially safe, and error states are "acceptable" (not preventable by the type system).
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
    and error states are acceptable (not preventable by the type system).
    Acceptable errors: divisionByZero, outOfFuel, aborted.
    All other errors (danglingRef, uninitializedVar, uninitializedSite,
    unknownLabel, unknownFunction, arityMismatch, invalidFieldAccess,
    typeMismatch) are ruled out by well-typedness. -/
def SafeExecState (state : ExecState) : Prop :=
  match state with
  | .running m => ∃ env lenv retTypes rmap,
      WellTypedState m env lenv retTypes rmap ∧
      StackSafe env.enumEnv m.stack m.frame.returnInfo m.heap retTypes
  | .halted _ => True
  | .error e => e.isAcceptable

/-- A safe exec state steps to a safe exec state.
    Uses step_error_is_acceptable (to rule out all non-acceptable errors)
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
      obtain ⟨env', lenv', retTypes', rmap', henum_eq, hwt', hss'⟩ :=
        preservation m m' env lenv retTypes rmap hwt hss hres
      exact ⟨env', lenv', retTypes', rmap', hwt', henum_eq ▸ hss'⟩
    | halted v => simp [SafeExecState]
    | error e =>
      simp only [SafeExecState]
      exact step_error_is_acceptable m env lenv retTypes rmap hwt hss e hres

/-- A SafeExecState is never a non-acceptable error -/
theorem SafeExecState.not_error {state : ExecState}
    (hsafe : SafeExecState state) (e : RuntimeError) (hna : ¬e.isAcceptable) :
    state ≠ .error e := by
  intro h; subst h; exact hna hsafe

/-- A SafeExecState is never a danglingRef error (backward-compatible corollary) -/
theorem SafeExecState.not_danglingRef {state : ExecState}
    (hsafe : SafeExecState state) :
    ∀ loc, state ≠ .error (.danglingRef loc) := by
  intro loc
  exact SafeExecState.not_error hsafe (.danglingRef loc) (by simp [RuntimeError.isAcceptable])

-- ============================================================
-- Part 10: Iterated Safety
-- ============================================================

/-- A safe exec state never reaches a non-acceptable error after any number of steps. -/
theorem safe_run_no_unacceptable_error (state : ExecState)
    (hsafe : SafeExecState state) (e : RuntimeError) (hna : ¬e.isAcceptable) :
    ∀ n, Semantics.run n state ≠ .error e := by
  intro n
  induction n generalizing state with
  | zero =>
    intro h
    unfold Semantics.run at h
    -- run 0 = .error .outOfFuel, which is acceptable
    have heq : RuntimeError.outOfFuel = e := by injection h
    subst heq; exact hna (by simp [RuntimeError.isAcceptable])
  | succ n ih =>
    intro h
    unfold Semantics.run at h
    match state, hsafe with
    | .running m, hsafe =>
      exact ih (step (.running m)) (safe_step (.running m) hsafe) h
    | .halted _, _ =>
      exact absurd h (by intro h'; cases h')
    | .error _, hsafe =>
      exact SafeExecState.not_error hsafe e hna h

/-- A safe exec state remains danglingRef-free after any number of steps.
    Backward-compatible corollary of `safe_run_no_unacceptable_error`. -/
theorem safe_run_no_danglingRef (state : ExecState)
    (hsafe : SafeExecState state) :
    ∀ n loc, Semantics.run n state ≠ .error (.danglingRef loc) := by
  intro n loc
  exact safe_run_no_unacceptable_error state hsafe (.danglingRef loc)
    (by simp [RuntimeError.isAcceptable]) n

end LeanMove.Typing.TypeSoundness
