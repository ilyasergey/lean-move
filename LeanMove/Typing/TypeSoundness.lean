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

import LeanMove.Typing.Soundness.SafeExec
import LeanMove.Typing.Soundness.InitState
import LeanMove.Typing.Algorithmic.DecidableTypeEnv

/-!
# Type Soundness: Main Theorems

A well-typed MoveLight function never produces a non-acceptable error at runtime.
The type system rules out 8 of 11 runtime error constructors:
`danglingRef`, `uninitializedVar`, `uninitializedSite`, `unknownLabel`,
`unknownFunction`, `arityMismatch`, `invalidFieldAccess`, `typeMismatch`.

Only 3 error constructors are acceptable (not preventable by the type system):
`divisionByZero` (runtime arithmetic), `outOfFuel` (bounded interpreter),
and `aborted` (well-typed `abort` statement or `skip` in callee).

Four versions are provided:
- `type_soundness`: general version ruling out all non-acceptable errors
- `type_soundness_no_danglingRef`: backward-compatible corollary for `danglingRef`
- `type_soundness_dec`: decidable version ruling out all non-acceptable errors
- `type_soundness_dec_no_danglingRef`: decidable backward-compatible corollary
-/

namespace LeanMove.Typing.TypeSoundness

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Typing
open LeanMove.Semantics
open AssocMap

-- ============================================================
-- General type soundness (relational version)
-- ============================================================

/-- The main type soundness theorem: a well-typed function never produces
    a non-acceptable error at runtime, regardless of fuel.
    Acceptable errors: `divisionByZero`, `outOfFuel`, `aborted`. -/
theorem type_soundness (f : FunDef) (lenv : LabelEnv) (enumEnv : EnumEnv)
    (funEnv : AssocMap Id FunDef)
    (args : List Value) (heap : Heap)
    (htyped : typecheck_fun f lenv enumEnv)
    (hfunEnv : ∀ fname fdef, lookup funEnv fname = some fdef → FunTypeSafe fdef funEnv enumEnv)
    (ha : SoundnessAssumptions f lenv enumEnv funEnv heap args)
    (e : RuntimeError) (hna : ¬e.isAcceptable) :
    ∀ n, Semantics.run n (initState f funEnv args (enumEnv := enumEnv) (heap := heap)) ≠ .error e :=
  safe_run_no_unacceptable_error (initState f funEnv args (enumEnv := enumEnv) (heap := heap))
    (initState_safe f lenv enumEnv funEnv args heap htyped hfunEnv ha) e hna

/-- Backward-compatible corollary: a well-typed function never produces
    a `danglingRef` error at runtime. -/
theorem type_soundness_no_danglingRef (f : FunDef) (lenv : LabelEnv) (enumEnv : EnumEnv)
    (funEnv : AssocMap Id FunDef) (args : List Value) (heap : Heap)
    (htyped : typecheck_fun f lenv enumEnv)
    (hfunEnv : ∀ fname fdef, lookup funEnv fname = some fdef → FunTypeSafe fdef funEnv enumEnv)
    (ha : SoundnessAssumptions f lenv enumEnv funEnv heap args) :
    ∀ n loc, Semantics.run n (initState f funEnv args (enumEnv := enumEnv) (heap := heap)) ≠ .error (.danglingRef loc) :=
  fun n loc => type_soundness f lenv enumEnv funEnv args heap htyped hfunEnv ha
    (.danglingRef loc) (by simp [RuntimeError.isAcceptable]) n

-- ============================================================
-- Decidable type soundness
-- ============================================================

/-- Decidable type soundness theorem: a single boolean check suffices to
    rule out all non-acceptable errors at runtime. -/
theorem type_soundness_dec (f : FunDef) (lenvDec : LabelEnvDec)
    (enumEnv : EnumEnv) (funEnv : AssocMap Id FunDef) (fte : FunTypingEnv)
    (args : List Value) (heap : Heap)
    (hdec : SoundnessAssumptions.checkDecidable f lenvDec enumEnv funEnv fte heap args = true)
    (e : RuntimeError) (hna : ¬e.isAcceptable) :
    ∀ n, Semantics.run n (initState f funEnv args (enumEnv := enumEnv) (heap := heap)) ≠ .error e := by
  have hcd := hdec
  simp only [SoundnessAssumptions.checkDecidable, Bool.and_eq_true] at hcd
  exact type_soundness f lenvDec.toLabelEnv enumEnv funEnv args heap
    (check_fun_dec_sound f lenvDec _ hcd.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1)
    (checkFunEnv_sound funEnv fte enumEnv hcd.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.1.2)
    (SoundnessAssumptions.of_check f lenvDec enumEnv funEnv fte heap args hdec)
    e hna

/-- Decidable backward-compatible corollary: a single boolean check suffices to
    rule out `danglingRef` errors at runtime. -/
theorem type_soundness_dec_no_danglingRef (f : FunDef) (lenvDec : LabelEnvDec)
    (enumEnv : EnumEnv) (funEnv : AssocMap Id FunDef) (fte : FunTypingEnv)
    (args : List Value) (heap : Heap)
    (hdec : SoundnessAssumptions.checkDecidable f lenvDec enumEnv funEnv fte heap args = true) :
    ∀ n loc, Semantics.run n (initState f funEnv args (enumEnv := enumEnv) (heap := heap)) ≠ .error (.danglingRef loc) :=
  fun n loc => type_soundness_dec f lenvDec enumEnv funEnv fte args heap hdec
    (.danglingRef loc) (by intro h; simp [RuntimeError.isAcceptable] at h) n

end LeanMove.Typing.TypeSoundness
