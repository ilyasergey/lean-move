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

A well-typed MoveLight function never produces a `danglingRef` error at runtime.

Two versions are provided:
- `type_soundness`: relational version using `typecheck_fun` and propositional assumptions
- `type_soundness_dec`: fully decidable version using `check_fun_dec`, `checkFunEnv`,
  and `SoundnessAssumptions.checkDecidable`
-/

namespace LeanMove.Typing.TypeSoundness

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Typing
open LeanMove.Semantics
open AssocMap

/-- The main type soundness theorem: a well-typed function never produces
    a danglingRef error at runtime, regardless of fuel. -/
theorem type_soundness (f : FunDef) (lenv : LabelEnv) (funEnv : AssocMap Id FunDef)
    (args : List Value) (heap : Heap)
    (htyped : typecheck_fun f lenv)
    (hfunEnv : ∀ fname fdef, lookup funEnv fname = some fdef → ∃ lenv', typecheck_fun fdef lenv')
    (ha : SoundnessAssumptions f lenv heap) :
    ∀ n loc, Semantics.run n (initState f funEnv args heap) ≠ .error (.danglingRef loc) :=
  safe_run_no_danglingRef (initState f funEnv args heap)
    (initState_safe f lenv funEnv args heap htyped hfunEnv ha)

/-- Decidable type soundness theorem: all hypotheses are decidable boolean checks.
    Uses `check_fun_dec` for the main function, `checkFunEnv` for the function
    environment, and `SoundnessAssumptions.checkDecidable` for remaining prerequisites. -/
theorem type_soundness_dec (f : FunDef) (lenvDec : LabelEnvDec)
    (funEnv : AssocMap Id FunDef) (fte : FunTypingEnv)
    (args : List Value) (heap : Heap)
    (hcheck : check_fun_dec f lenvDec = true)
    (hfunEnv : checkFunEnv funEnv fte = true)
    (hdec : SoundnessAssumptions.checkDecidable f lenvDec.toLabelEnv heap = true) :
    ∀ n loc, Semantics.run n (initState f funEnv args heap) ≠ .error (.danglingRef loc) :=
  type_soundness f lenvDec.toLabelEnv funEnv args heap
    (check_fun_dec_sound f lenvDec hcheck)
    (checkFunEnv_sound funEnv fte hfunEnv)
    (SoundnessAssumptions.of_check f lenvDec.toLabelEnv heap
      (check_fun_dec_lenv_wf f lenvDec hcheck)
      (check_fun_dec_lenv_non_member_from f lenvDec hcheck)
      (check_fun_dec_lenv_non_member_to f lenvDec hcheck)
      (check_fun_dec_lenv_self_loop f lenvDec hcheck)
      hdec)

end LeanMove.Typing.TypeSoundness
