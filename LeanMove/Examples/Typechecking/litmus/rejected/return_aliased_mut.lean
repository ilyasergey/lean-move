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


import LeanMove.Lang.MoveLight
import LeanMove.Typing.TypeChecking
import LeanMove.Typing.Algorithmic.TypeCheckingAlgorithmic
import LeanMove.Typing.Algorithmic.DecidableTypeEnv
import LeanMove.Lang.Macros

/-!
# Return Aliased Mutable Refs — Rejected

This function creates two mutable references that alias each other and
attempts to return both. It should be rejected by condition 4 of the
`ret` rule: "no aliasing of mutable returns".

```
fn_return_aliased(r: &mut u64): (&mut u64, &mut u64) {
label b0:
    return (copy(r), move(r));   // REJECTED: both refs alias the same aref
}
```

After `copy(r)` and `move(r)`, both returned sites hold refs to the same
underlying aref (`varRef r`). The no-aliasing condition checks:
  G(r₂, r₁) = ∅ for each pair where r₁ is a mutable return.
Since both refs point to `varRef r`, the self-loop gives G(varRef r, varRef r) = {ε} ≠ ∅.
-/

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Typing
open AssocMap

namespace LeanMove.Examples.Litmus.ReturnAliasedMut

-- Variables
def var_r : Var := ⟨"r"⟩

-- Sites
def s0 : Site := .site 0
def s1 : Site := .site 1

/-
  fn_return_aliased(r: &mut u64): (&mut u64, &mut u64)
  Returns two aliased mutable refs — should be rejected.
-/
def fn_return_aliased : FunDef := {
  params := [(var_r, .ref .u64 (.varRef var_r) .siteBorrowMut)]
  returnType := [⟨.u64, some true⟩, ⟨.u64, some true⟩]
  locals := []
  blocks := [
    { label := "b0"
      body :=
        (letsite s0 ← copy var_r) ;;
        (letsite s1 ← move var_r) ;;
        ret [s0, s1]
    }
  ]
}

def fn_return_aliased_initEnv : TypeEnv := {
  siteEnv := empty
  varEnv := init_fun_varEnv fn_return_aliased
  pathEnv := (init_fun_pathEnvDec fn_return_aliased.params).toPathEnv
  funEnv := empty
}

def fn_return_aliased_lenv : LabelEnv :=
  insert empty "b0" fn_return_aliased_initEnv

-- The algorithmic checker rejects this
#guard !check_fun fn_return_aliased fn_return_aliased_lenv

end LeanMove.Examples.Litmus.ReturnAliasedMut
