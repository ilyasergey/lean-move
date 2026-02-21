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
import LeanMove.Typing.Algorithmic.DecidableTypeEnv
import LeanMove.Typing.Algorithmic.AlgorithmicTypingSoundness
import LeanMove.Lang.Macros

/-!
# Return Parameter Reference Tests

Tests demonstrating that the new `ret` rule correctly accepts functions
that return references derived from parameters (not locals).

## Test 1: `fn_return_basic`
Returns a basic u64 value. Trivially passes all return conditions
because no references are involved.

## Test 2: `fn_return_param_ref`
Takes `r: &mut u64` and returns `move(r)` as `&mut u64`.
Passes because:
- **types_conform**: the returned site type matches `⟨.u64, some true⟩`
- **no local borrowing**: `r`'s aref is `.varRef var_r`, which is a parameter ref.
  The pathEnv has no path from `.root` to `.varRef var_r`.
- **writability**: `.varRef var_r` has only trivial self-loops in the pathEnv
  (no outbound edges to other arefs)
- **no aliasing**: only one returned ref, so no aliasing possible

## Test 3: `fn_return_two_independent_mut_refs`
Takes `r1: &mut u64` and `r2: &mut u64`, returns both.
Passes because:
- Both are parameter refs with no root paths
- Each has only trivial self-loops (independent parameters)
- No aliasing: `G(varRef r1, varRef r2) = ∅` and vice versa
-/

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Typing
open AssocMap

namespace LeanMove.Examples.Litmus.ReturnParamRefOk

-- Variables
def var_a : Var := ⟨"a"⟩
def var_r : Var := ⟨"r"⟩
def var_r1 : Var := ⟨"r1"⟩
def var_r2 : Var := ⟨"r2"⟩

-- Sites
def s0 : Site := .site 0
def s1 : Site := .site 1
def s2 : Site := .site 2
def s3 : Site := .site 3

-- ═══════════════════════════════════════════════════════
-- Test 1: fn_return_basic — returns a basic u64
-- ═══════════════════════════════════════════════════════

/-
  fn_return_basic(a: u64): u64 {
  label b0:
      return copy(a);
  }
-/
def fn_return_basic : FunDef := {
  params := [(var_a, .basic .u64)]
  returnType := [⟨.u64, none⟩]
  locals := []
  blocks := [
    { label := "b0"
      body :=
        (letsite s0 ← copy var_a) ;;
        ret [s0]
    }
  ]
}

def fn_return_basic_lenvDec : LabelEnvDec :=
  insert empty "b0"
    { siteEnv := empty, varEnv := init_fun_varEnv fn_return_basic,
      pathEnv := init_fun_pathEnvDec fn_return_basic.params, funEnv := empty }

theorem fn_return_basic_check :
    check_fun_dec fn_return_basic fn_return_basic_lenvDec = true := by rfl

theorem fn_return_basic_welltyped : ∃ lenv, typecheck_fun fn_return_basic lenv :=
  ⟨_, check_fun_dec_sound _ _ fn_return_basic_check⟩

-- ═══════════════════════════════════════════════════════
-- Test 2: fn_return_param_ref — returns a moved param ref
-- ═══════════════════════════════════════════════════════

/-
  fn_return_param_ref(r: &mut u64): &mut u64 {
  label b0:
      return move(r);
  }
-/
def fn_return_param_ref : FunDef := {
  params := [(var_r, .ref .u64 (.varRef var_r) .siteBorrowMut)]
  returnType := [⟨.u64, some true⟩]
  locals := []
  blocks := [
    { label := "b0"
      body :=
        (letsite s0 ← move var_r) ;;
        ret [s0]
    }
  ]
}

def fn_return_param_ref_lenvDec : LabelEnvDec :=
  insert empty "b0"
    { siteEnv := empty, varEnv := init_fun_varEnv fn_return_param_ref,
      pathEnv := init_fun_pathEnvDec fn_return_param_ref.params, funEnv := empty }

theorem fn_return_param_ref_check :
    check_fun_dec fn_return_param_ref fn_return_param_ref_lenvDec = true := by rfl

theorem fn_return_param_ref_welltyped : ∃ lenv, typecheck_fun fn_return_param_ref lenv :=
  ⟨_, check_fun_dec_sound _ _ fn_return_param_ref_check⟩

-- ═══════════════════════════════════════════════════════
-- Test 3: fn_return_two_independent_mut_refs
-- ═══════════════════════════════════════════════════════

/-
  fn_return_two(r1: &mut u64, r2: &mut u64): (&mut u64, &mut u64) {
  label b0:
      return (move(r1), move(r2));
  }
-/
def fn_return_two : FunDef := {
  params := [(var_r1, .ref .u64 (.varRef var_r1) .siteBorrowMut),
             (var_r2, .ref .u64 (.varRef var_r2) .siteBorrowMut)]
  returnType := [⟨.u64, some true⟩, ⟨.u64, some true⟩]
  locals := []
  blocks := [
    { label := "b0"
      body :=
        (letsite s0 ← move var_r1) ;;
        (letsite s1 ← move var_r2) ;;
        ret [s0, s1]
    }
  ]
}

def fn_return_two_lenvDec : LabelEnvDec :=
  insert empty "b0"
    { siteEnv := empty, varEnv := init_fun_varEnv fn_return_two,
      pathEnv := init_fun_pathEnvDec fn_return_two.params, funEnv := empty }

theorem fn_return_two_check :
    check_fun_dec fn_return_two fn_return_two_lenvDec = true := by rfl

theorem fn_return_two_welltyped : ∃ lenv, typecheck_fun fn_return_two lenv :=
  ⟨_, check_fun_dec_sound _ _ fn_return_two_check⟩

end LeanMove.Examples.Litmus.ReturnParamRefOk
