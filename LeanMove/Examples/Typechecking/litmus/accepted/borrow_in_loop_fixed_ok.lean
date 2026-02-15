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

import Ssreflect.Lang

import LeanMove.Lang.MoveLight
import LeanMove.Typing.TypeChecking
import LeanMove.Typing.Algorithmic.DecidableTypeEnv
import LeanMove.Lang.Macros

/-!
# Fixed Version of borrow_in_loop

See: `borrow_in_loop.lean` for the broken version and detailed analysis of why it fails.

This file demonstrates the corrected version of the program. The original program
failed to type-check because it kept a borrow alive across a loop back-edge while
trying to reassign the borrowed variable.

The fix: **release the borrow before jumping back**.

## Original (broken) program from borrow_in_loop.lean:
```
foo() {
    let x: u64;
    let r: &u64;
    label l0:
    x = 0;
    r = &x;      // borrow created
    jump l0;     // borrow still live! Cannot reassign x on next iteration
}
```

## Fixed program (this file):
```
foo(x: u64) {
label l0:
    let s0 = &x;   // borrow x
    release(s0);   // release borrow immediately
    jump l0;       // x is no longer borrowed, loop can continue
}
```

Key differences:
1. We use `x` as a parameter (starting valid) since MoveLight lacks constant expressions
2. We release the borrow before jumping back, restoring the PathEnv to its initial state
3. The simplified version doesn't assign to a local variable `r` to avoid Aref mismatch issues

The proof uses algorithmic type checking soundness (`check_fun_dec_sound`) to
establish well-typedness, rather than manually constructing the relational proof.
-/

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Typing
open AssocMap
open Regex

namespace LeanMove.Examples.BorrowInLoopFixed

-- Variables
def var_x : Var := ⟨"x"⟩
def var_r : Var := ⟨"r"⟩

-- Sites (temporaries in A-normal form)
def s0 : Site := .site 0  -- &x
def s1 : Site := .site 1  -- move(r) for release

/-
  Function foo(x: u64) translated to MoveLight AST:

  Simplified version: borrow x, immediately release, then loop.
  We don't assign to r to avoid the Aref mismatch issue.

  foo(x: u64) {
  label l0:
      let s0 = &x;     // borrow x
      release(s0);     // immediately release
      jump l0;
  }
-/
def foo : FunDef := {
  params := [(var_x, .basic .u64)]  -- x is a parameter, starts valid
  returnType := .basic .tunit
  locals := []  -- no locals needed for this simplified version
  blocks := [
    { label := "l0"
      body :=
        (letsite s0 ← &var_x) ;;  -- let s0 = &x
        (release s0) ;;           -- release(s0)
        jump "l0"                 -- jump l0 (terminal)
    }
  ]
}

-- Decidable label environment for foo
def foo_lenvDec : LabelEnvDec :=
  insert empty "l0"
    { siteEnv := empty, varEnv := init_fun_varEnv foo,
      pathEnv := .init, funEnv := empty }

-- Test theorem: foo type checks algorithmically
theorem foo_check : check_fun_dec foo foo_lenvDec = true := by rfl

-- Theorem: foo is well-typed (via algorithmic soundness)
theorem foo_welltyped : ∃ lenv, typecheck_fun foo lenv :=
  ⟨_, check_fun_dec_sound _ _ foo_check⟩

end LeanMove.Examples.BorrowInLoopFixed
