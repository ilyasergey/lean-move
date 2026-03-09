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
import LeanMove.Typing.Algorithmic.AlgorithmicTypeChecking
import LeanMove.Typing.Algorithmic.AlgorithmicTypingSoundness
import LeanMove.Lang.Macros

/-!
# Use After Move — Runtime Litmus Test

Demonstrates that Move's linear ownership system prevents use-after-move errors.
After `move(x)` consumes variable `x`, any subsequent `copy(x)` is rejected by
the type checker and produces `uninitializedVar` at runtime.

Original Move-like pseudocode:
```
foo() {
    let x: u64;
    let y: u64;
label b0:
    x = 42;
    y = move(x);     // x consumed
    _ = copy(x);     // ERROR: use after move
    return;
}
```
-/

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Typing
open AssocMap
open Regex

namespace LeanMove.Tests.UseAfterMove

-- Variables
def var_x : Var := ⟨"x"⟩
def var_y : Var := ⟨"y"⟩

-- Sites
def s0 : Site := .site 0   -- integer literal 42
def s1 : Site := .site 1   -- move(x)
def s2 : Site := .site 2   -- copy(x) — ERROR

def foo : FunDef := {
  params := []
  returnType := []
  locals := [
    { name := var_x, type := .basic .u64 },
    { name := var_y, type := .basic .u64 }
  ]
  blocks := [
    { label := "b0"
      body :=
        -- x = 42
        (letsite s0 ← #42) ;;
        (var_x ::= s0) ;;
        -- y = move(x)  — consumes x
        (letsite s1 ← move var_x) ;;
        (var_y ::= s1) ;;
        -- copy(x) — ERROR: x was moved, var_x is None
        (letsite s2 ← copy var_x) ;;
        (var_y ::= s2) ;;
        ret []
    }
  ]
}

/-!
## Why this is rejected by the type checker

After `move(x)`, the variable `x` becomes invalid in the VarEnv. The subsequent
`copy(x)` requires `x` to be valid, so the algorithmic checker rejects the program.

## Why this fails at runtime

After `move(x)`, the interpreter sets `varStore[x] = None`. When `copy(x)` executes,
`readVar` reads `varStore[x]` → `None` → produces `uninitializedVar ⟨"x"⟩`.
-/

-- -----------------------------------------------------
-- -           Algorithmic Type Checking Tests        --
-- -----------------------------------------------------

def foo_lenv := mkLabelEnv foo

#eval check_fun foo foo_lenv AssocMap.empty

-- Test: algorithmic checker rejects foo
#guard !check_fun foo foo_lenv AssocMap.empty

end LeanMove.Tests.UseAfterMove
