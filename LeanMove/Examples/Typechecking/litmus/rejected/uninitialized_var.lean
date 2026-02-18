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
import LeanMove.Typing.Algorithmic.AlgorithmicTypingSoundness
import LeanMove.Lang.Macros

/-!
# Uninitialized Variable — Runtime Litmus Test

Demonstrates that the type checker prevents reading uninitialized variables.
Local variables start as invalid; using them before assignment is rejected by
the type checker and produces `uninitializedVar` at runtime.

Original Move-like pseudocode:
```
foo() {
    let x: u64;
    let y: u64;
label b0:
    y = copy(x);     // ERROR: x never assigned
    return;
}
```
-/

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Typing
open AssocMap
open Regex

namespace LeanMove.Examples.UninitializedVar

-- Variables
def var_x : Var := ⟨"x"⟩
def var_y : Var := ⟨"y"⟩

-- Sites
def s0 : Site := .site 0   -- copy(x) — ERROR

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
        -- y = copy(x) — ERROR: x never assigned
        (letsite s0 ← copy var_x) ;;
        (var_y ::= s0) ;;
        Stmt.ret []
    }
  ]
}

/-!
## Why this is rejected by the type checker

Local variables start as `.invalid` in the VarEnv. The `copy(x)` requires `x` to
be valid (assigned), so the algorithmic checker rejects the program.

## Why this fails at runtime

Local variables start as `None` in the VarStore. When `copy(x)` executes,
`readVar` reads `varStore[x]` → `None` → produces `uninitializedVar ⟨"x"⟩`.
-/

-- -----------------------------------------------------
-- -           Algorithmic Type Checking Tests        --
-- -----------------------------------------------------

def foo_initEnv : TypeEnv := {
  siteEnv := AssocMap.empty
  varEnv := init_fun_varEnv foo
  pathEnv := PathEnv.init
  funEnv := AssocMap.empty
}

def foo_lenv : LabelEnv :=
  AssocMap.insert AssocMap.empty "b0" foo_initEnv

#eval check_fun foo foo_lenv

#guard !check_fun foo foo_lenv

end LeanMove.Examples.UninitializedVar
