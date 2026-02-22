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
# Unpack Non-Record — Runtime Litmus Test

Demonstrates that the type checker prevents unpacking a non-record value.
Applying `unpack` to an integer site is rejected by the type checker and produces
`typeMismatch` at runtime.

Original Move-like pseudocode:
```
foo() {
    let x: u64;
    let y: u64;
label b0:
    x = 42;
    S { f: y } = copy(x);    // ERROR: x is u64, not a record
    return;
}
```
-/

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Typing
open AssocMap
open Regex

namespace LeanMove.Tests.UnpackNonRecord

-- Fields
def field_f : Field := ⟨"f"⟩

-- Variables
def var_x : Var := ⟨"x"⟩
def var_y : Var := ⟨"y"⟩

-- Sites
def s0 : Site := .site 0   -- integer literal 42
def s1 : Site := .site 1   -- copy(x)
def s2 : Site := .site 2   -- unpack destination for field f

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
        -- S { f: y } = copy(x) — ERROR: x is u64, not a record
        (letsite s1 ← copy var_x) ;;
        (unpack([(field_f, s2)], s1)) ;;
        (var_y ::= s2) ;;
        ret []
    }
  ]
}

/-!
## Why this is rejected by the type checker

The `unpack` statement requires its source site to have a record type (`.basic (.trecord ...)`).
Since `copy(x)` produces a site with type `.basic .u64`, the checker rejects the unpack.

## Why this fails at runtime

At runtime, `s1` holds `Value.int 42`. The `unpack` case in the step function
pattern-matches for `Value.record recFields` and falls through to the catch-all,
producing `typeMismatch "unpack on non-record"`.
-/

-- -----------------------------------------------------
-- -           Algorithmic Type Checking Tests        --
-- -----------------------------------------------------

def foo_lenv := mkLabelEnv foo

#eval check_fun foo foo_lenv

#guard !check_fun foo foo_lenv

end LeanMove.Tests.UnpackNonRecord
