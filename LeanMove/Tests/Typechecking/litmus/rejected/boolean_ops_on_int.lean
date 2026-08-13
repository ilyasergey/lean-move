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
import LeanMove.Typing.Algorithmic.DecidableTypeEnv
import LeanMove.Lang.Macros

/-!
# Boolean Operators Applied to Integers — Rejected

Move's `And`, `Or` and `Not` are *boolean* instructions: the integer
conjunction/disjunction are the separate `BitAnd`/`BitOr` opcodes, which
MoveLight does not model. Applying the boolean operators to `u64` operands
is therefore a type error.

Rejected by `unop_type`/`binop_type`, both of which are defined only at
`tbool`:

- `unop_type .not .u64 = none`
- `binop_type .and .u64 .u64 = none`
- `binop_type .or .u64 .u64 = none`

```
fn_not_on_int(a: u64): bool {
label b0:
    s0 = copy(a);
    s1 = !s0;              // REJECTED: unop_type .not .u64 = none
    return s1;
}

fn_and_on_int(a: u64, b: u64): u64 {
label b0:
    s0 = copy(a); s1 = copy(b);
    s2 = s0 && s1;         // REJECTED: binop_type .and .u64 .u64 = none
    return s2;
}
```
-/

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Typing
open AssocMap

namespace LeanMove.Tests.Litmus.BooleanOpsOnInt

-- Variables
def var_a : Var := ⟨"a"⟩
def var_b : Var := ⟨"b"⟩

-- Sites
def s0 : Site := .site 0
def s1 : Site := .site 1
def s2 : Site := .site 2

/-
  `Not` applied to a u64 — should be rejected.
-/
def fn_not_on_int : FunDef := {
  params := [(var_a, .basic .u64)]
  returnType := [⟨.tbool, none⟩]
  locals := []
  blocks := [
    { label := "b0"
      body :=
        (letsite s0 ← copy var_a) ;;
        (letsite s1 ← unop(.not, s0)) ;;   -- REJECTED
        ret [s1]
    }
  ]
}

def fn_not_on_int_lenv := mkLabelEnv fn_not_on_int

#guard !check_fun fn_not_on_int fn_not_on_int_lenv AssocMap.empty

/-
  `And` applied to two u64s — should be rejected.
-/
def fn_and_on_int : FunDef := {
  params := [(var_a, .basic .u64), (var_b, .basic .u64)]
  returnType := [⟨.u64, none⟩]
  locals := []
  blocks := [
    { label := "b0"
      body :=
        (letsite s0 ← copy var_a) ;;
        (letsite s1 ← copy var_b) ;;
        (letsite s2 ← binop(.and, s0, s1)) ;;   -- REJECTED
        ret [s2]
    }
  ]
}

def fn_and_on_int_lenv := mkLabelEnv fn_and_on_int

#guard !check_fun fn_and_on_int fn_and_on_int_lenv AssocMap.empty

/-
  `Or` applied to two u64s — should be rejected.
-/
def fn_or_on_int : FunDef := {
  params := [(var_a, .basic .u64), (var_b, .basic .u64)]
  returnType := [⟨.u64, none⟩]
  locals := []
  blocks := [
    { label := "b0"
      body :=
        (letsite s0 ← copy var_a) ;;
        (letsite s1 ← copy var_b) ;;
        (letsite s2 ← binop(.or, s0, s1)) ;;    -- REJECTED
        ret [s2]
    }
  ]
}

def fn_or_on_int_lenv := mkLabelEnv fn_or_on_int

#guard !check_fun fn_or_on_int fn_or_on_int_lenv AssocMap.empty

end LeanMove.Tests.Litmus.BooleanOpsOnInt
