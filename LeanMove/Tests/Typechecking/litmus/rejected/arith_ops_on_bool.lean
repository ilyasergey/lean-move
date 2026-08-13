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
# Arithmetic Applied to Booleans — Rejected

`Add`, `Sub`, `Mul`, `Div` and `Mod` are *integer* instructions: `binop_type`
gives them a `u64` row and nothing else. Move has no `bool` arithmetic — the
boolean opcodes are `And`/`Or`/`Not` (see `boolean_ops_ok.lean`).

```
arith_on_bool(a: bool, b: bool): bool {
label b0:
    s0 = copy(a); s1 = copy(b);
    s2 = s0 * s1;          // REJECTED: binop_type .mul .tbool .tbool = none
    return s2;
}
```

The result type is `bool` here only so that the *sole* reason for rejection is
the operand types; a `u64` return would additionally mismatch.
-/

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Typing
open AssocMap

namespace LeanMove.Tests.Litmus.ArithOpsOnBool

-- Variables
def var_a : Var := ⟨"a"⟩
def var_b : Var := ⟨"b"⟩

-- Sites
def s (n : Nat) : Site := .site n

/-- `fn(a: bool, b: bool): bool { return a op b; }` for an arithmetic `op`. -/
def arith_on_bool (op : Binop) : FunDef := {
  params := [(var_a, .basic .tbool), (var_b, .basic .tbool)]
  returnType := [⟨.tbool, none⟩]
  locals := []
  blocks := [
    { label := "b0"
      body :=
        (letsite (s 0) ← copy var_a) ;;
        (letsite (s 1) ← copy var_b) ;;
        (letsite (s 2) ← binop(op, (s 0), (s 1))) ;;   -- REJECTED
        ret [(s 2)]
    }
  ]
}

def fn_mul_on_bool : FunDef := arith_on_bool .mul

#guard !check_fun fn_mul_on_bool (mkLabelEnv fn_mul_on_bool) AssocMap.empty

-- The other integer instructions are rejected at `bool` for the same reason.
#guard !check_fun (arith_on_bool .add) (mkLabelEnv (arith_on_bool .add)) AssocMap.empty
#guard !check_fun (arith_on_bool .sub) (mkLabelEnv (arith_on_bool .sub)) AssocMap.empty
#guard !check_fun (arith_on_bool .div) (mkLabelEnv (arith_on_bool .div)) AssocMap.empty
#guard !check_fun (arith_on_bool .mod) (mkLabelEnv (arith_on_bool .mod)) AssocMap.empty

/-
  Mixed operand types: `u64 * bool` — also rejected, there is no
  `(.mul, .u64, .tbool)` row.
-/
def fn_mul_mixed : FunDef := {
  params := [(var_a, .basic .u64), (var_b, .basic .tbool)]
  returnType := [⟨.u64, none⟩]
  locals := []
  blocks := [
    { label := "b0"
      body :=
        (letsite (s 0) ← copy var_a) ;;
        (letsite (s 1) ← copy var_b) ;;
        (letsite (s 2) ← binop(.mul, (s 0), (s 1))) ;;   -- REJECTED
        ret [(s 2)]
    }
  ]
}

#guard !check_fun fn_mul_mixed (mkLabelEnv fn_mul_mixed) AssocMap.empty

end LeanMove.Tests.Litmus.ArithOpsOnBool
