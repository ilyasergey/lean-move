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
# Ordering Comparisons Applied to Booleans — Rejected

`Lt`, `Gt`, `Le` and `Ge` are *integer* instructions in the Move bytecode: they
are defined only at `u64`. Only `Eq`/`Neq` are polymorphic (see
`comparison_ops_ok.lean`, which accepts `Neq` at `bool`).

Rejected by `binop_type`, which has no `tbool` row for any ordering comparison:

- `binop_type .lt .tbool .tbool = none`
- `binop_type .gt .tbool .tbool = none`
- `binop_type .le .tbool .tbool = none`
- `binop_type .ge .tbool .tbool = none`

```
fn_gt_on_bool(a: bool, b: bool): bool {
label b0:
    s0 = copy(a); s1 = copy(b);
    s2 = s0 > s1;          // REJECTED: binop_type .gt .tbool .tbool = none
    return s2;
}
```

Mixing the operand types is rejected for the same reason — there is no
`(.ge, .u64, .tbool)` row either.
-/

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Typing
open AssocMap

namespace LeanMove.Tests.Litmus.ComparisonOpsOnBool

-- Variables
def var_a : Var := ⟨"a"⟩
def var_b : Var := ⟨"b"⟩

-- Sites
def s (n : Nat) : Site := .site n

/-- `fn(a: bool, b: bool): bool { return a op b; }` for an ordering comparison. -/
def cmp_on_bool (op : Binop) : FunDef := {
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

def fn_lt_on_bool : FunDef := cmp_on_bool .lt
def fn_gt_on_bool : FunDef := cmp_on_bool .gt
def fn_le_on_bool : FunDef := cmp_on_bool .le
def fn_ge_on_bool : FunDef := cmp_on_bool .ge

#guard !check_fun fn_lt_on_bool (mkLabelEnv fn_lt_on_bool) AssocMap.empty
#guard !check_fun fn_gt_on_bool (mkLabelEnv fn_gt_on_bool) AssocMap.empty
#guard !check_fun fn_le_on_bool (mkLabelEnv fn_le_on_bool) AssocMap.empty
#guard !check_fun fn_ge_on_bool (mkLabelEnv fn_ge_on_bool) AssocMap.empty

-- `Neq` at bool, by contrast, is accepted (see comparison_ops_ok.lean).
#guard check_fun (cmp_on_bool .neq) (mkLabelEnv (cmp_on_bool .neq)) AssocMap.empty

/-
  Mixed operand types: `u64 >= bool` — also rejected.
-/
def fn_ge_mixed : FunDef := {
  params := [(var_a, .basic .u64), (var_b, .basic .tbool)]
  returnType := [⟨.tbool, none⟩]
  locals := []
  blocks := [
    { label := "b0"
      body :=
        (letsite (s 0) ← copy var_a) ;;
        (letsite (s 1) ← copy var_b) ;;
        (letsite (s 2) ← binop(.ge, (s 0), (s 1))) ;;   -- REJECTED
        ret [(s 2)]
    }
  ]
}

#guard !check_fun fn_ge_mixed (mkLabelEnv fn_ge_mixed) AssocMap.empty

end LeanMove.Tests.Litmus.ComparisonOpsOnBool
