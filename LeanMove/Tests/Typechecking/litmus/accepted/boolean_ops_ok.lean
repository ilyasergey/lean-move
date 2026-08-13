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
# Boolean Operators — Accepted

Exercises the three Move bytecode boolean instructions, `And`, `Or` and `Not`,
which MoveLight models as `Binop.and`, `Binop.or` and `Unop.not`.

Booleans are introduced by the comparison operators (`==`, `<`), since
MoveLight has no boolean literal expression.

## Test 1: `fn_and_or_not`
Threads all three operators through a single block. Note that `binop` and
`unop` **consume** their operand sites, so each comparison needs freshly
copied operands.

```
fn_and_or_not(a: u64, b: u64): bool {
label b0:
    s0 = copy(a); s1 = copy(b); s2 = s0 == s1;   // bool
    s3 = copy(a); s4 = copy(b); s5 = s3 < s4;    // bool
    s6 = s2 && s5;                                // And
    s7 = !s6;                                     // Not
    s8 = copy(a); s9 = copy(b); s10 = s8 == s9;  // bool
    s11 = s7 || s10;                              // Or
    return s11;
}
```

## Test 2: `fn_double_negation`
`!!(a == b)`, checking that `Unop.not` composes with itself.
-/

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Typing
open AssocMap

namespace LeanMove.Tests.Litmus.BooleanOpsOk

-- Variables
def var_a : Var := ⟨"a"⟩
def var_b : Var := ⟨"b"⟩

-- Sites
def s0 : Site := .site 0
def s1 : Site := .site 1
def s2 : Site := .site 2
def s3 : Site := .site 3
def s4 : Site := .site 4
def s5 : Site := .site 5
def s6 : Site := .site 6
def s7 : Site := .site 7
def s8 : Site := .site 8
def s9 : Site := .site 9
def s10 : Site := .site 10
def s11 : Site := .site 11

-- ═══════════════════════════════════════════════════════
-- Test 1: fn_and_or_not — And, Or and Not in one block
-- ═══════════════════════════════════════════════════════

def fn_and_or_not : FunDef := {
  params := [(var_a, .basic .u64), (var_b, .basic .u64)]
  returnType := [⟨.tbool, none⟩]
  locals := []
  blocks := [
    { label := "b0"
      body :=
        (letsite s0 ← copy var_a) ;;
        (letsite s1 ← copy var_b) ;;
        (letsite s2 ← binop(.eq, s0, s1)) ;;      -- s2 : bool
        (letsite s3 ← copy var_a) ;;
        (letsite s4 ← copy var_b) ;;
        (letsite s5 ← binop(.lt, s3, s4)) ;;      -- s5 : bool
        (letsite s6 ← binop(.and, s2, s5)) ;;     -- And
        (letsite s7 ← unop(.not, s6)) ;;          -- Not
        (letsite s8 ← copy var_a) ;;
        (letsite s9 ← copy var_b) ;;
        (letsite s10 ← binop(.eq, s8, s9)) ;;     -- s10 : bool
        (letsite s11 ← binop(.or, s7, s10)) ;;    -- Or
        ret [s11]
    }
  ]
}

def fn_and_or_not_lenvDec := mkLabelEnvDec fn_and_or_not

theorem fn_and_or_not_check :
    check_fun_dec fn_and_or_not fn_and_or_not_lenvDec = true := by rfl

theorem fn_and_or_not_welltyped : ∃ lenv, typecheck_fun fn_and_or_not lenv AssocMap.empty :=
  ⟨_, check_fun_dec_sound _ _ _ fn_and_or_not_check⟩

-- ═══════════════════════════════════════════════════════
-- Test 2: fn_double_negation — !!(a == b)
-- ═══════════════════════════════════════════════════════

def fn_double_negation : FunDef := {
  params := [(var_a, .basic .u64), (var_b, .basic .u64)]
  returnType := [⟨.tbool, none⟩]
  locals := []
  blocks := [
    { label := "b0"
      body :=
        (letsite s0 ← copy var_a) ;;
        (letsite s1 ← copy var_b) ;;
        (letsite s2 ← binop(.eq, s0, s1)) ;;
        (letsite s3 ← unop(.not, s2)) ;;
        (letsite s4 ← unop(.not, s3)) ;;
        ret [s4]
    }
  ]
}

def fn_double_negation_lenvDec := mkLabelEnvDec fn_double_negation

theorem fn_double_negation_check :
    check_fun_dec fn_double_negation fn_double_negation_lenvDec = true := by rfl

theorem fn_double_negation_welltyped :
    ∃ lenv, typecheck_fun fn_double_negation lenv AssocMap.empty :=
  ⟨_, check_fun_dec_sound _ _ _ fn_double_negation_check⟩

end LeanMove.Tests.Litmus.BooleanOpsOk
