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
# Comparison Operators — Accepted

Exercises the Move bytecode comparison instructions `Neq`, `Gt`, `Le` and `Ge`
alongside the pre-existing `Eq` and `Lt`.

`Lt`, `Gt`, `Le` and `Ge` are integer instructions: they are typed at `u64` and
produce a `bool`. `Eq` and `Neq`, by contrast, are defined at every comparable
type, so `Neq` also applies to two `bool`s.

## Test 1: `fn_comparisons`
All four new comparisons in one block, combined with `And`/`Or`. As with any
`binop`, each comparison **consumes** its operand sites, so every one of them
needs freshly copied operands.

```
fn_comparisons(a: u64, b: u64): bool {
label b0:
    s0 = copy(a); s1 = copy(b); s2  = s0 != s1;    // Neq
    s3 = copy(a); s4 = copy(b); s5  = s3 > s4;     // Gt
    s6 = s2 && s5;
    s7 = copy(a); s8 = copy(b); s9  = s7 <= s8;    // Le
    s10 = s6 || s9;
    s11 = copy(a); s12 = copy(b); s13 = s11 >= s12; // Ge
    s14 = s10 && s13;
    return s14;
}
```

## Test 2: `fn_neq_bool`
`Neq` at `bool`, mirroring `Eq`.

## Test 3: `fn_ge_branch`
A comparison in branch position — the `Ge` result must be a `bool` for the
branch to typecheck. This is the shape that the translator used to mistranslate:
`>=` became `add`, yielding a `u64` where the branch demanded a `bool`.
-/

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Typing
open AssocMap

namespace LeanMove.Tests.Litmus.ComparisonOpsOk

-- Variables
def var_a : Var := ⟨"a"⟩
def var_b : Var := ⟨"b"⟩

-- Sites
def s (n : Nat) : Site := .site n

-- ═══════════════════════════════════════════════════════
-- Test 1: fn_comparisons — Neq, Gt, Le and Ge in one block
-- ═══════════════════════════════════════════════════════

def fn_comparisons : FunDef := {
  params := [(var_a, .basic .u64), (var_b, .basic .u64)]
  returnType := [⟨.tbool, none⟩]
  locals := []
  blocks := [
    { label := "b0"
      body :=
        (letsite (s 0) ← copy var_a) ;;
        (letsite (s 1) ← copy var_b) ;;
        (letsite (s 2) ← binop(.neq, (s 0), (s 1))) ;;    -- Neq
        (letsite (s 3) ← copy var_a) ;;
        (letsite (s 4) ← copy var_b) ;;
        (letsite (s 5) ← binop(.gt, (s 3), (s 4))) ;;     -- Gt
        (letsite (s 6) ← binop(.and, (s 2), (s 5))) ;;
        (letsite (s 7) ← copy var_a) ;;
        (letsite (s 8) ← copy var_b) ;;
        (letsite (s 9) ← binop(.le, (s 7), (s 8))) ;;     -- Le
        (letsite (s 10) ← binop(.or, (s 6), (s 9))) ;;
        (letsite (s 11) ← copy var_a) ;;
        (letsite (s 12) ← copy var_b) ;;
        (letsite (s 13) ← binop(.ge, (s 11), (s 12))) ;;  -- Ge
        (letsite (s 14) ← binop(.and, (s 10), (s 13))) ;;
        ret [(s 14)]
    }
  ]
}

def fn_comparisons_lenvDec := mkLabelEnvDec fn_comparisons

theorem fn_comparisons_check :
    check_fun_dec fn_comparisons fn_comparisons_lenvDec = true := by rfl

theorem fn_comparisons_welltyped :
    ∃ lenv, typecheck_fun fn_comparisons lenv AssocMap.empty :=
  ⟨_, check_fun_dec_sound _ _ _ fn_comparisons_check⟩

-- ═══════════════════════════════════════════════════════
-- Test 2: fn_neq_bool — Neq at bool
-- ═══════════════════════════════════════════════════════

def fn_neq_bool : FunDef := {
  params := [(var_a, .basic .tbool), (var_b, .basic .tbool)]
  returnType := [⟨.tbool, none⟩]
  locals := []
  blocks := [
    { label := "b0"
      body :=
        (letsite (s 0) ← copy var_a) ;;
        (letsite (s 1) ← copy var_b) ;;
        (letsite (s 2) ← binop(.neq, (s 0), (s 1))) ;;
        ret [(s 2)]
    }
  ]
}

def fn_neq_bool_lenvDec := mkLabelEnvDec fn_neq_bool

theorem fn_neq_bool_check :
    check_fun_dec fn_neq_bool fn_neq_bool_lenvDec = true := by rfl

theorem fn_neq_bool_welltyped :
    ∃ lenv, typecheck_fun fn_neq_bool lenv AssocMap.empty :=
  ⟨_, check_fun_dec_sound _ _ _ fn_neq_bool_check⟩

-- ═══════════════════════════════════════════════════════
-- Test 3: fn_ge_branch — a Ge result in branch position
-- ═══════════════════════════════════════════════════════

def fn_ge_branch : FunDef := {
  params := [(var_a, .basic .u64), (var_b, .basic .u64)]
  returnType := [⟨.u64, none⟩]
  locals := []
  blocks := [
    { label := "b0"
      body :=
        (letsite (s 0) ← copy var_a) ;;
        (letsite (s 1) ← copy var_b) ;;
        (letsite (s 2) ← binop(.ge, (s 0), (s 1))) ;;
        branch (s 2) "b2" "b1"
    },
    { label := "b1"
      body :=
        (letsite (s 3) ← copy var_b) ;;
        ret [(s 3)]
    },
    { label := "b2"
      body :=
        (letsite (s 4) ← copy var_a) ;;
        ret [(s 4)]
    }
  ]
}

-- Multi-block: every block needs a label-env entry, not just the entry block.
def fn_ge_branch_lenvDec := mkLabelEnvDecAll fn_ge_branch

theorem fn_ge_branch_check :
    check_fun_dec fn_ge_branch fn_ge_branch_lenvDec = true := by rfl

theorem fn_ge_branch_welltyped :
    ∃ lenv, typecheck_fun fn_ge_branch lenv AssocMap.empty :=
  ⟨_, check_fun_dec_sound _ _ _ fn_ge_branch_check⟩

end LeanMove.Tests.Litmus.ComparisonOpsOk
