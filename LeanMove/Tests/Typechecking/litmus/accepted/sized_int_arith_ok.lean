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
# Sized Integer Arithmetic — Accepted

Arithmetic at a *single* width typechecks at every width, `u8` through `u256`.
Overflow, underflow and division by zero are **runtime** conditions, not static
ones: these functions all typecheck, and whether they abort depends on the
arguments they are run with. The companion runtime tests in
`Tests/Runtime/AllTests.lean` execute them at both in-range and out-of-range
arguments.

This is the same division of labour as division by zero: the borrow checker
does not, and cannot, prevent an arithmetic abort, so `arithmeticError` joins
`divisionByZero` among the accepted runtime errors.

```
fn_sub(a: u64, b: u64): u64 {
label b0:
    s0 = copy(a); s1 = copy(b);
    s2 = s0 - s1;          // aborts at run time when b > a
    return s2;
}

fn_add_u8(a: u8, b: u8): u8 {
label b0:
    s0 = copy(a); s1 = copy(b);
    s2 = s0 + s1;          // aborts at run time when a + b >= 256
    return s2;
}
```
-/

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Typing
open AssocMap

namespace LeanMove.Tests.Litmus.SizedIntArithOk

-- Variables
def var_a : Var := ⟨"a"⟩
def var_b : Var := ⟨"b"⟩

-- Sites
def s0 : Site := .site 0
def s1 : Site := .site 1
def s2 : Site := .site 2

/-
  `Sub` at u64. Well typed; underflows at run time when `b > a`.
-/
def fn_sub : FunDef := {
  params := [(var_a, .basic .u64), (var_b, .basic .u64)]
  returnType := [⟨.u64, none⟩]
  locals := []
  blocks := [
    { label := "b0"
      body :=
        (letsite s0 ← copy var_a) ;;
        (letsite s1 ← copy var_b) ;;
        (letsite s2 ← binop(.sub, s0, s1)) ;;
        ret [s2]
    }
  ]
}

def fn_sub_lenv := mkLabelEnv fn_sub
def fn_sub_lenvDec := mkLabelEnvDec fn_sub

#guard check_fun fn_sub fn_sub_lenv AssocMap.empty

theorem fn_sub_checks : check_fun_dec fn_sub fn_sub_lenvDec = true := by rfl

/-
  `Add` at u8. Well typed; overflows at run time when `a + b ≥ 256`.
-/
def fn_add_u8 : FunDef := {
  params := [(var_a, .basic .u8), (var_b, .basic .u8)]
  returnType := [⟨.u8, none⟩]
  locals := []
  blocks := [
    { label := "b0"
      body :=
        (letsite s0 ← copy var_a) ;;
        (letsite s1 ← copy var_b) ;;
        (letsite s2 ← binop(.add, s0, s1)) ;;
        ret [s2]
    }
  ]
}

def fn_add_u8_lenv := mkLabelEnv fn_add_u8
def fn_add_u8_lenvDec := mkLabelEnvDec fn_add_u8

#guard check_fun fn_add_u8 fn_add_u8_lenv AssocMap.empty

theorem fn_add_u8_checks : check_fun_dec fn_add_u8 fn_add_u8_lenvDec = true := by rfl

/-
  `Mul` at u8: the same product that is fine at u64 overflows here.
-/
def fn_mul_u8 : FunDef := {
  params := [(var_a, .basic .u8), (var_b, .basic .u8)]
  returnType := [⟨.u8, none⟩]
  locals := []
  blocks := [
    { label := "b0"
      body :=
        (letsite s0 ← copy var_a) ;;
        (letsite s1 ← copy var_b) ;;
        (letsite s2 ← binop(.mul, s0, s1)) ;;
        ret [s2]
    }
  ]
}

def fn_mul_u8_lenv := mkLabelEnv fn_mul_u8
def fn_mul_u8_lenvDec := mkLabelEnvDec fn_mul_u8

#guard check_fun fn_mul_u8 fn_mul_u8_lenv AssocMap.empty

theorem fn_mul_u8_checks : check_fun_dec fn_mul_u8 fn_mul_u8_lenvDec = true := by rfl

/-
  The widths beyond `u64` are not special-cased anywhere: `u256` arithmetic
  typechecks by the same `binop_type` row as `u8`.
-/
def fn_add_u256 : FunDef := {
  params := [(var_a, .basic (.int .u256)), (var_b, .basic (.int .u256))]
  returnType := [⟨.int .u256, none⟩]
  locals := []
  blocks := [
    { label := "b0"
      body :=
        (letsite s0 ← copy var_a) ;;
        (letsite s1 ← copy var_b) ;;
        (letsite s2 ← binop(.add, s0, s1)) ;;
        ret [s2]
    }
  ]
}

def fn_add_u256_lenv := mkLabelEnv fn_add_u256
def fn_add_u256_lenvDec := mkLabelEnvDec fn_add_u256

#guard check_fun fn_add_u256 fn_add_u256_lenv AssocMap.empty

theorem fn_add_u256_checks : check_fun_dec fn_add_u256 fn_add_u256_lenvDec = true := by rfl

/-
  A narrowing cast. Well typed at any pair of widths; aborts at run time when
  the value does not fit, since Move's `CastU*` checks rather than truncates.
-/
def fn_narrow : FunDef := {
  params := [(var_a, .basic .u64)]
  returnType := [⟨.u8, none⟩]
  locals := []
  blocks := [
    { label := "b0"
      body :=
        (letsite s0 ← copy var_a) ;;
        (letsite s1 ← unop(.cast .u8, s0)) ;;
        ret [s1]
    }
  ]
}

def fn_narrow_lenv := mkLabelEnv fn_narrow
def fn_narrow_lenvDec := mkLabelEnvDec fn_narrow

#guard check_fun fn_narrow fn_narrow_lenv AssocMap.empty

theorem fn_narrow_checks : check_fun_dec fn_narrow fn_narrow_lenvDec = true := by rfl

/-
  A widening cast, which can never fail.
-/
def fn_widen : FunDef := {
  params := [(var_a, .basic .u8)]
  returnType := [⟨.u64, none⟩]
  locals := []
  blocks := [
    { label := "b0"
      body :=
        (letsite s0 ← copy var_a) ;;
        (letsite s1 ← unop(.cast .u64, s0)) ;;
        ret [s1]
    }
  ]
}

def fn_widen_lenv := mkLabelEnv fn_widen
def fn_widen_lenvDec := mkLabelEnvDec fn_widen

#guard check_fun fn_widen fn_widen_lenv AssocMap.empty

theorem fn_widen_checks : check_fun_dec fn_widen fn_widen_lenvDec = true := by rfl

end LeanMove.Tests.Litmus.SizedIntArithOk
