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
def s (n : Nat) : Site := .site n

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

/-
  Bitwise `Xor` at u8. Unlike the arithmetic operators this can never overflow:
  a bitwise combination of two values below `2^8` is itself below `2^8`, which
  is why `evalBinop`'s bitwise rows carry no range guard.
-/
def fn_xor_u8 : FunDef := {
  params := [(var_a, .basic .u8), (var_b, .basic .u8)]
  returnType := [⟨.u8, none⟩]
  locals := []
  blocks := [
    { label := "b0"
      body :=
        (letsite s0 ← copy var_a) ;;
        (letsite s1 ← copy var_b) ;;
        (letsite s2 ← binop(.bitxor, s0, s1)) ;;
        ret [s2]
    }
  ]
}

def fn_xor_u8_lenv := mkLabelEnv fn_xor_u8
def fn_xor_u8_lenvDec := mkLabelEnvDec fn_xor_u8

#guard check_fun fn_xor_u8 fn_xor_u8_lenv AssocMap.empty

theorem fn_xor_u8_checks : check_fun_dec fn_xor_u8 fn_xor_u8_lenvDec = true := by rfl

/-
  `Shl` at u8, shifted by a u8. Aborts at run time when the amount reaches the
  operand width; overflowing bits are discarded rather than aborting.
-/
def fn_shl_u8 : FunDef := {
  params := [(var_a, .basic .u8), (var_b, .basic .u8)]
  returnType := [⟨.u8, none⟩]
  locals := []
  blocks := [
    { label := "b0"
      body :=
        (letsite s0 ← copy var_a) ;;
        (letsite s1 ← copy var_b) ;;
        (letsite s2 ← binop(.shl, s0, s1)) ;;
        ret [s2]
    }
  ]
}

def fn_shl_u8_lenv := mkLabelEnv fn_shl_u8
def fn_shl_u8_lenvDec := mkLabelEnvDec fn_shl_u8

#guard check_fun fn_shl_u8 fn_shl_u8_lenv AssocMap.empty

theorem fn_shl_u8_checks : check_fun_dec fn_shl_u8 fn_shl_u8_lenvDec = true := by rfl

/-
  `Shr` on a u64 by a u8 — the asymmetric shape, where the two operand types
  genuinely differ.
-/
def fn_shr_u64 : FunDef := {
  params := [(var_a, .basic .u64), (var_b, .basic .u8)]
  returnType := [⟨.u64, none⟩]
  locals := []
  blocks := [
    { label := "b0"
      body :=
        (letsite s0 ← copy var_a) ;;
        (letsite s1 ← copy var_b) ;;
        (letsite s2 ← binop(.shr, s0, s1)) ;;
        ret [s2]
    }
  ]
}

def fn_shr_u64_lenv := mkLabelEnv fn_shr_u64
def fn_shr_u64_lenvDec := mkLabelEnvDec fn_shr_u64

#guard check_fun fn_shr_u64 fn_shr_u64_lenv AssocMap.empty

theorem fn_shr_u64_checks : check_fun_dec fn_shr_u64 fn_shr_u64_lenvDec = true := by rfl

/-
  All three bitwise operators on the same pair of operands, returned together.

  `fn_xor_u8` alone pins only one of the three `evalBinop` rows: swapping the
  `bitand` and `bitor` rows leaves every existing guard green. Returning
  `[a & b, a | b, a ^ b]` from a single execution distinguishes all three, since
  no two of them agree on operands that share some but not all bits.
-/
def fn_bit_table : FunDef := {
  params := [(var_a, .basic .u8), (var_b, .basic .u8)]
  returnType := [⟨.u8, none⟩, ⟨.u8, none⟩, ⟨.u8, none⟩]
  locals := []
  blocks := [
    { label := "b0"
      body :=
        (letsite (s 0) ← copy var_a) ;;
        (letsite (s 1) ← copy var_b) ;;
        (letsite (s 2) ← binop(.bitand, (s 0), (s 1))) ;;
        (letsite (s 3) ← copy var_a) ;;
        (letsite (s 4) ← copy var_b) ;;
        (letsite (s 5) ← binop(.bitor, (s 3), (s 4))) ;;
        (letsite (s 6) ← copy var_a) ;;
        (letsite (s 7) ← copy var_b) ;;
        (letsite (s 8) ← binop(.bitxor, (s 6), (s 7))) ;;
        ret [(s 2), (s 5), (s 8)]
    }
  ]
}

def fn_bit_table_lenv := mkLabelEnv fn_bit_table
def fn_bit_table_lenvDec := mkLabelEnvDec fn_bit_table

#guard check_fun fn_bit_table fn_bit_table_lenv AssocMap.empty

theorem fn_bit_table_checks : check_fun_dec fn_bit_table fn_bit_table_lenvDec = true := by rfl

/-
  `Div` at u64. Well typed; aborts with `divisionByZero` at run time when the
  divisor is zero. Nothing else in the tree reaches that error constructor, so
  without this function the `divisionByZero` arm of `isAcceptable` is only ever
  discharged vacuously.
-/
def fn_div_u64 : FunDef := {
  params := [(var_a, .basic .u64), (var_b, .basic .u64)]
  returnType := [⟨.u64, none⟩]
  locals := []
  blocks := [
    { label := "b0"
      body :=
        (letsite s0 ← copy var_a) ;;
        (letsite s1 ← copy var_b) ;;
        (letsite s2 ← binop(.div, s0, s1)) ;;
        ret [s2]
    }
  ]
}

def fn_div_u64_lenv := mkLabelEnv fn_div_u64
def fn_div_u64_lenvDec := mkLabelEnvDec fn_div_u64

#guard check_fun fn_div_u64 fn_div_u64_lenv AssocMap.empty

theorem fn_div_u64_checks : check_fun_dec fn_div_u64 fn_div_u64_lenvDec = true := by rfl

/-
  `Mod` at u64 — the other operator with a zero divisor.
-/
def fn_mod_u64 : FunDef := {
  params := [(var_a, .basic .u64), (var_b, .basic .u64)]
  returnType := [⟨.u64, none⟩]
  locals := []
  blocks := [
    { label := "b0"
      body :=
        (letsite s0 ← copy var_a) ;;
        (letsite s1 ← copy var_b) ;;
        (letsite s2 ← binop(.mod, s0, s1)) ;;
        ret [s2]
    }
  ]
}

def fn_mod_u64_lenv := mkLabelEnv fn_mod_u64
def fn_mod_u64_lenvDec := mkLabelEnvDec fn_mod_u64

#guard check_fun fn_mod_u64 fn_mod_u64_lenv AssocMap.empty

theorem fn_mod_u64_checks : check_fun_dec fn_mod_u64 fn_mod_u64_lenvDec = true := by rfl

end LeanMove.Tests.Litmus.SizedIntArithOk
