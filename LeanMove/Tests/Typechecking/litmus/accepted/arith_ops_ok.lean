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
# Multiplication — Accepted

`Mul` is an integer instruction: typed at `u64 × u64 → u64`, like `Add`, `Sub`,
`Div` and `Mod`. The opcode and its `binop_type` row long predate the concrete
syntax for it — until `*` was admitted as an infix operator there was no way to
reach `Binop.mul` from a `.mvir` source, and so no test exercised it.

The reference-typed cases below are the ones worth having: `*` is overloaded in
the concrete syntax (prefix dereference, infix multiplication), so a product of
two dereferences and a product written *through* a reference are the shapes
where a parser slip would show up as a typing error rather than a parse error.

## Test 1: `fn_mul`
```
fn_mul(a: u64, b: u64): u64 {
label b0:
    s0 = copy(a); s1 = copy(b); s2 = s0 * s1;
    return s2;
}
```

## Test 2: `fn_mul_add`
`(a * b) + c` — `Mul` composed with another arithmetic operator.

## Test 3: `fn_mul_derefs`
`*a * *b` on two immutable references: each operand is a `readRef`, and the
product is taken of the two read values.

## Test 4: `fn_scale`
`*r = k * k` — a product written back through a mutable reference.
-/

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Typing
open AssocMap

namespace LeanMove.Tests.Litmus.ArithOpsOk

-- Variables
def var_a : Var := ⟨"a"⟩
def var_b : Var := ⟨"b"⟩
def var_c : Var := ⟨"c"⟩
def var_k : Var := ⟨"k"⟩
def var_r : Var := ⟨"r"⟩

-- Sites
def s (n : Nat) : Site := .site n

-- ═══════════════════════════════════════════════════════
-- Test 1: fn_mul — the plain integer product
-- ═══════════════════════════════════════════════════════

def fn_mul : FunDef := {
  params := [(var_a, .basic .u64), (var_b, .basic .u64)]
  returnType := [⟨.u64, none⟩]
  locals := []
  blocks := [
    { label := "b0"
      body :=
        (letsite (s 0) ← copy var_a) ;;
        (letsite (s 1) ← copy var_b) ;;
        (letsite (s 2) ← binop(.mul, (s 0), (s 1))) ;;
        ret [(s 2)]
    }
  ]
}

def fn_mul_lenvDec := mkLabelEnvDec fn_mul

theorem fn_mul_check : check_fun_dec fn_mul fn_mul_lenvDec = true := by rfl

theorem fn_mul_welltyped :
    ∃ lenv, typecheck_fun fn_mul lenv AssocMap.empty :=
  ⟨_, check_fun_dec_sound _ _ _ fn_mul_check⟩

-- ═══════════════════════════════════════════════════════
-- Test 2: fn_mul_add — (a * b) + c
-- ═══════════════════════════════════════════════════════

def fn_mul_add : FunDef := {
  params := [(var_a, .basic .u64), (var_b, .basic .u64), (var_c, .basic .u64)]
  returnType := [⟨.u64, none⟩]
  locals := []
  blocks := [
    { label := "b0"
      body :=
        (letsite (s 0) ← copy var_a) ;;
        (letsite (s 1) ← copy var_b) ;;
        (letsite (s 2) ← binop(.mul, (s 0), (s 1))) ;;
        (letsite (s 3) ← copy var_c) ;;
        (letsite (s 4) ← binop(.add, (s 2), (s 3))) ;;
        ret [(s 4)]
    }
  ]
}

def fn_mul_add_lenvDec := mkLabelEnvDec fn_mul_add

theorem fn_mul_add_check :
    check_fun_dec fn_mul_add fn_mul_add_lenvDec = true := by rfl

theorem fn_mul_add_welltyped :
    ∃ lenv, typecheck_fun fn_mul_add lenv AssocMap.empty :=
  ⟨_, check_fun_dec_sound _ _ _ fn_mul_add_check⟩

-- ═══════════════════════════════════════════════════════
-- Test 3: fn_mul_derefs — *a * *b
-- ═══════════════════════════════════════════════════════

def fn_mul_derefs : FunDef := {
  params := [(var_a, .ref .u64 (.paramRef var_a) .siteBorrowImm),
             (var_b, .ref .u64 (.paramRef var_b) .siteBorrowImm)]
  returnType := [⟨.u64, none⟩]
  locals := []
  blocks := [
    { label := "b0"
      body :=
        (letsite (s 0) ← copy var_a) ;;
        (letsite (s 1) ← *(s 0)) ;;
        (letsite (s 2) ← copy var_b) ;;
        (letsite (s 3) ← *(s 2)) ;;
        (letsite (s 4) ← binop(.mul, (s 1), (s 3))) ;;
        ret [(s 4)]
    }
  ]
}

def fn_mul_derefs_lenvDec := mkLabelEnvDec fn_mul_derefs

theorem fn_mul_derefs_check :
    check_fun_dec fn_mul_derefs fn_mul_derefs_lenvDec = true := by rfl

theorem fn_mul_derefs_welltyped :
    ∃ lenv, typecheck_fun fn_mul_derefs lenv AssocMap.empty :=
  ⟨_, check_fun_dec_sound _ _ _ fn_mul_derefs_check⟩

-- ═══════════════════════════════════════════════════════
-- Test 4: fn_scale — *r = k * k
-- ═══════════════════════════════════════════════════════

def fn_scale : FunDef := {
  params := [(var_r, .ref .u64 (.paramRef var_r) .siteBorrowMut),
             (var_k, .basic .u64)]
  returnType := []
  locals := []
  blocks := [
    { label := "b0"
      body :=
        (letsite (s 0) ← copy var_r) ;;
        (letsite (s 1) ← copy var_k) ;;
        (letsite (s 2) ← copy var_k) ;;
        (letsite (s 3) ← binop(.mul, (s 1), (s 2))) ;;
        (*(s 0) ::= (s 3)) ;;
        ret []
    }
  ]
}

def fn_scale_lenvDec := mkLabelEnvDec fn_scale

theorem fn_scale_check : check_fun_dec fn_scale fn_scale_lenvDec = true := by rfl

theorem fn_scale_welltyped :
    ∃ lenv, typecheck_fun fn_scale lenv AssocMap.empty :=
  ⟨_, check_fun_dec_sound _ _ _ fn_scale_check⟩

-- ═══════════════════════════════════════════════════════
-- Test 5: fn_scale_read — *r = k * k; return *r
-- ═══════════════════════════════════════════════════════

/-
`fn_scale` returns nothing, so the only thing a runtime test can observe about
it is that it halts — which says nothing about the product it wrote. Reading the
reference back makes the written value part of the result, so `k * k` can be
told apart from `k + k`.
-/
def fn_scale_read : FunDef := {
  params := [(var_r, .ref .u64 (.paramRef var_r) .siteBorrowMut),
             (var_k, .basic .u64)]
  returnType := [⟨.u64, none⟩]
  locals := []
  blocks := [
    { label := "b0"
      body :=
        (letsite (s 0) ← copy var_r) ;;
        (letsite (s 1) ← copy var_k) ;;
        (letsite (s 2) ← copy var_k) ;;
        (letsite (s 3) ← binop(.mul, (s 1), (s 2))) ;;
        (*(s 0) ::= (s 3)) ;;
        (letsite (s 4) ← copy var_r) ;;
        (letsite (s 5) ← *(s 4)) ;;
        ret [(s 5)]
    }
  ]
}

def fn_scale_read_lenvDec := mkLabelEnvDec fn_scale_read

theorem fn_scale_read_check :
    check_fun_dec fn_scale_read fn_scale_read_lenvDec = true := by rfl

theorem fn_scale_read_welltyped :
    ∃ lenv, typecheck_fun fn_scale_read lenv AssocMap.empty :=
  ⟨_, check_fun_dec_sound _ _ _ fn_scale_read_check⟩

end LeanMove.Tests.Litmus.ArithOpsOk
