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
import LeanMove.Lang.Macros

/-!
# Call Rule Accepted Tests

Tests demonstrating that the call rule correctly accepts valid programs.

Callee functions:
- `fn_deref(r: &mut u64): u64` — dereferences the ref, returns basic value
- `fn_id_mut(r: &mut u64): &mut u64` — identity on mutable refs

Caller tests:
1. **basic_return_then_write**: Call `fn_deref(copy(m))`, then write through `m`.
   Accepted because the call returns a basic value — `call_connect_inputs_outputs`
   creates no output ref connections.

2. **read_through_call_output**: Call `fn_id_mut(copy(m))`, assign to `mut1`, then
   read through `mut1`. Accepted because `readRef` does not invoke `check_outbound_bool`.
-/

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Typing
open AssocMap

namespace LeanMove.Tests.Litmus.CallRuleOk

-- Variables
def var_r : Var := ⟨"r"⟩
def var_a : Var := ⟨"a"⟩
def var_m : Var := ⟨"m"⟩
def var_mut1 : Var := ⟨"mut1"⟩

-- Sites
def s0 : Site := .site 0
def s1 : Site := .site 1
def s2 : Site := .site 2
def s3 : Site := .site 3
def s4 : Site := .site 4
def s5 : Site := .site 5

-- Function signatures
def deref_sig : FunSig := ⟨[⟨.u64, some true⟩], [⟨.u64, none⟩]⟩
def id_mut_sig : FunSig := ⟨[⟨.u64, some true⟩], [⟨.u64, some true⟩]⟩

-- ═══════════════════════════════════════════════════════
-- Callee: fn_deref(r: &mut u64): u64
-- ═══════════════════════════════════════════════════════

def fn_deref : FunDef := {
  params := [(var_r, .ref .u64 (.paramRef var_r) .siteBorrowMut)]
  returnType := [⟨.u64, none⟩]
  locals := []
  blocks := [
    { label := "b0"
      body :=
        (letsite s0 ← move var_r) ;;
        (letsite s1 ← *s0) ;;
        ret [s1]
    }
  ]
}

def fn_deref_lenvDec := mkLabelEnvDec fn_deref

theorem fn_deref_check : check_fun_dec fn_deref fn_deref_lenvDec = true := by rfl

-- ═══════════════════════════════════════════════════════
-- Callee: fn_id_mut(r: &mut u64): &mut u64
-- ═══════════════════════════════════════════════════════

def fn_id_mut : FunDef := {
  params := [(var_r, .ref .u64 (.paramRef var_r) .siteBorrowMut)]
  returnType := [⟨.u64, some true⟩]
  locals := []
  blocks := [
    { label := "b0"
      body :=
        (letsite s0 ← move var_r) ;;
        ret [s0]
    }
  ]
}

def fn_id_mut_lenvDec := mkLabelEnvDec fn_id_mut

theorem fn_id_mut_check : check_fun_dec fn_id_mut fn_id_mut_lenvDec = true := by rfl

-- ═══════════════════════════════════════════════════════
-- Test 1: basic_return_then_write
-- ═══════════════════════════════════════════════════════

/-
  t() {
      let a: u64;
      let m: &mut u64;
  label b0:
      a = 0;
      m = &mut a;
      _ = Self.fn_deref(copy(m));  // returns basic u64, no ref alias
      *copy(m) = 0;                // OK: no outbound edges from m
      return;
  }
-/
def basic_return_then_write : FunDef := {
  params := []
  returnType := []
  locals := [
    { name := var_a, type := .basic .u64 },
    { name := var_m, type := .ref .u64 (.refid 0) .siteBorrowMut }
  ]
  blocks := [
    { label := "b0"
      body :=
        (letsite s0 ← #0) ;;
        (var_a ::= s0) ;;
        (letsite s1 ← &mut var_a) ;;
        (var_m ::= s1) ;;
        (letsite s2 ← copy var_m) ;;
        (call([s3], "deref", [s2])) ;;
        (letsite s4 ← copy var_m) ;;
        (letsite s5 ← #0) ;;
        (*s4 ::= s5) ;;
        ret []
    }
  ]
}

def deref_funEnv : FunEnv := insert empty "deref" deref_sig

def basic_return_then_write_lenvDec := mkLabelEnvDec basic_return_then_write deref_funEnv

theorem basic_return_then_write_check :
    check_fun_dec basic_return_then_write basic_return_then_write_lenvDec = true := by rfl

theorem basic_return_then_write_welltyped :
    ∃ lenv, typecheck_fun basic_return_then_write lenv :=
  ⟨_, check_fun_dec_sound _ _ basic_return_then_write_check⟩

-- ═══════════════════════════════════════════════════════
-- Test 2: read_through_call_output
-- ═══════════════════════════════════════════════════════

/-
  t() {
      let a: u64;
      let m: &mut u64;
      let mut1: &mut u64;
  label b0:
      a = 0;
      m = &mut a;
      mut1 = Self.fn_id_mut(copy(m));  // returns mutable ref (aliased with m)
      _ = *copy(mut1);                 // OK: readRef never checks outbound
      return;
  }
-/
def read_call_output : FunDef := {
  params := []
  returnType := []
  locals := [
    { name := var_a, type := .basic .u64 },
    { name := var_m, type := .ref .u64 (.refid 0) .siteBorrowMut },
    { name := var_mut1, type := .ref .u64 (.refid 1) .siteBorrowMut }
  ]
  blocks := [
    { label := "b0"
      body :=
        (letsite s0 ← #0) ;;
        (var_a ::= s0) ;;
        (letsite s1 ← &mut var_a) ;;
        (var_m ::= s1) ;;
        (letsite s2 ← copy var_m) ;;
        (call([s3], "id_mut", [s2])) ;;
        (var_mut1 ::= s3) ;;
        (letsite s4 ← copy var_mut1) ;;
        (letsite s5 ← *s4) ;;
        ret []
    }
  ]
}

def id_mut_funEnv : FunEnv := insert empty "id_mut" id_mut_sig

def read_call_output_lenvDec := mkLabelEnvDec read_call_output id_mut_funEnv

theorem read_call_output_check :
    check_fun_dec read_call_output read_call_output_lenvDec = true := by rfl

theorem read_call_output_welltyped :
    ∃ lenv, typecheck_fun read_call_output lenv :=
  ⟨_, check_fun_dec_sound _ _ read_call_output_check⟩

end LeanMove.Tests.Litmus.CallRuleOk
