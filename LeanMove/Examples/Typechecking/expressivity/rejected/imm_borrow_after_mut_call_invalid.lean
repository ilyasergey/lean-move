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
import LeanMove.Typing.Algorithmic.TypeCheckingAlgorithmic
import LeanMove.Typing.Algorithmic.AlgorithmicTypingSoundness
import LeanMove.Lang.Macros

/-!
# Immutable Borrow After Mutable Call - Invalid Module

Source: https://github.com/tnowacki/sui/blob/example-tests/external-crates/move/crates/bytecode-verifier-transactional-tests/tests/reference_safety/expressivity/imm_borrow_after_mut_call.mvir

This file contains the INVALID module that fails because you cannot write to
a mutable reference when an immutable reference to the same root exists.

Original MVIR:
```
// can create an immutabe extension via a call after a mut borrow,
// but if the mut is a parent, it won't be writable

//# publish
module 0x2.valid {

    id_mut(r: &mut u64): &mut u64 {
    label b0:
        return move(r);
    }

    id(r: &u64): &u64 {
    label b0:
        return move(r);
    }

    t() {
        let a: u64;
        let r: &mut u64;
        let mut1: &mut u64;
        let imm1: &u64;
        let imm2: &u64;
        let imm3: &u64;
    label b0:
        a = 0;
        r = &mut a;
        mut1 = Self.id_mut(copy(r));
        // all valid
        imm1 = Self.id(&a);
        imm2 = Self.id(freeze(copy(r)));
        imm3 = Self.id(freeze(copy(mut1)));
        // all readable
        _ = *copy(imm1);
        _ = *copy(imm2);
        _ = *copy(imm3);
        return;
    }
}

//# publish
module 0x2.invalid {

    id_mut(r: &mut u64): &mut u64 {
    label b0:
        return move(r);
    }

    id(r: &u64): &u64 {
    label b0:
        return move(r);
    }

    t() {
        let a: u64;
        let r: &mut u64;
        let mut1: &mut u64;
        let imm1: &u64;
    label b0:
        a = 0;
        r = &mut a;
        mut1 = Self.id_mut(copy(r));
        // all valid
        imm1 = Self.id(&a);
        // cannot write to mut1
        *copy(mut1) = 0;
        return;
    }
}
```
-/

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Typing
open AssocMap
open Regex

namespace LeanMove.Examples.Expressivity.ImmBorrowAfterMutCallInvalid

-- Variables
def var_a : Var := ⟨"a"⟩
def var_r : Var := ⟨"r"⟩
def var_mut1 : Var := ⟨"mut1"⟩
def var_imm1 : Var := ⟨"imm1"⟩

-- Sites
def s0 : Site := .site 0   -- integer literal 0 for a
def s1 : Site := .site 1   -- &mut a
def s2 : Site := .site 2   -- copy(r) [input to id_mut]
def s3 : Site := .site 3   -- output of id_mut
def s4 : Site := .site 4   -- &a [input to id]
def s5 : Site := .site 5   -- output of id
def s6 : Site := .site 6   -- copy(mut1)
def s7 : Site := .site 7   -- integer literal 0 for write

-- Function signatures
-- id_mut(r: &mut u64): &mut u64  { return move(r); }
def id_mut_sig : FunSig := ⟨[⟨.u64, some true⟩], [⟨.u64, some true⟩]⟩
-- id(r: &u64): &u64  { return move(r); }
def id_sig : FunSig := ⟨[⟨.u64, some false⟩], [⟨.u64, some false⟩]⟩

/-
  invalid module: "cannot write to mut1"

  t() {
      let a: u64;
      let r: &mut u64;
      let mut1: &mut u64;
      let imm1: &u64;
  label b0:
      a = 0;
      r = &mut a;
      mut1 = Self.id_mut(copy(r));  -- call id_mut
      imm1 = Self.id(&a);           -- call id
      *copy(mut1) = 0;              -- ERROR: cannot write, a has immutable alias imm1
      return;
  }
-/
def invalid : FunDef := {
  params := []
  returnType := []
  locals := [
    { name := var_a, type := .basic .u64 },
    { name := var_r, type := .ref .u64 (.refid 0) .siteBorrowMut },
    { name := var_mut1, type := .ref .u64 (.refid 1) .siteBorrowMut },
    { name := var_imm1, type := .ref .u64 (.refid 2) .siteBorrowImm }
  ]
  blocks := [
    { label := "b0"
      body :=
        -- a = 0
        (letsite s0 ← #0) ;;
        (var_a ::= s0) ;;
        -- r = &mut a
        (letsite s1 ← &mut var_a) ;;
        (var_r ::= s1) ;;
        -- mut1 = Self.id_mut(copy(r))  [using call macro]
        (letsite s2 ← copy var_r) ;;
        (call([s3], "id_mut", [s2])) ;;
        (var_mut1 ::= s3) ;;
        -- imm1 = Self.id(&a)  [using call macro]
        (letsite s4 ← &var_a) ;;
        (call([s5], "id", [s4])) ;;
        (var_imm1 ::= s5) ;;
        -- *copy(mut1) = 0 -- ERROR: a is immutably borrowed via imm1
        (letsite s6 ← copy var_mut1) ;;
        (letsite s7 ← #0) ;;
        (*s6 ::= s7) ;;
        ret []
    }
  ]
}

/-!
## Why this is rejected

After `call([s3], "id_mut", [s2])`, `call_connect_inputs_outputs` creates paths
connecting the mutable output ref (s3) to the mutable input ref (s2, which traces back
to `r`'s borrow of `a`). Then after `call([s5], "id", [s4])`, the immutable output
ref (s5) is connected to the immutable input ref (s4 = &a). When `writeRef` on
`copy(mut1)` is checked, `check_outbound_bool` finds paths from `mut1`'s ref (through
`r` and `.root`) to `imm1`'s ref, rejecting the write.

## Runtime behavior

The interpreter writes `0` to the heap location. Both `mut1` and `imm1` point to the same
location, and the write goes through. In a real Move VM, this would violate the immutability
guarantee of `imm1`. The small-step semantics intentionally does not enforce borrow rules.
-/

-- -----------------------------------------------------
-- -           Algorithmic Type Checking Tests        --
-- -----------------------------------------------------

-- Function environment with id_mut and id signatures
def invalid_funEnv : FunEnv :=
  AssocMap.insert (AssocMap.insert AssocMap.empty "id_mut" id_mut_sig) "id" id_sig

-- Initial environment for invalid function
def invalid_initEnv : TypeEnv := {
  siteEnv := AssocMap.empty
  varEnv := init_fun_varEnv invalid
  pathEnv := init_fun_pathEnv invalid
  funEnv := invalid_funEnv
}

-- LabelEnv for invalid
def invalid_lenv : LabelEnv :=
  AssocMap.insert AssocMap.empty "b0" invalid_initEnv

#eval check_fun invalid invalid_lenv

-- Test: algorithmic checker rejects invalid
#guard !check_fun invalid invalid_lenv

end LeanMove.Examples.Expressivity.ImmBorrowAfterMutCallInvalid
