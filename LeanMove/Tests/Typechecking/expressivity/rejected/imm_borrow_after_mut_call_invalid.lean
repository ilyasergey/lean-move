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
import LeanMove.Typing.Algorithmic.AlgorithmicTypingSoundness
import LeanMove.Lang.Macros
import LeanMove.Lang.MoveIR.PrettyPrint
import LeanMove.Tests.Parsing.TestUtils

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

namespace LeanMove.Tests.Expressivity.ImmBorrowAfterMutCallInvalid

-- Variables
def var_a : Var := ⟨"a"⟩
def var_r : Var := ⟨"r"⟩
def var_mut1 : Var := ⟨"mut1"⟩
def var_imm1 : Var := ⟨"imm1"⟩

-- Hand-written sites moved to Tests/Parsing/Test_imm_borrow_after_mut_call.lean

-- Function signatures
-- id_mut(r: &mut u64): &mut u64  { return move(r); }
def id_mut_sig : FunSig := ⟨[⟨.u64, some true⟩], [⟨.u64, some true⟩]⟩
-- id(r: &u64): &u64  { return move(r); }
def id_sig : FunSig := ⟨[⟨.u64, some false⟩], [⟨.u64, some false⟩]⟩

-- Hand-written FunDef moved to Tests/Parsing/Test_imm_borrow_after_mut_call.lean

-- -----------------------------------------------------
-- -           Parsed MVIR Definitions                 --
-- -----------------------------------------------------

open LeanMove.Tests.Parsing.TestUtils

private def immBorrowAfterMutCallMvir :=
  include_str "imm_borrow_after_mut_call.mvir"

#guard (parseAndTranslate immBorrowAfterMutCallMvir).isOk

private def parsedFuns := (parseAndTranslate immBorrowAfterMutCallMvir).toOption.get!

def parsed_invalid := (findFunInModule parsedFuns "invalid" "t").get!

-- Uncomment to pretty-print the parsed FunDef:
-- #eval IO.println (ppFunDef "t" parsed_invalid)

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
  AssocMap.insert (AssocMap.insert AssocMap.empty "invalid.id_mut" id_mut_sig) "invalid.id" id_sig

def invalid_lenv := mkLabelEnv parsed_invalid invalid_funEnv

#eval check_fun parsed_invalid invalid_lenv AssocMap.empty

-- Test: algorithmic checker rejects invalid
#guard !check_fun parsed_invalid invalid_lenv AssocMap.empty

end LeanMove.Tests.Expressivity.ImmBorrowAfterMutCallInvalid
