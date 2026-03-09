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
# Immutable Borrow After Mutable Fields - Invalid Module

Source: https://github.com/tnowacki/sui/blob/example-tests/external-crates/move/crates/bytecode-verifier-transactional-tests/tests/reference_safety/expressivity/imm_borrow_after_mut_fields.mvir

This file contains the INVALID module (invalid_write) that fails because you cannot
write through a mutable reference when an immutable reference to the same location exists.

Original MVIR:
```
// can borrow imm fields after a mut borrow, but if the mut is a parent, it won't be writable

//# publish
module 0x2.field {

    struct S has copy, drop { f: u64 }

    t(s: Self.S) {
        let s_imm: &Self.S;
        let s_mut: &mut Self.S;
        let f_imm: &u64;
    label b0:
        s_imm = &s;
        s_mut = &mut s;
        f_imm = &copy(s_imm).S::f;
        return;
    }
}

//# publish
module 0x3.field {

    struct S has copy, drop { f: u64 }

    t(s: Self.S) {
        let s_imm: &Self.S;
        let s_mut: &mut Self.S;
        let f_imm: &u64;
    label b0:
        // not really after, but also allowed
        s_imm = &s;
        f_imm = &copy(s_imm).S::f;
        s_mut = &mut s;
        return;
    }
}

//# publish
module 0x4.invalid_write {

    struct S has copy, drop { f: u64 }

    t(s: Self.S) {
        let s_imm: &Self.S;
        let s_mut: &mut Self.S;
        let f_imm: &u64;
    label b0:
        s_imm = &s;
        s_mut = &mut s;
        f_imm = &copy(s_imm).S::f;
        // cannot write to s_mut because of f_imm
        *copy(s_mut) = S { f: 0 };
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

namespace LeanMove.Tests.Expressivity.ImmBorrowAfterMutFieldsInvalid

-- Field for S struct
def field_f : Field := ⟨"f"⟩

-- S { f: u64 }
def s_entries : AssocMap Field BasicMoveType := insert empty field_f .u64

-- Variables
def var_s : Var := ⟨"s"⟩
def var_s_mut : Var := ⟨"s_mut"⟩
def var_s_imm : Var := ⟨"s_imm"⟩
def var_f_imm : Var := ⟨"f_imm"⟩

-- Hand-written FunDef moved to Tests/Parsing/Test_imm_borrow_after_mut_fields.lean

-- -----------------------------------------------------
-- -           Parsed MVIR Definitions                 --
-- -----------------------------------------------------

open LeanMove.Tests.Parsing.TestUtils

private def immBorrowAfterMutFieldsMvir :=
  include_str "imm_borrow_after_mut_fields.mvir"

#guard (parseAndTranslate immBorrowAfterMutFieldsMvir).isOk

private def parsedFuns := (parseAndTranslate immBorrowAfterMutFieldsMvir).toOption.get!

def parsed_invalid_write := (findFunInModule parsedFuns "invalid_write" "t").get!

-- Uncomment to pretty-print the parsed FunDef:
-- #eval IO.println (ppFunDef "t" parsed_invalid_write)

/-!
## Why this is rejected

After `f_imm = &copy(s_imm).S::f`, the PathEnv records that `f_imm`'s reference extends
`s_imm`, which in turn borrows from `s`. When `writeRef` on `copy(s_mut)` is checked,
`check_outbound_bool` detects that `s_mut`'s reference has outbound paths (through `s`)
to `f_imm`'s reference. The write is rejected because it would invalidate the immutable
borrow `f_imm`.

## Runtime behavior

The interpreter writes `S{f:0}` to the heap location without checking alias validity.
The function halts successfully. The small-step semantics intentionally does not enforce
borrow rules.
-/

-- -----------------------------------------------------
-- -           Algorithmic Type Checking Tests        --
-- -----------------------------------------------------

def invalid_write_lenv := mkLabelEnv parsed_invalid_write

-- Debug
#eval check_fun parsed_invalid_write invalid_write_lenv AssocMap.empty

-- Test: algorithmic checker rejects invalid_write
#guard !check_fun parsed_invalid_write invalid_write_lenv AssocMap.empty

-- Theorem: invalid_write is ILL-typed (REJECTED by type checker)
-- Note: proving this formally requires the completeness theorem (check_fun_complete),
-- which is not yet fully proven. The algorithmic rejection above demonstrates the result.

end LeanMove.Tests.Expressivity.ImmBorrowAfterMutFieldsInvalid
