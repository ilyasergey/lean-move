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
# Mutable Borrows Not Unique Calls - Invalid Module

Source: https://github.com/tnowacki/sui/blob/example-tests/external-crates/move/crates/bytecode-verifier-transactional-tests/tests/reference_safety/expressivity/mutable_borrows_are_not_unique_calls.mvir

This file contains the INVALID module (call_and_write_invalid) that fails because
you cannot write to mutable references when their relationship is unknown.

Original MVIR:
```
// mutable borrows are not unique

//# publish
module 0x4.call {

    struct S has copy, drop { f: u64 }

    borrow_f(s: &mut Self.S): &mut u64 {
    label b0:
        return &mut move(s).S::f;
    }

    create(s: &mut Self.S) {
        let call: &mut u64;
        let f: &mut u64;
    label b0:
        // we can create multiple mutable references, even with a call, as long as the argument
        // to the call does not have any extensions at the time of the call (and as long as it does
        // not overlap with any other arguments)

        // if we swap the call with the field borrow, this will error
        call = Self.borrow_f(copy(s));
        f = &mut copy(s).S::f;
        return;
    }

}

//# publish
module 0x5.call_and_write_invalid {

    struct S has copy, drop { f: u64 }

    borrow_f(s: &mut Self.S): &mut u64 {
    label b0:
        return &mut move(s).S::f;
    }

    write(s: &mut Self.S) {
        let call: &mut u64;
        let f: &mut u64;
    label b0:
        // While mutable references are not unique, and we can create all sorts of overlaps, that
        // does not mean that we can write to all of them.
        // We cannot write to either call or f since we do not know the relationship between them.
        // While it is "safe" in this case, we do not look at the type layout for that information.
        // It could be the case that f extends call, and that call extends f.
        call = Self.borrow_f(copy(s));
        f = &mut copy(s).S::f;
        *copy(call) = 0;
        *copy(f) = 0;
        return;
    }

}

//# publish
module 0x6.call_and_write_valid {

    struct S has copy, drop { f: u64 }

    borrow_f(s: &mut Self.S): &mut u64 {
    label b0:
        return &mut move(s).S::f;
    }

    write(s: &mut Self.S) {
        let call: &mut u64;
        let f: &mut u64;
    label b0:
        // If however we free the call's return value before borrowing f, this is valid.
        call = Self.borrow_f(copy(s));
        *move(call) = 0; // the move frees the value
        f = &mut copy(s).S::f;
        *copy(f) = 0;

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

namespace LeanMove.Tests.Expressivity.MutableBorrowsNotUniqueCallsInvalid

-- Fields for struct
def field_f : Field := ⟨"f"⟩

-- S { f: u64 }
def s_entries : AssocMap Field BasicMoveType := insert empty field_f .u64

-- Variables
def var_s : Var := ⟨"s"⟩
def var_call : Var := ⟨"call"⟩
def var_f : Var := ⟨"f"⟩

/- Hand-written sites and FunDefs commented out; using parsed MVIR versions instead

-- Sites for borrow_f function
def bs0 : Site := .site 0   -- copy(s) in borrow_f
def bs1 : Site := .site 1   -- &mut bs0.S::f in borrow_f

-- Sites for call_and_write_invalid function
def s0 : Site := .site 0   -- copy(s) for call argument
def s1 : Site := .site 1   -- result site from call to borrow_f
def s2 : Site := .site 2   -- copy(s) for f
def s3 : Site := .site 3   -- &mut s2.S::f (for f)
def s4 : Site := .site 4   -- copy(call)
def s5 : Site := .site 5   -- integer literal 0 for first write
def s6 : Site := .site 6   -- copy(f)
def s7 : Site := .site 7   -- integer literal 0 for second write

/-
  borrow_f(s: &mut Self.S): &mut u64
  Returns a mutable reference to the f field.
-/
def borrow_f : FunDef := {
  params := [(var_s, .ref (.trecord s_entries) (.paramRef var_s) .siteBorrowMut)]
  returnType := [⟨.u64, some true⟩]
  locals := []
  blocks := [
    { label := "b0"
      body :=
        (letsite bs0 ← copy var_s) ;;
        (letsite bs1 ← borrowMutField(bs0, .trecord s_entries, field_f)) ;;
        ret [bs1]
    }
  ]
}

-/

-- Function signature for borrow_f
def borrow_f_sig : FunSig :=
  ⟨[⟨.trecord s_entries, some true⟩], [⟨.u64, some true⟩]⟩

-- Function environment containing borrow_f
def call_funEnv : FunEnv :=
  AssocMap.insert AssocMap.empty "borrow_f" borrow_f_sig

/- Hand-written call_and_write_invalid commented out; using parsed MVIR version instead

/-
  call_and_write_invalid module: "we cannot write to either call or f since we
  do not know the relationship between them"

  write(s: &mut Self.S) {
      let call: &mut u64;
      let f: &mut u64;
  label b0:
      call = Self.borrow_f(copy(s));
      f = &mut copy(s).S::f;
      *copy(call) = 0;                -- ERROR: relationship with f unknown
      *copy(f) = 0;                   -- ERROR: relationship with call unknown
      return;
  }
-/
def call_and_write_invalid : FunDef := {
  params := [(var_s, .ref (.trecord s_entries) (.paramRef var_s) .siteBorrowMut)]
  returnType := []
  locals := [
    { name := var_call, type := .ref .u64 (.refid 1) .siteBorrowMut },
    { name := var_f, type := .ref .u64 (.refid 2) .siteBorrowMut }
  ]
  blocks := [
    { label := "b0"
      body :=
        -- call = Self.borrow_f(copy(s))
        (letsite s0 ← copy var_s) ;;
        (call([s1], "borrow_f", [s0])) ;;
        (var_call ::= s1) ;;
        -- f = &mut copy(s).S::f
        (letsite s2 ← copy var_s) ;;
        (letsite s3 ← borrowMutField(s2, .trecord s_entries, field_f)) ;;
        (var_f ::= s3) ;;
        -- *copy(call) = 0 -- ERROR: relationship with f unknown
        (letsite s4 ← copy var_call) ;;
        (letsite s5 ← #0) ;;
        (*s4 ::= s5) ;;
        -- *copy(f) = 0 -- ERROR: relationship with call unknown
        (letsite s6 ← copy var_f) ;;
        (letsite s7 ← #0) ;;
        (*s6 ::= s7) ;;
        ret []
    }
  ]
}

-/

-- -----------------------------------------------------
-- -           Parsed MVIR Definitions                 --
-- -----------------------------------------------------

open LeanMove.Tests.Parsing.TestUtils

private def mutableBorrowsNotUniqueCallsMvir :=
  include_str "mutable_borrows_are_not_unique_calls.mvir"

#guard (parseAndTranslate mutableBorrowsNotUniqueCallsMvir).isOk

private def parsedFuns := (parseAndTranslate mutableBorrowsNotUniqueCallsMvir).toOption.get!

def parsed_borrow_f := (findFunInModule parsedFuns "call_and_write_invalid" "borrow_f").get!

def parsed_call_and_write_invalid := (findFunInModule parsedFuns "call_and_write_invalid" "write").get!

-- Uncomment to pretty-print the parsed FunDefs:
-- #eval IO.println (ppFunDef "borrow_f" parsed_borrow_f)
-- #eval IO.println (ppFunDef "t" parsed_call_and_write_invalid)

/-!
## Why this is rejected

Both `call` and `f` are mutable borrows of `s.f`, created from separate `copy(s)` operations.
The PathEnv records that `call`'s ref extends `s`'s ref via `[.field "f"]`, and `f`'s ref
also extends `s`'s ref via `[.field "f"]`. When either `writeRef` is checked,
`check_outbound_bool` finds outbound paths from the written reference to the other reference
(both trace back to `s`). Since the type checker cannot determine the exact relationship
between `call` and `f` (they could overlap), it conservatively rejects both writes.

## Runtime behavior

Both `call` and `f` point to the same heap field (`s.f`). The writes to `0` are sequential
and valid — each overwrites the same location. The function halts successfully. The
small-step semantics intentionally does not enforce borrow rules.
-/

-- -----------------------------------------------------
-- -           Algorithmic Type Checking Tests        --
-- -----------------------------------------------------

def call_and_write_invalid_lenv := mkLabelEnv parsed_call_and_write_invalid call_funEnv

-- Debug
#eval check_fun parsed_call_and_write_invalid call_and_write_invalid_lenv

-- Test: algorithmic checker rejects call_and_write_invalid
#guard !check_fun parsed_call_and_write_invalid call_and_write_invalid_lenv

end LeanMove.Tests.Expressivity.MutableBorrowsNotUniqueCallsInvalid
