/-
 Copyright Ilya Sergey
 Licensed under the Apache License, Version 2.0
-/

import LeanMove.Examples.Parsing.TestUtils
import LeanMove.Examples.Typechecking.expressivity.rejected.mutable_borrows_are_not_unique_calls_invalid

/-! ## Parse Test: mutable_borrows_are_not_unique_calls.mvir (REJECTED)

Tests parsing of mutable_borrows_are_not_unique_calls — mutable borrows are not unique,
even with calls, as long as arguments have no extensions at call time.
Three modules: call (create), call_and_write_invalid (write), call_and_write_valid (write).
-/

open LeanMove.Lang.MoveLight
open LeanMove.Lang.MoveIR.Parser
open LeanMove.Lang.MoveIR.Translate
open LeanMove.Examples.Parsing.TestUtils
open LeanMove.Examples.Expressivity.MutableBorrowsNotUniqueCallsInvalid

def mutableBorrowsAreNotUniqueCallsMvir := "
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
        call = Self.borrow_f(copy(s));
        *move(call) = 0;
        f = &mut copy(s).S::f;
        *copy(f) = 0;
        return;
    }

}
"

-- Parse succeeds
#guard (parseMvir mutableBorrowsAreNotUniqueCallsMvir).isOk

-- 3 modules
#guard (parseMvir mutableBorrowsAreNotUniqueCallsMvir).toOption.get!.modules.length == 3

-- Translation succeeds
#guard (parseAndTranslate mutableBorrowsAreNotUniqueCallsMvir).isOk

-- Alpha-equivalence with hand-written example
#guard
  match parseAndTranslate mutableBorrowsAreNotUniqueCallsMvir with
  | .ok results =>
    match findFunInModule results "call_and_write_invalid" "write" with
    | some fd => alphaEquivFunDef fd call_and_write_invalid
    | none => false
  | .error _ => false
