/-
 Copyright Ilya Sergey
 Licensed under the Apache License, Version 2.0
-/

import LeanMove.Tests.Parsing.TestUtils
import LeanMove.Tests.Typechecking.expressivity.rejected.mutable_borrows_are_not_unique_calls_invalid

/-! ## Parse Test: mutable_borrows_are_not_unique_calls.mvir (REJECTED)

Tests parsing of mutable_borrows_are_not_unique_calls — mutable borrows are not unique,
even with calls, as long as arguments have no extensions at call time.
Three modules: call (create), call_and_write_invalid (write), call_and_write_valid (write).
-/

open LeanMove.Lang.MoveLight
open LeanMove.Lang.MoveIR.Parser
open LeanMove.Lang.MoveIR.Translate
open LeanMove.Tests.Parsing.TestUtils
open LeanMove.Tests.Expressivity.MutableBorrowsNotUniqueCallsInvalid

def mutableBorrowsAreNotUniqueCallsMvir :=
  include_str "../Typechecking/expressivity/rejected/mutable_borrows_are_not_unique_calls.mvir"

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
    | some fd => alphaEquivFunDef fd parsed_call_and_write_invalid
    | none => false
  | .error _ => false
