/-
 Copyright Ilya Sergey
 Licensed under the Apache License, Version 2.0
-/

import LeanMove.Tests.Parsing.TestUtils
import LeanMove.Tests.Typechecking.expressivity.rejected.imm_borrow_after_mut_call_invalid

/-! ## Parse Test: imm_borrow_after_mut_call.mvir (REJECTED)

Tests parsing of imm_borrow_after_mut_call — can create an immutable extension
via a call after a mut borrow, but if the mut is a parent, it won't be writable.
Two modules: valid and invalid.
-/

open LeanMove.Lang.MoveLight
open LeanMove.Lang.MoveIR.Parser
open LeanMove.Lang.MoveIR.Translate
open LeanMove.Tests.Parsing.TestUtils
open LeanMove.Tests.Expressivity.ImmBorrowAfterMutCallInvalid

def immBorrowAfterMutCallMvir :=
  include_str "../Typechecking/expressivity/rejected/imm_borrow_after_mut_call.mvir"

-- Parse succeeds
#guard (parseMvir immBorrowAfterMutCallMvir).isOk

-- 2 modules
#guard (parseMvir immBorrowAfterMutCallMvir).toOption.get!.modules.length == 2

-- Translation succeeds
#guard (parseAndTranslate immBorrowAfterMutCallMvir).isOk

-- Alpha-equivalence: invalid module t function
#guard
  match parseAndTranslate immBorrowAfterMutCallMvir with
  | .ok results =>
    match findFunInModule results "invalid" "t" with
    | some fd => alphaEquivFunDef fd parsed_invalid
    | none => false
  | .error _ => false
