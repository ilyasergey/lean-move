/-
 Copyright Ilya Sergey
 Licensed under the Apache License, Version 2.0
-/

import LeanMove.Tests.Parsing.TestUtils
import LeanMove.Tests.Typechecking.expressivity.rejected.imm_borrow_after_mut_fields_invalid

/-! ## Parse Test: imm_borrow_after_mut_fields.mvir (REJECTED)

Tests parsing of imm_borrow_after_mut_fields — can borrow imm fields after a mut borrow,
but if the mut is a parent, it won't be writable.
Three modules: field (0x2), field (0x3), invalid_write (0x4).
-/

open LeanMove.Lang.MoveLight
open LeanMove.Lang.MoveIR.Parser
open LeanMove.Lang.MoveIR.Translate
open LeanMove.Tests.Parsing.TestUtils
open LeanMove.Tests.Expressivity.ImmBorrowAfterMutFieldsInvalid

def immBorrowAfterMutFieldsMvir :=
  include_str "../Typechecking/expressivity/rejected/imm_borrow_after_mut_fields.mvir"

-- Parse succeeds
#guard (parseMvir immBorrowAfterMutFieldsMvir).isOk

-- 3 modules
#guard (parseMvir immBorrowAfterMutFieldsMvir).toOption.get!.modules.length == 3

-- Translation succeeds
#guard (parseAndTranslate immBorrowAfterMutFieldsMvir).isOk

-- Alpha-equivalence: invalid_write module t function
#guard
  match parseAndTranslate immBorrowAfterMutFieldsMvir with
  | .ok results =>
    match findFunInModule results "invalid_write" "t" with
    | some fd => alphaEquivFunDef fd parsed_invalid_write
    | none => false
  | .error _ => false
