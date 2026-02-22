/-
 Copyright Ilya Sergey
 Licensed under the Apache License, Version 2.0
-/

import LeanMove.Tests.Parsing.TestUtils
import LeanMove.Tests.Typechecking.expressivity.accepted.imm_borrow_after_mut

/-! ## Parse Test: imm_borrow_after_mut.mvir

Tests parsing of imm_borrow_after_mut — can borrow immutable after mutable.
Two modules: direct and copy_and_freeze.
-/

open LeanMove.Lang.MoveLight
open LeanMove.Lang.MoveIR.Parser
open LeanMove.Lang.MoveIR.Translate
open LeanMove.Tests.Parsing.TestUtils
open LeanMove.Tests.Expressivity.ImmBorrowAfterMut

def immBorrowAfterMutMvir :=
  include_str "../Typechecking/expressivity/accepted/imm_borrow_after_mut.mvir"

-- Parse succeeds
#guard (parseMvir immBorrowAfterMutMvir).isOk

-- Translation succeeds
#guard (parseAndTranslate immBorrowAfterMutMvir).isOk

-- Alpha-equivalence with hand-written examples
#guard
  match parseAndTranslate immBorrowAfterMutMvir with
  | .ok results =>
    match findFunInModule results "direct" "t" with
    | some fd => alphaEquivFunDef fd parsed_direct
    | none => false
  | .error _ => false

#guard
  match parseAndTranslate immBorrowAfterMutMvir with
  | .ok results =>
    match findFunInModule results "copy_and_freeze" "t" with
    | some fd => alphaEquivFunDef fd parsed_copy_and_freeze
    | none => false
  | .error _ => false
