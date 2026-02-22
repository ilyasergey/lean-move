/-
 Copyright Ilya Sergey
 Licensed under the Apache License, Version 2.0
-/

import LeanMove.Tests.Parsing.TestUtils
import LeanMove.Tests.Typechecking.expressivity.accepted.mutable_borrows_are_not_unique

/-! ## Parse Test: mutable_borrows_are_not_unique.mvir

Tests parsing of mutable_borrows_are_not_unique — demonstrates that mutable borrows
are not unique, with nested struct field borrows. Two modules: fields (create) and
fields_write (write).
-/

open LeanMove.Lang.MoveLight
open LeanMove.Lang.MoveIR.Parser
open LeanMove.Lang.MoveIR.Translate
open LeanMove.Tests.Parsing.TestUtils
open LeanMove.Tests.Expressivity.MutableBorrowsNotUnique

def mutableBorrowsAreNotUniqueMvir :=
  include_str "../Typechecking/expressivity/accepted/mutable_borrows_are_not_unique.mvir"

-- Parse succeeds
#guard (parseMvir mutableBorrowsAreNotUniqueMvir).isOk

-- Translation succeeds
#guard (parseAndTranslate mutableBorrowsAreNotUniqueMvir).isOk

-- Alpha-equivalence with hand-written examples
#guard
  match parseAndTranslate mutableBorrowsAreNotUniqueMvir with
  | .ok results =>
    match findFunInModule results "fields" "create" with
    | some fd => alphaEquivFunDef fd parsed_fields
    | none => false
  | .error _ => false

#guard
  match parseAndTranslate mutableBorrowsAreNotUniqueMvir with
  | .ok results =>
    match findFunInModule results "fields_write" "write" with
    | some fd => alphaEquivFunDef fd parsed_fields_write
    | none => false
  | .error _ => false
