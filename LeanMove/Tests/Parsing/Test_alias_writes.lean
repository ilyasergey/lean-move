/-
 Copyright Ilya Sergey
 Licensed under the Apache License, Version 2.0
-/

import LeanMove.Tests.Parsing.TestUtils
import LeanMove.Tests.Typechecking.expressivity.accepted.alias_writes

/-! ## Parse Test: alias_writes.mvir

Tests parsing and translation of the alias_writes Move IR example.
Four modules: borrow_local_twice, borrow_local_twice_reverse,
borrow_local_and_copy_ref, borrow_local_and_copy_ref_reverse.
-/

open LeanMove.Lang.MoveLight
open LeanMove.Lang.MoveIR.Parser
open LeanMove.Lang.MoveIR.Translate
open LeanMove.Tests.Parsing.TestUtils
open LeanMove.Tests.Expressivity.AliasWrites

def aliasWritesMvir :=
  include_str "../Typechecking/expressivity/accepted/alias_writes.mvir"

-- Parse succeeds
#guard (parseMvir aliasWritesMvir).isOk

-- Correct number of modules
#guard (parseMvir aliasWritesMvir).toOption.get!.modules.length == 4

-- Translation succeeds
#guard (parseAndTranslate aliasWritesMvir).isOk

-- Alpha-equivalence with hand-written examples
#guard
  match parseAndTranslate aliasWritesMvir with
  | .ok results =>
    match findFunInModule results "borrow_local_twice" "t" with
    | some fd => alphaEquivFunDef fd parsed_borrow_local_twice
    | none => false
  | .error _ => false

#guard
  match parseAndTranslate aliasWritesMvir with
  | .ok results =>
    match findFunInModule results "borrow_local_twice_reverse" "t" with
    | some fd => alphaEquivFunDef fd parsed_borrow_local_twice_reverse
    | none => false
  | .error _ => false

#guard
  match parseAndTranslate aliasWritesMvir with
  | .ok results =>
    match findFunInModule results "borrow_local_and_copy_ref" "t" with
    | some fd => alphaEquivFunDef fd parsed_borrow_local_and_copy_ref
    | none => false
  | .error _ => false

#guard
  match parseAndTranslate aliasWritesMvir with
  | .ok results =>
    match findFunInModule results "borrow_local_and_copy_ref_reverse" "t" with
    | some fd => alphaEquivFunDef fd parsed_borrow_local_and_copy_ref_reverse
    | none => false
  | .error _ => false
