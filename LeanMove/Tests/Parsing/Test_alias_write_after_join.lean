/-
 Copyright Ilya Sergey
 Licensed under the Apache License, Version 2.0
-/

import LeanMove.Tests.Parsing.TestUtils
import LeanMove.Tests.Typechecking.expressivity.accepted.alias_write_after_join

/-! ## Parse Test: alias_write_after_join.mvir

Tests parsing of alias_write_after_join — writing to alias after join with branching.
-/

open LeanMove.Lang.MoveLight
open LeanMove.Lang.MoveIR.Parser
open LeanMove.Lang.MoveIR.Translate
open LeanMove.Tests.Parsing.TestUtils
open LeanMove.Tests.Expressivity.AliasWriteAfterJoin

def aliasWriteAfterJoinMvir :=
  include_str "../Typechecking/expressivity/accepted/alias_write_after_join.mvir"

-- Parse succeeds
#guard (parseMvir aliasWriteAfterJoinMvir).isOk

-- Translation succeeds
#guard (parseAndTranslate aliasWriteAfterJoinMvir).isOk

-- Alpha-equivalence with hand-written example
#guard
  match parseAndTranslate aliasWriteAfterJoinMvir with
  | .ok results =>
    match findFun results "t" with
    | some fd => alphaEquivFunDef fd parsed_t
    | none => false
  | .error _ => false
