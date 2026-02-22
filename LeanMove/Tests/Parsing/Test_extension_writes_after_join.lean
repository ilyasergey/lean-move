/-
 Copyright Ilya Sergey
 Licensed under the Apache License, Version 2.0
-/

import LeanMove.Tests.Parsing.TestUtils
import LeanMove.Tests.Typechecking.expressivity.accepted.extension_writes_after_join

/-! ## Parse Test: extension_writes_after_join.mvir

Tests parsing of extension_writes_after_join — writing to extension after join
with struct S and conditional branching.
-/

open LeanMove.Lang.MoveLight
open LeanMove.Lang.MoveIR.Parser
open LeanMove.Lang.MoveIR.Translate
open LeanMove.Tests.Parsing.TestUtils
open LeanMove.Tests.Expressivity.ExtensionWritesAfterJoin

def extensionWritesAfterJoinMvir :=
  include_str "../Typechecking/expressivity/accepted/extension_writes_after_join.mvir"

-- Parse succeeds
#guard (parseMvir extensionWritesAfterJoinMvir).isOk

-- Translation succeeds
#guard (parseAndTranslate extensionWritesAfterJoinMvir).isOk

-- Alpha-equivalence with hand-written example
#guard
  match parseAndTranslate extensionWritesAfterJoinMvir with
  | .ok results =>
    match findFun results "t" with
    | some fd => alphaEquivFunDef fd parsed_t
    | none => false
  | .error _ => false
