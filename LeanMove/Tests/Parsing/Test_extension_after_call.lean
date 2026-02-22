/-
 Copyright Ilya Sergey
 Licensed under the Apache License, Version 2.0
-/

import LeanMove.Tests.Parsing.TestUtils

/-! ## Parse Test: extension_after_call.mvir

Tests parsing of extension_after_call — writing to extension after a function call,
with struct definitions (Point, Box) and multiple functions.
-/

open LeanMove.Lang.MoveLight
open LeanMove.Lang.MoveIR.Parser
open LeanMove.Lang.MoveIR.Translate
open LeanMove.Tests.Parsing.TestUtils

def extensionAfterCallMvir :=
  include_str "../Typechecking/expressivity/accepted/extension_after_call.mvir"

-- Parse succeeds
#guard (parseMvir extensionAfterCallMvir).isOk

-- Translation succeeds
#guard (parseAndTranslate extensionAfterCallMvir).isOk

-- Check borrow function
#guard
  match parseAndTranslate extensionAfterCallMvir with
  | .ok results =>
    match findFun results "borrow" with
    | some fd =>
      fd.params.length == 1 &&
      fd.locals.length == 0 &&
      fd.returnType.length == 1 &&
      fd.blocks.length == 1
    | none => false
  | .error _ => false

-- Check write function
#guard
  match parseAndTranslate extensionAfterCallMvir with
  | .ok results =>
    match findFun results "write" with
    | some fd =>
      fd.params.length == 1 &&
      fd.locals.length == 3 &&
      fd.returnType.length == 1 &&
      fd.blocks.length == 1
    | none => false
  | .error _ => false

-- Note: alpha-equivalence with hand-written example is not tested because
-- the hand-written version uses different variable names (p → tl in fn_write)
-- and different parameter names (p → b in fn_borrow).
