/-
 Copyright Ilya Sergey
 Licensed under the Apache License, Version 2.0
-/

import LeanMove.Tests.Parsing.TestUtils
import LeanMove.Lang.Macros

/-! ## Parse Test: enum_invalid_ref_unpack_loop.mvir

All 5 modules REJECTED by Sui. All multi-block with loops.
Testing block counts and verifying parse+translate succeeds.
-/

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Lang.MoveIR.Parser
open LeanMove.Lang.MoveIR.Translate
open LeanMove.Tests.Parsing.TestUtils

private def src :=
  include_str "../Typechecking/expressivity/rejected/enum_invalid_ref_unpack_loop.mvir"

#guard (parseMvir src).isOk
#guard (parseAndTranslate src).isOk
#guard (parseAndTranslate src).toOption.get!.length == 5

-- All multi-block, verify block counts
#guard
  match findFunAt (parseAndTranslate src).toOption.get! 0 with
  | some fd => fd.blocks.length == 6
  | none => false

#guard
  match findFunAt (parseAndTranslate src).toOption.get! 1 with
  | some fd => fd.blocks.length == 6
  | none => false

#guard
  match findFunAt (parseAndTranslate src).toOption.get! 2 with
  | some fd => fd.blocks.length == 6
  | none => false

#guard
  match findFunAt (parseAndTranslate src).toOption.get! 3 with
  | some fd => fd.blocks.length == 6
  | none => false

#guard
  match findFunAt (parseAndTranslate src).toOption.get! 4 with
  | some fd => fd.blocks.length == 6
  | none => false
