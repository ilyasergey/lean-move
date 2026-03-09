/-
 Copyright Ilya Sergey
 Licensed under the Apache License, Version 2.0
-/

import LeanMove.Tests.Parsing.TestUtils
import LeanMove.Lang.Macros

/-! ## Parse Test: enum_valid_unpack_loop.mvir

Three modules: woo.h, o.h, k.h — all multi-block with loops.
These are accepted by Sui's bytecode verifier.
Testing block counts and verifying parse+translate succeeds.
-/

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Lang.MoveIR.Parser
open LeanMove.Lang.MoveIR.Translate
open LeanMove.Tests.Parsing.TestUtils

private def src :=
  include_str "../MVIR/enum_valid_unpack_loop.mvir"

#guard (parseMvir src).isOk
#guard (parseAndTranslate src).isOk
#guard (parseAndTranslate src).toOption.get!.length == 3

-- Verify block counts
#guard
  match findFunInModule (parseAndTranslate src).toOption.get! "woo" "h" with
  | some fd => fd.blocks.length == 6
  | none => false

#guard
  match findFunInModule (parseAndTranslate src).toOption.get! "o" "h" with
  | some fd => fd.blocks.length == 6
  | none => false

#guard
  match findFunInModule (parseAndTranslate src).toOption.get! "k" "h" with
  | some fd => fd.blocks.length == 5
  | none => false
