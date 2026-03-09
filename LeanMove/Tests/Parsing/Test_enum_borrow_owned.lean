/-
 Copyright Ilya Sergey
 Licensed under the Apache License, Version 2.0
-/

import LeanMove.Tests.Parsing.TestUtils
import LeanMove.Lang.Macros

/-! ## Parse Test: enum_borrow_owned.mvir

One module: borrow_owned_enum.test — multi-block (17 blocks).
Borrows fields from an owned enum while immutable borrows are outstanding.
REJECTED by Sui.
-/

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Lang.MoveIR.Parser
open LeanMove.Lang.MoveIR.Translate
open LeanMove.Tests.Parsing.TestUtils

private def src :=
  include_str "../MVIR/enum_borrow_owned.mvir"

#guard (parseMvir src).isOk
#guard (parseAndTranslate src).isOk
#guard (parseAndTranslate src).toOption.get!.length == 1

-- Multi-block (17 blocks) — verify block count
#guard
  match findFunAt (parseAndTranslate src).toOption.get! 0 with
  | some fd => fd.blocks.length == 17
  | none => false
