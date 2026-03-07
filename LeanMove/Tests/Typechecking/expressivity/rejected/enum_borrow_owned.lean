/-
 Copyright Ilya Sergey
 Licensed under the Apache License, Version 2.0
-/

import LeanMove.Lang.MoveLight
import LeanMove.Typing.TypeChecking
import LeanMove.Typing.Algorithmic.DecidableTypeEnv
import LeanMove.Lang.Macros
import LeanMove.Tests.Parsing.TestUtils

/-!
# Enum Borrow Owned

One module: borrow_owned_enum.test — multi-block (18 blocks).
Borrows fields from an owned enum and then writes to the owned enum
while immutable borrows are outstanding.

Source: enum_borrow_owned.mvir
-/

namespace LeanMove.Tests.Expressivity.EnumBorrowOwned

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Typing
open LeanMove.Tests.Parsing.TestUtils

private def src := include_str "enum_borrow_owned.mvir"

#guard (parseAndTranslate src).isOk

private def parsedFuns := (parseAndTranslate src).toOption.get!

-- 1 function
#guard parsedFuns.length == 1

def parsed_test := (findFunAt parsedFuns 0).get!
#guard parsed_test.blocks.length == 17

-- Multi-block type checking — should be REJECTED
def test_lenvDec := mkLabelEnvDecAll parsed_test

theorem test_rejected :
  check_fun_dec parsed_test test_lenvDec = false := by native_decide

end LeanMove.Tests.Expressivity.EnumBorrowOwned
