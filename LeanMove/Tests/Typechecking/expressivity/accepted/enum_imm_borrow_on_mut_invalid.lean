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
# Enum Immutable Borrow on Mut Invalid

Both modules REJECTED by Sui.
Error types: FIELD_EXISTS_MUTABLE_BORROW_ERROR, FREEZEREF_EXISTS_MUTABLE_BORROW_ERROR

Two modules (0x42.Tester, 0x43.Tester):
- set_and_pick: multi-block (3 blocks)
- bump_and_give: single-block
- larger_field_1: single-block

Note: This file is in the accepted/ directory but its larger_field_1 functions should be REJECTED.

Source: enum_imm_borrow_on_mut_invalid.mvir
-/

namespace LeanMove.Tests.Expressivity.EnumImmBorrowOnMutInvalid

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Typing
open LeanMove.Tests.Parsing.TestUtils

private def src := include_str "enum_imm_borrow_on_mut_invalid.mvir"

#guard (parseAndTranslate src).isOk

private def parsedFuns := (parseAndTranslate src).toOption.get!

-- 6 functions across 2 modules
#guard parsedFuns.length == 6

-- Test single-block functions
-- Module 0x42: bump_and_give (index 1)
def parsed_bump1 := (findFunAt parsedFuns 1).get!
#guard parsed_bump1.blocks.length == 1

def bump1_lenvDec := mkLabelEnvDec parsed_bump1

theorem bump1_check :
  check_fun_dec parsed_bump1 bump1_lenvDec = true := by native_decide

theorem bump1_welltyped : ∃ lenv, typecheck_fun parsed_bump1 lenv :=
  ⟨_, check_fun_dec_sound _ _ bump1_check⟩

-- Module 0x43: bump_and_give (index 4)
def parsed_bump2 := (findFunAt parsedFuns 4).get!
#guard parsed_bump2.blocks.length == 1

def bump2_lenvDec := mkLabelEnvDec parsed_bump2

theorem bump2_check :
  check_fun_dec parsed_bump2 bump2_lenvDec = true := by native_decide

theorem bump2_welltyped : ∃ lenv, typecheck_fun parsed_bump2 lenv :=
  ⟨_, check_fun_dec_sound _ _ bump2_check⟩

end LeanMove.Tests.Expressivity.EnumImmBorrowOnMutInvalid
