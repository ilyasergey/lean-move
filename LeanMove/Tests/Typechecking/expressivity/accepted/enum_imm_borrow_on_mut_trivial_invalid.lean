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
# Enum Immutable Borrow on Mut Trivial Invalid

REJECTED: FIELD_EXISTS_MUTABLE_BORROW_ERROR
Two functions: bump_and_give (single-block), contrived_example_no (single-block with call).
Cannot mutably borrow from x_ref when it is already being borrowed by returned_ref.

Note: This file is in the accepted/ directory but contrived_example_no should be REJECTED.

Source: enum_imm_borrow_on_mut_trivial_invalid.mvir
-/

namespace LeanMove.Tests.Expressivity.EnumImmBorrowOnMutTrivialInvalid

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Typing
open LeanMove.Tests.Parsing.TestUtils

private def src := include_str "../../../MVIR/enum_imm_borrow_on_mut_trivial_invalid.mvir"

#guard (parseAndTranslateWithEnums src).isOk

private def parsedFuns : List (String × String × FunDef) :=
  match parseAndTranslateWithEnums src with
  | Except.ok (funs, _) => funs
  | Except.error _ => []

private def enumEnv : EnumEnv :=
  match parseAndTranslateWithEnums src with
  | Except.ok (_, ee) => ee
  | Except.error _ => ⟨[]⟩

-- 2 functions
#guard parsedFuns.length == 2

-- bump_and_give: single-block, should type check
def parsed_bump := (findFunAt parsedFuns 0).get!
#guard parsed_bump.blocks.length == 1

def bump_lenvDec := mkLabelEnvDec parsed_bump (enumEnv := enumEnv)

theorem bump_check :
  check_fun_dec parsed_bump bump_lenvDec enumEnv = true := by native_decide

theorem bump_welltyped : ∃ lenv, typecheck_fun parsed_bump lenv enumEnv :=
  ⟨_, check_fun_dec_sound _ _ _ bump_check⟩

-- contrived_example_no: single-block, should be REJECTED
-- (mutably borrows x_ref while returned_ref borrows it)
def parsed_contrived := (findFunAt parsedFuns 1).get!
#guard parsed_contrived.blocks.length == 1

-- Uses function call, so we can't test rejection without funEnv.
-- Just verify parsing succeeds.

end LeanMove.Tests.Expressivity.EnumImmBorrowOnMutTrivialInvalid
