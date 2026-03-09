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
# Enum Factor Invalid

REJECTED: FIELD_EXISTS_MUTABLE_BORROW_ERROR
Two functions: M.t1 (multi-block), M.bar (single-block).
Root has weak empty borrow so a field cannot be borrowed mutably.

Note: This file is in the accepted/ directory but its functions should be REJECTED.

Source: enum_factor_invalid.mvir
-/

namespace LeanMove.Tests.Expressivity.EnumFactorInvalid

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Typing
open LeanMove.Tests.Parsing.TestUtils

private def src := include_str "../../../MVIR/enum_factor_invalid.mvir"

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

-- M.bar is single-block — test type checking
def parsed_bar := (findFunInModule parsedFuns "M" "bar").get!
#guard parsed_bar.blocks.length == 1

def bar_lenvDec := mkLabelEnvDec parsed_bar (enumEnv := enumEnv)

theorem bar_check :
  check_fun_dec parsed_bar bar_lenvDec enumEnv = true := by native_decide

theorem bar_welltyped : ∃ lenv, typecheck_fun parsed_bar lenv enumEnv :=
  ⟨_, check_fun_dec_sound _ _ _ bar_check⟩

-- M.t1 is multi-block (4 blocks)
def parsed_t1 := (findFunInModule parsedFuns "M" "t1").get!
#guard parsed_t1.blocks.length == 4

-- M.t1 uses a function call to M.bar, so we need a funEnv
-- For now, test with mkLabelEnvDecAll (no funEnv)
def t1_lenvDec := mkLabelEnvDecAll parsed_t1

-- M.t1 should be rejected (borrows field of root that has weak empty borrow)
-- Without funEnv for the call, the checker may behave differently
#guard !check_fun_dec parsed_t1 t1_lenvDec enumEnv

end LeanMove.Tests.Expressivity.EnumFactorInvalid
