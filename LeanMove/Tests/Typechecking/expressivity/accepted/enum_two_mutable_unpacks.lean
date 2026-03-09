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
# Enum Two Mutable Unpacks

Tests multiple mutable variant unpacks from the same reference.
One module: M.create_mutable_field_addresses (single block)

Source: enum_two_mutable_unpacks.mvir
-/

namespace LeanMove.Tests.Expressivity.EnumTwoMutableUnpacks

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Typing
open LeanMove.Tests.Parsing.TestUtils

private def src := include_str "enum_two_mutable_unpacks.mvir"

#guard (parseAndTranslateWithEnums src).isOk

private def parsedFuns : List (String × String × FunDef) :=
  match parseAndTranslateWithEnums src with
  | Except.ok (funs, _) => funs
  | Except.error _ => []

private def enumEnv : EnumEnv :=
  match parseAndTranslateWithEnums src with
  | Except.ok (_, ee) => ee
  | Except.error _ => ⟨[]⟩

def parsed_fn := (findFunInModule parsedFuns "M" "create_mutable_field_addresses").get!

-- Verify single block
#guard parsed_fn.blocks.length == 1

-- Algorithmic type checking
def fn_lenvDec := mkLabelEnvDec parsed_fn (enumEnv := enumEnv)

theorem fn_check :
  check_fun_dec parsed_fn fn_lenvDec enumEnv = true := by native_decide

theorem fn_welltyped : ∃ lenv, typecheck_fun parsed_fn lenv enumEnv :=
  ⟨_, check_fun_dec_sound _ _ _ fn_check⟩

end LeanMove.Tests.Expressivity.EnumTwoMutableUnpacks
