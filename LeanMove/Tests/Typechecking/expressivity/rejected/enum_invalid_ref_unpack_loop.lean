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
# Enum Invalid Ref Unpack Loop

All 5 modules REJECTED by Sui.
Error types: WRITEREF_EXISTS_BORROW_ERROR, COPYLOC_UNAVAILABLE_ERROR

All functions are multi-block with loops. References stay live between
loop iterations while their roots are written to.

Source: enum_invalid_ref_unpack_loop.mvir
-/

namespace LeanMove.Tests.Expressivity.EnumInvalidRefUnpackLoop

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Typing
open LeanMove.Tests.Parsing.TestUtils

private def src := include_str "../../../MVIR/enum_invalid_ref_unpack_loop.mvir"

#guard (parseAndTranslateWithEnums src).isOk

private def parsedFuns : List (String × String × FunDef) :=
  match parseAndTranslateWithEnums src with
  | Except.ok (funs, _) => funs
  | Except.error _ => []

private def enumEnv : EnumEnv :=
  match parseAndTranslateWithEnums src with
  | Except.ok (_, ee) => ee
  | Except.error _ => ⟨[]⟩

-- 5 functions across 5 modules
#guard parsedFuns.length == 5

-- All multi-block — verify block counts
def parsed_h0 := (findFunAt parsedFuns 0).get!
def parsed_h1 := (findFunAt parsedFuns 1).get!
def parsed_h2 := (findFunAt parsedFuns 2).get!
def parsed_h3 := (findFunAt parsedFuns 3).get!
def parsed_h4 := (findFunAt parsedFuns 4).get!

#guard parsed_h0.blocks.length == 6
#guard parsed_h1.blocks.length == 6
#guard parsed_h2.blocks.length == 6
#guard parsed_h3.blocks.length == 6
#guard parsed_h4.blocks.length == 6

-- Multi-block type checking — all should be REJECTED
def h0_lenvDec := mkLabelEnvDecAll parsed_h0
def h1_lenvDec := mkLabelEnvDecAll parsed_h1
def h2_lenvDec := mkLabelEnvDecAll parsed_h2
def h3_lenvDec := mkLabelEnvDecAll parsed_h3
def h4_lenvDec := mkLabelEnvDecAll parsed_h4

theorem h0_rejected :
  check_fun_dec parsed_h0 h0_lenvDec enumEnv = false := by native_decide

theorem h1_rejected :
  check_fun_dec parsed_h1 h1_lenvDec enumEnv = false := by native_decide

theorem h2_accepted :
  check_fun_dec parsed_h2 h2_lenvDec enumEnv = false := by native_decide

theorem h3_rejected :
  check_fun_dec parsed_h3 h3_lenvDec enumEnv = false := by native_decide

theorem h4_rejected :
  check_fun_dec parsed_h4 h4_lenvDec enumEnv = false := by native_decide

end LeanMove.Tests.Expressivity.EnumInvalidRefUnpackLoop
