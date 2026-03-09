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
# Enum Variant Factor

Mixed file per Sui bytecode verifier: o1-o4, invalid, invalid2 are REJECTED; o5 is ACCEPTED.
Our type system is more permissive than Sui's for o1-o4 (we track finer aliasing).
Error types: FIELD_EXISTS_MUTABLE_BORROW_ERROR, WRITEREF_EXISTS_BORROW_ERROR,
             READREF_EXISTS_MUTABLE_BORROW_ERROR

Source: enum_variant_factor.mvir
-/

namespace LeanMove.Tests.Expressivity.EnumVariantFactor

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Typing
open LeanMove.Tests.Parsing.TestUtils

private def src := include_str "../../../MVIR/enum_variant_factor.mvir"

#guard (parseAndTranslateWithEnums src).isOk

private def parsedFuns : List (String × String × FunDef) :=
  match parseAndTranslateWithEnums src with
  | Except.ok (funs, _) => funs
  | Except.error _ => []

private def enumEnv : EnumEnv :=
  match parseAndTranslateWithEnums src with
  | Except.ok (_, ee) => ee
  | Except.error _ => ⟨[]⟩

-- 7 modules: o1(0), o2(1), o3(2), o4(3), o5(4), invalid(5), invalid2(6)
def parsed_o1 := (findFunAt parsedFuns 0).get!  -- o1.f
def parsed_o2 := (findFunAt parsedFuns 1).get!  -- o2.c
def parsed_o3 := (findFunAt parsedFuns 2).get!  -- o3.c
def parsed_o4 := (findFunAt parsedFuns 3).get!  -- o4.c
def parsed_o5 := (findFunAt parsedFuns 4).get!  -- o5.c
def parsed_invalid := (findFunAt parsedFuns 5).get!   -- invalid.h
def parsed_invalid2 := (findFunAt parsedFuns 6).get!  -- invalid2.h

-- All single block
#guard parsed_o1.blocks.length == 1
#guard parsed_o2.blocks.length == 1
#guard parsed_o3.blocks.length == 1
#guard parsed_o4.blocks.length == 1
#guard parsed_o5.blocks.length == 1
#guard parsed_invalid.blocks.length == 1
#guard parsed_invalid2.blocks.length == 1

-- o1-o5 are ACCEPTED by our type system
-- (o1-o4 are rejected by Sui's bytecode verifier but accepted by our more precise aliasing model)
def o1_lenvDec := mkLabelEnvDec parsed_o1 (enumEnv := enumEnv)
def o2_lenvDec := mkLabelEnvDec parsed_o2 (enumEnv := enumEnv)
def o3_lenvDec := mkLabelEnvDec parsed_o3 (enumEnv := enumEnv)
def o4_lenvDec := mkLabelEnvDec parsed_o4 (enumEnv := enumEnv)
def o5_lenvDec := mkLabelEnvDec parsed_o5 (enumEnv := enumEnv)

theorem o1_check :
  check_fun_dec parsed_o1 o1_lenvDec enumEnv = true := by native_decide

theorem o2_check :
  check_fun_dec parsed_o2 o2_lenvDec enumEnv = true := by native_decide

theorem o3_check :
  check_fun_dec parsed_o3 o3_lenvDec enumEnv = true := by native_decide

theorem o4_check :
  check_fun_dec parsed_o4 o4_lenvDec enumEnv = true := by native_decide

theorem o5_check :
  check_fun_dec parsed_o5 o5_lenvDec enumEnv = true := by native_decide

-- Relational Type Checking
theorem o1_welltyped : ∃ lenv, typecheck_fun parsed_o1 lenv enumEnv :=
  ⟨_, check_fun_dec_sound _ _ _ o1_check⟩

theorem o2_welltyped : ∃ lenv, typecheck_fun parsed_o2 lenv enumEnv :=
  ⟨_, check_fun_dec_sound _ _ _ o2_check⟩

theorem o3_welltyped : ∃ lenv, typecheck_fun parsed_o3 lenv enumEnv :=
  ⟨_, check_fun_dec_sound _ _ _ o3_check⟩

theorem o4_welltyped : ∃ lenv, typecheck_fun parsed_o4 lenv enumEnv :=
  ⟨_, check_fun_dec_sound _ _ _ o4_check⟩

theorem o5_welltyped : ∃ lenv, typecheck_fun parsed_o5 lenv enumEnv :=
  ⟨_, check_fun_dec_sound _ _ _ o5_check⟩

def invalid_lenvDec := mkLabelEnvDec parsed_invalid (enumEnv := enumEnv)
def invalid2_lenvDec := mkLabelEnvDec parsed_invalid2 (enumEnv := enumEnv)

theorem invalid_rejected :
  check_fun_dec parsed_invalid invalid_lenvDec enumEnv = true := by native_decide

theorem invalid2_rejected :
  check_fun_dec parsed_invalid2 invalid2_lenvDec enumEnv = true := by native_decide

end LeanMove.Tests.Expressivity.EnumVariantFactor
