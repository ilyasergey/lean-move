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
# Enum Valid Ref Unpack

Tests various valid mutable and immutable variant unpack patterns.
One module: o.h, o.f, o.g, o.k, o.k1 (all single block)

Source: enum_valid_ref_unpack.mvir
-/

namespace LeanMove.Tests.Expressivity.EnumValidRefUnpack

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Typing
open LeanMove.Tests.Parsing.TestUtils

private def src := include_str "enum_valid_ref_unpack.mvir"

#guard (parseAndTranslateWithEnums src).isOk

private def parsedFuns : List (String × String × FunDef) :=
  match parseAndTranslateWithEnums src with
  | Except.ok (funs, _) => funs
  | Except.error _ => []

private def enumEnv : EnumEnv :=
  match parseAndTranslateWithEnums src with
  | Except.ok (_, ee) => ee
  | Except.error _ => ⟨[]⟩

def parsed_h := (findFunInModule parsedFuns "o" "h").get!
def parsed_f := (findFunInModule parsedFuns "o" "f").get!
def parsed_g := (findFunInModule parsedFuns "o" "g").get!

#guard parsed_h.blocks.length == 1
#guard parsed_f.blocks.length == 1
#guard parsed_g.blocks.length == 1

-- Algorithmic type checking
def h_lenvDec := mkLabelEnvDec parsed_h (enumEnv := enumEnv)
def f_lenvDec := mkLabelEnvDec parsed_f (enumEnv := enumEnv)
def g_lenvDec := mkLabelEnvDec parsed_g (enumEnv := enumEnv)

theorem h_check :
  check_fun_dec parsed_h h_lenvDec enumEnv = true := by native_decide

theorem f_check :
  check_fun_dec parsed_f f_lenvDec enumEnv = true := by native_decide

theorem g_check :
  check_fun_dec parsed_g g_lenvDec enumEnv = true := by native_decide

-- Relational Type Checking
theorem h_welltyped : ∃ lenv, typecheck_fun parsed_h lenv enumEnv :=
  ⟨_, check_fun_dec_sound _ _ _ h_check⟩

theorem f_welltyped : ∃ lenv, typecheck_fun parsed_f lenv enumEnv :=
  ⟨_, check_fun_dec_sound _ _ _ f_check⟩

theorem g_welltyped : ∃ lenv, typecheck_fun parsed_g lenv enumEnv :=
  ⟨_, check_fun_dec_sound _ _ _ g_check⟩

-- Functions k and k1: freeze + immutable unpack + release + writeRef via packVariant
-- The translator now emits release for `_ = move(x)` patterns, which properly
-- garbage-collects the immutable borrows before the writeRef.
def parsed_k := (findFunInModule parsedFuns "o" "k").get!
def parsed_k1 := (findFunInModule parsedFuns "o" "k1").get!

#guard parsed_k.blocks.length == 1
#guard parsed_k1.blocks.length == 1

def k_lenvDec := mkLabelEnvDec parsed_k (enumEnv := enumEnv)
def k1_lenvDec := mkLabelEnvDec parsed_k1 (enumEnv := enumEnv)

theorem k_check :
  check_fun_dec parsed_k k_lenvDec enumEnv = true := by native_decide

theorem k1_check :
  check_fun_dec parsed_k1 k1_lenvDec enumEnv = true := by native_decide

theorem k_welltyped : ∃ lenv, typecheck_fun parsed_k lenv enumEnv :=
  ⟨_, check_fun_dec_sound _ _ _ k_check⟩

theorem k1_welltyped : ∃ lenv, typecheck_fun parsed_k1 lenv enumEnv :=
  ⟨_, check_fun_dec_sound _ _ _ k1_check⟩

end LeanMove.Tests.Expressivity.EnumValidRefUnpack
