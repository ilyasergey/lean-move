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
# Enum Invalid Ref Unpack

All 7 modules REJECTED by Sui bytecode verifier.
Error types: WRITEREF_EXISTS_BORROW_ERROR, CALL_BORROWED_MUTABLE_REFERENCE_ERROR

Source: enum_invalid_ref_unpack.mvir

Function index mapping (10 total, some modules have `overwrite` helper):
  0: m1 (o.i)          — *move(e) while fields borrowed
  1: m2 (o.i)          — Self.overwrite(move(e)) while fields borrowed
  2: m2.overwrite
  3: m3 (o.j)          — *copy(e) while x borrowed (writeRef)
  4: m4 (o.j)          — Self.overwrite(copy(e)) while fields borrowed
  5: m4.overwrite
  6: m5 (o.k)          — *copy(e) while y borrowed (writeRef)
  7: m6 (o.k)          — *move(e) after freeze+unpack (immutable borrows)
  8: m7 (o.k)          — Self.overwrite(move(e)) after freeze+unpack
  9: m7.overwrite
-/

namespace LeanMove.Tests.Expressivity.EnumInvalidRefUnpack

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Typing
open LeanMove.Tests.Parsing.TestUtils

private def src := include_str "../../../MVIR/enum_invalid_ref_unpack.mvir"

#guard (parseAndTranslate src).isOk

private def parsedFuns := (parseAndTranslate src).toOption.get!

#guard parsedFuns.length == 10

-- Parse all 7 main functions (skipping overwrite helpers)
def parsed_m1 := (findFunAt parsedFuns 0).get!  -- o.i (module 1)
def parsed_m2 := (findFunAt parsedFuns 1).get!  -- o.i (module 2)
def parsed_m3 := (findFunAt parsedFuns 3).get!  -- o.j (module 3)
def parsed_m4 := (findFunAt parsedFuns 4).get!  -- o.j (module 4)
def parsed_m5 := (findFunAt parsedFuns 6).get!  -- o.k (module 5)
def parsed_m6 := (findFunAt parsedFuns 7).get!  -- o.k (module 6)
def parsed_m7 := (findFunAt parsedFuns 8).get!  -- o.k (module 7)

-- All single-block
#guard parsed_m1.blocks.length == 1
#guard parsed_m2.blocks.length == 1
#guard parsed_m3.blocks.length == 1
#guard parsed_m4.blocks.length == 1
#guard parsed_m5.blocks.length == 1
#guard parsed_m6.blocks.length == 1
#guard parsed_m7.blocks.length == 1

-- Label envs
def m1_lenvDec := mkLabelEnvDec parsed_m1
def m2_lenvDec := mkLabelEnvDec parsed_m2
def m3_lenvDec := mkLabelEnvDec parsed_m3
def m4_lenvDec := mkLabelEnvDec parsed_m4
def m5_lenvDec := mkLabelEnvDec parsed_m5
def m6_lenvDec := mkLabelEnvDec parsed_m6
def m7_lenvDec := mkLabelEnvDec parsed_m7

-- m1: *move(e) while fields borrowed — REJECTED
theorem m1_rejected :
  check_fun_dec parsed_m1 m1_lenvDec = false := by native_decide

-- m2: Self.overwrite(move(e)) while fields borrowed — REJECTED (no funEnv)
theorem m2_rejected :
  check_fun_dec parsed_m2 m2_lenvDec = false := by native_decide

-- m3: *copy(e) while x borrowed — REJECTED
theorem m3_rejected :
  check_fun_dec parsed_m3 m3_lenvDec = false := by native_decide

-- m4: Self.overwrite(copy(e)) while fields borrowed — REJECTED (no funEnv)
theorem m4_rejected :
  check_fun_dec parsed_m4 m4_lenvDec = false := by native_decide

-- m5: *copy(e) while y borrowed — REJECTED
theorem m5_rejected :
  check_fun_dec parsed_m5 m5_lenvDec = false := by native_decide

-- m6: *move(e) after freeze+unpack, immutable borrows alive — REJECTED
theorem m6_rejected :
  check_fun_dec parsed_m6 m6_lenvDec = false := by native_decide

-- m7: Self.overwrite(move(e)) after freeze+unpack — REJECTED (no funEnv)
theorem m7_rejected :
  check_fun_dec parsed_m7 m7_lenvDec = false := by native_decide

end LeanMove.Tests.Expressivity.EnumInvalidRefUnpack
