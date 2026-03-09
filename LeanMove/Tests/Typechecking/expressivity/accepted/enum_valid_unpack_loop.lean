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
# Enum Valid Unpack Loop

Three modules: woo.h, o.h, k.h — all multi-block with loops.
These are accepted by Sui's bytecode verifier.

Source: enum_valid_unpack_loop.mvir

**Limitation**: The translator does not yet handle sequential `jump_if` statements
correctly — it produces `branch cond L L` with both targets identical instead of
creating intermediate blocks for multi-way branching. This prevents these functions
from type-checking even with manual label envs.
-/

namespace LeanMove.Tests.Expressivity.EnumValidUnpackLoop

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Typing
open LeanMove.Tests.Parsing.TestUtils

private def src := include_str "../../../MVIR/enum_valid_unpack_loop.mvir"

#guard (parseAndTranslate src).isOk

private def parsedFuns := (parseAndTranslate src).toOption.get!

-- 3 functions across 3 modules
#guard parsedFuns.length == 3

-- All multi-block
def parsed_woo_h := (findFunInModule parsedFuns "woo" "h").get!
def parsed_o_h := (findFunInModule parsedFuns "o" "h").get!
def parsed_k_h := (findFunInModule parsedFuns "k" "h").get!

#guard parsed_woo_h.blocks.length == 6
#guard parsed_o_h.blocks.length == 6
#guard parsed_k_h.blocks.length == 5

-- Multi-block type checking with mkLabelEnvDecAll (known to fail):
-- 1. Sequential jump_if translation produces degenerate branches (both targets same)
-- 2. mkLabelEnvDecAll doesn't produce precise enough varEnv for loop targets
def woo_h_lenvDec := mkLabelEnvDecAll parsed_woo_h
def o_h_lenvDec := mkLabelEnvDecAll parsed_o_h
def k_h_lenvDec := mkLabelEnvDecAll parsed_k_h

#guard !check_fun_dec parsed_woo_h woo_h_lenvDec
#guard !check_fun_dec parsed_o_h o_h_lenvDec
#guard !check_fun_dec parsed_k_h k_h_lenvDec

end LeanMove.Tests.Expressivity.EnumValidUnpackLoop
