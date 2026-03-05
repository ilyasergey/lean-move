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
# Enum Match

Tests basic variant_switch dispatch with packVariant and unpackVariant.
One module: m.t0

Source: enum_match.mvir

Note: Algorithmic type checking for enums is not yet complete
(packVariant builds a single-variant tenum instead of the full enum definition).
Parsing and translation tests only for now.
-/

namespace LeanMove.Tests.Expressivity.EnumMatch

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Typing
open LeanMove.Tests.Parsing.TestUtils

private def enumMatchMvir :=
  include_str "enum_match.mvir"

private def parsedFuns := (parseAndTranslate enumMatchMvir).toOption.get!

def parsed_t0 := (findFunInModule parsedFuns "m" "t0").get!

-- Verify parsing succeeds
#guard parsedFuns.length == 1
#guard parsed_t0.blocks.length == 5

-- TODO: Algorithmic type checking once packVariant produces full enum type
-- def t0_lenvDec := mkLabelEnvDec parsed_t0
-- theorem t0_check :
--   check_fun_dec parsed_t0 t0_lenvDec = true := by native_decide

end LeanMove.Tests.Expressivity.EnumMatch
