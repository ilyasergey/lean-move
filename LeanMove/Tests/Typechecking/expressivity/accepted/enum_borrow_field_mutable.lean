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
# Enum Borrow Field Mutable

Three modules: M (foo), M1 (foo, bar), M2 (foo, bar, baz).
Multi-block functions with enum variant unpacking, branching, freeze.

Source: enum_borrow_field_mutable.mvir
-/

namespace LeanMove.Tests.Expressivity.EnumBorrowFieldMutable

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Typing
open LeanMove.Tests.Parsing.TestUtils

private def src := include_str "../../../MVIR/enum_borrow_field_mutable.mvir"

#guard (parseAndTranslateWithEnums src).isOk

private def parsedFuns : List (String × String × FunDef) :=
  match parseAndTranslateWithEnums src with
  | Except.ok (funs, _) => funs
  | Except.error _ => []

def enumEnv : EnumEnv :=
  match parseAndTranslateWithEnums src with
  | Except.ok (_, ee) => ee
  | Except.error _ => ⟨[]⟩

-- 6 functions across 3 modules
#guard parsedFuns.length == 6

-- M1.bar is single-block but uses mismatched field name (g vs f0) — not type-checkable
def parsed_M1_bar := (findFunInModule parsedFuns "M1" "bar").get!
#guard parsed_M1_bar.blocks.length == 1

-- M2.bar same issue
def parsed_M2_bar := (findFunInModule parsedFuns "M2" "bar").get!
#guard parsed_M2_bar.blocks.length == 1

-- M2.baz is single-block and type checks
def parsed_M2_baz := (findFunInModule parsedFuns "M2" "baz").get!
#guard parsed_M2_baz.blocks.length == 1

def M2_baz_lenvDec := mkLabelEnvDec parsed_M2_baz (enumEnv := enumEnv)

theorem M2_baz_check :
  check_fun_dec parsed_M2_baz M2_baz_lenvDec enumEnv = true := by native_decide

theorem M2_baz_welltyped : ∃ lenv, typecheck_fun parsed_M2_baz lenv enumEnv :=
  ⟨_, check_fun_dec_sound _ _ _ M2_baz_check⟩

-- M.foo is multi-block (4 blocks): start→branch, f→jump end, t→fall through end, end→return
def parsed_M_foo := (findFunInModule parsedFuns "M" "foo").get!
#guard parsed_M_foo.blocks.length == 4

def M_foo_lenvDec := mkLabelEnvDecAll parsed_M_foo

-- M.foo type-checking attempt with mkLabelEnvDecAll
#guard !check_fun_dec parsed_M_foo M_foo_lenvDec enumEnv
-- mkLabelEnvDecAll doesn't produce precise enough label envs for multi-block branching

end LeanMove.Tests.Expressivity.EnumBorrowFieldMutable
