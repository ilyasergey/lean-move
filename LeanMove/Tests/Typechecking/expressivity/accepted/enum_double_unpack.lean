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
# Enum Double Unpack

Tests two successive mutable variant unpacks from the same reference.
One module: o.a, o.b (each single block)

Source: enum_double_unpack.mvir

Note: function `a` reuses field variables (x,y) across two unpacks without releasing
the old borrows before move(e). Our sequential translation model requires the old
borrows to be released first. Function `b` works because it moves y before the second
unpack, releasing its borrow.
-/

namespace LeanMove.Tests.Expressivity.EnumDoubleUnpack

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Typing
open LeanMove.Tests.Parsing.TestUtils

private def src := include_str "../../../MVIR/enum_double_unpack.mvir"

#guard (parseAndTranslateWithEnums src).isOk

private def parsedFuns : List (String × String × FunDef) :=
  match parseAndTranslateWithEnums src with
  | Except.ok (funs, _) => funs
  | Except.error _ => []

private def enumEnv : EnumEnv :=
  match parseAndTranslateWithEnums src with
  | Except.ok (_, ee) => ee
  | Except.error _ => ⟨[]⟩

-- Function a: reuses x,y across two unpacks. The var_assign_valid_ref rule
-- releases old borrows via delete_ref_node when reassigning ref-typed variables.
def parsed_a := (findFunInModule parsedFuns "o" "a").get!
#guard parsed_a.blocks.length == 1

def a_lenvDec := mkLabelEnvDec parsed_a (enumEnv := enumEnv)

theorem a_check :
  check_fun_dec parsed_a a_lenvDec enumEnv = true := by native_decide

theorem a_welltyped : ∃ lenv, typecheck_fun parsed_a lenv enumEnv :=
  ⟨_, check_fun_dec_sound _ _ _ a_check⟩

-- Function b: moves y between unpacks, releasing the borrow. Accepted.
def parsed_b := (findFunInModule parsedFuns "o" "b").get!

#guard parsed_b.blocks.length == 1

def b_lenvDec := mkLabelEnvDec parsed_b (enumEnv := enumEnv)

theorem b_check :
  check_fun_dec parsed_b b_lenvDec enumEnv = true := by native_decide

theorem b_welltyped : ∃ lenv, typecheck_fun parsed_b lenv enumEnv :=
  ⟨_, check_fun_dec_sound _ _ _ b_check⟩

end LeanMove.Tests.Expressivity.EnumDoubleUnpack
