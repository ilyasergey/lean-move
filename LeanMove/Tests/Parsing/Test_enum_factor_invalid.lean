/-
 Copyright Ilya Sergey
 Licensed under the Apache License, Version 2.0
-/

import LeanMove.Tests.Parsing.TestUtils
import LeanMove.Lang.Macros

/-! ## Parse Test: enum_factor_invalid.mvir

Alpha-equivalence tests for enum factor invalid (REJECTED).
Two functions: M.t1 (multi-block, 4 blocks), M.bar (single-block).
Testing M.bar (single-block) with alpha-equivalence.
-/

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Lang.MoveIR.Parser
open LeanMove.Lang.MoveIR.Translate
open LeanMove.Tests.Parsing.TestUtils

private def src :=
  include_str "../Typechecking/expressivity/accepted/enum_factor_invalid.mvir"

#guard (parseMvir src).isOk
#guard (parseAndTranslate src).isOk
#guard (parseAndTranslate src).toOption.get!.length == 2

-- ----------------------------------------------------------------
-- Common type definitions
-- ----------------------------------------------------------------

private def var_a : Var := ⟨"a"⟩
private def var_x : Var := ⟨"x"⟩
private def s (n : Nat) : Site := .site n

private def sVariants : AssocMap Id (AssocMap Field BasicMoveType) :=
  AssocMap.mk [("V", AssocMap.mk [(⟨"g"⟩, .u64)])]

private def sType : BasicMoveType := .tenum "S" sVariants

-- ----------------------------------------------------------------
-- M.bar: freeze → immutable unpack → return
-- ----------------------------------------------------------------

private def hw_bar : FunDef := {
  params := [(var_a, .ref sType (.paramRef var_a) .siteBorrowMut)]
  returnType := [⟨.u64, some false⟩]
  locals := [
    { name := var_x, type := .ref .u64 (.refid 1) .siteBorrowImm }
  ]
  blocks := [
    { label := "b0"
      body :=
        (letsite (s 0) ← move var_a) ;;
        (letsite (s 1) ← freeze (s 0)) ;;
        unpackVariant("V", [(⟨"g"⟩, (s 2))], (s 1)) ;;
        (var_x ::= (s 2)) ;;
        (letsite (s 3) ← move var_x) ;;
        ret [(s 3)]
    }
  ]
}

#guard
  match findFunInModule (parseAndTranslate src).toOption.get! "M" "bar" with
  | some fd => alphaEquivFunDef fd hw_bar
  | none => false

-- ----------------------------------------------------------------
-- M.t1: multi-block (4 blocks) — verify block count
-- ----------------------------------------------------------------

#guard
  match findFunInModule (parseAndTranslate src).toOption.get! "M" "t1" with
  | some fd => fd.blocks.length == 4
  | none => false
