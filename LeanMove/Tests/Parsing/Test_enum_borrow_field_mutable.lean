/-
 Copyright Ilya Sergey
 Licensed under the Apache License, Version 2.0
-/

import LeanMove.Tests.Parsing.TestUtils
import LeanMove.Lang.Macros

/-! ## Parse Test: enum_borrow_field_mutable.mvir

Alpha-equivalence tests for enum borrow field mutable.
Three modules: M (foo), M1 (foo, bar), M2 (foo, bar, baz).
Testing M1.bar and M2.baz (single-block) with alpha-equivalence.
Multi-block functions verified by block count.
-/

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Lang.MoveIR.Parser
open LeanMove.Lang.MoveIR.Translate
open LeanMove.Tests.Parsing.TestUtils

private def src :=
  include_str "../Typechecking/expressivity/accepted/enum_borrow_field_mutable.mvir"

#guard (parseMvir src).isOk
#guard (parseAndTranslate src).isOk
#guard (parseAndTranslate src).toOption.get!.length == 6

-- ----------------------------------------------------------------
-- Common type definitions
-- ----------------------------------------------------------------

private def var_a : Var := ⟨"a"⟩
private def var_x : Var := ⟨"x"⟩
private def s (n : Nat) : Site := .site n

private def eVariants : AssocMap Id (AssocMap Field BasicMoveType) :=
  AssocMap.mk [("V", AssocMap.mk [(⟨"f0"⟩, .u64)])]

private def eType : BasicMoveType := .tenum "E" eVariants

-- ----------------------------------------------------------------
-- M1.bar: &mut unpackVariant with field "g" → return
-- ----------------------------------------------------------------

private def hw_M1_bar : FunDef := {
  params := [(var_a, .ref eType (.paramRef var_a) .siteBorrowMut)]
  returnType := [⟨.u64, some true⟩]
  locals := [
    { name := var_x, type := .ref .u64 (.refid 1) .siteBorrowMut }
  ]
  blocks := [
    { label := "b0"
      body :=
        (letsite (s 0) ← move var_a) ;;
        unpackVariant("V", [(⟨"g"⟩, (s 1))], (s 0)) ;;
        (var_x ::= (s 1)) ;;
        (letsite (s 2) ← move var_x) ;;
        ret [(s 2)]
    }
  ]
}

#guard
  match findFunInModule (parseAndTranslate src).toOption.get! "M1" "bar" with
  | some fd => alphaEquivFunDef fd hw_M1_bar
  | none => false

-- ----------------------------------------------------------------
-- M2.baz: trivial function (just returns)
-- ----------------------------------------------------------------

private def var_baz_x : Var := ⟨"x"⟩

private def hw_M2_baz : FunDef := {
  params := [(var_baz_x, .ref .u64 (.paramRef var_baz_x) .siteBorrowMut)]
  returnType := []
  locals := []
  blocks := [
    { label := "b0"
      body := ret []
    }
  ]
}

#guard
  match findFunInModule (parseAndTranslate src).toOption.get! "M2" "baz" with
  | some fd => alphaEquivFunDef fd hw_M2_baz
  | none => false

-- ----------------------------------------------------------------
-- Multi-block functions: verify block counts
-- ----------------------------------------------------------------

#guard
  match findFunInModule (parseAndTranslate src).toOption.get! "M" "foo" with
  | some fd => fd.blocks.length == 4
  | none => false

#guard
  match findFunInModule (parseAndTranslate src).toOption.get! "M1" "foo" with
  | some fd => fd.blocks.length == 4
  | none => false

#guard
  match findFunInModule (parseAndTranslate src).toOption.get! "M2" "foo" with
  | some fd => fd.blocks.length == 4
  | none => false
