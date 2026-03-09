/-
 Copyright Ilya Sergey
 Licensed under the Apache License, Version 2.0
-/

import LeanMove.Tests.Parsing.TestUtils
import LeanMove.Lang.Macros

/-! ## Parse Test: enum_variant_factor.mvir

Alpha-equivalence tests for enum variant factor patterns.
7 modules: o1.f, o2.c, o3.c, o4.c, o5.c, invalid.h, invalid2.h
All single-block. Testing o5.c and invalid.h as representatives.
-/

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Lang.MoveIR.Parser
open LeanMove.Lang.MoveIR.Translate
open LeanMove.Tests.Parsing.TestUtils

private def src :=
  include_str "../Typechecking/expressivity/accepted/enum_variant_factor.mvir"

#guard (parseMvir src).isOk
#guard (parseAndTranslate src).isOk
#guard (parseAndTranslate src).toOption.get!.length == 7

-- ----------------------------------------------------------------
-- Common type definitions
-- ----------------------------------------------------------------

private def var_e : Var := ⟨"e"⟩
private def var_a1 : Var := ⟨"a1"⟩
private def var_a2 : Var := ⟨"a2"⟩
private def var_x : Var := ⟨"x"⟩
private def var_y : Var := ⟨"y"⟩
private def s (n : Nat) : Site := .site n

private def xType : BasicMoveType := .tenum "o1.X"

-- ----------------------------------------------------------------
-- o1.f (index 0): copy+copy of same &mut ref
-- ----------------------------------------------------------------

private def hw_o1_f : FunDef := {
  params := [(var_e, .ref xType (.paramRef var_e) .siteBorrowMut)]
  returnType := []
  locals := [
    { name := var_a1, type := .ref xType (.refid 1) .siteBorrowMut },
    { name := var_a2, type := .ref xType (.refid 2) .siteBorrowMut }
  ]
  blocks := [
    { label := "b0"
      body :=
        (letsite (s 0) ← copy var_e) ;;
        (var_a1 ::= (s 0)) ;;
        (letsite (s 1) ← copy var_e) ;;
        (var_a2 ::= (s 1)) ;;
        (letsite (s 2) ← move var_a2) ;;
        unpackVariant("Empty", [], (s 2)) ;;
        ret []
    }
  ]
}

#guard
  match findFunAt (parseAndTranslate src).toOption.get! 0 with
  | some fd => alphaEquivFunDef fd hw_o1_f
  | none => false
