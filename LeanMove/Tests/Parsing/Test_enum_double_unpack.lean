/-
 Copyright Ilya Sergey
 Licensed under the Apache License, Version 2.0
-/

import LeanMove.Tests.Parsing.TestUtils
import LeanMove.Lang.Macros

/-! ## Parse Test: enum_double_unpack.mvir

Alpha-equivalence tests for double variant unpack.
Two functions: o.a (reuses field vars), o.b (moves y before second unpack)
-/

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Lang.MoveIR.Parser
open LeanMove.Lang.MoveIR.Translate
open LeanMove.Tests.Parsing.TestUtils

private def src :=
  include_str "../Typechecking/expressivity/accepted/enum_double_unpack.mvir"

#guard (parseMvir src).isOk
#guard (parseAndTranslate src).isOk
#guard (parseAndTranslate src).toOption.get!.length == 2

-- ----------------------------------------------------------------
-- Common type definitions
-- ----------------------------------------------------------------

private def var_e : Var := ⟨"e"⟩
private def var_x : Var := ⟨"x"⟩
private def var_x2 : Var := ⟨"x2"⟩
private def var_y : Var := ⟨"y"⟩
private def s (n : Nat) : Site := .site n

-- AssocMap.insert prepends, so entries are reversed from declaration order
private def xType : BasicMoveType := .tenum "o.X"

-- ----------------------------------------------------------------
-- Function a: reuses field vars across unpacks (sequencing issue)
-- ----------------------------------------------------------------

private def hw_a : FunDef := {
  params := [(var_e, .ref xType (.paramRef var_e) .siteBorrowMut)]
  returnType := []
  locals := [
    { name := var_x, type := .ref .u64 (.refid 1) .siteBorrowMut },
    { name := var_y, type := .ref .u64 (.refid 2) .siteBorrowMut }
  ]
  blocks := [
    { label := "b0"
      body :=
        (letsite (s 0) ← copy var_e) ;;
        unpackVariant("One", [(⟨"x"⟩, (s 1)), (⟨"y"⟩, (s 2))], (s 0)) ;;
        (var_x ::= (s 1)) ;;
        (var_y ::= (s 2)) ;;
        (letsite (s 3) ← move var_e) ;;
        unpackVariant("Two", [(⟨"x"⟩, (s 4)), (⟨"y"⟩, (s 5))], (s 3)) ;;
        (var_x ::= (s 4)) ;;
        (var_y ::= (s 5)) ;;
        ret []
    }
  ]
}

#guard
  match findFunInModule (parseAndTranslate src).toOption.get!
          "o" "a" with
  | some fd => alphaEquivFunDef fd hw_a
  | none => false

-- ----------------------------------------------------------------
-- Function b: moves y before second unpack
-- ----------------------------------------------------------------

private def hw_b : FunDef := {
  params := [(var_e, .ref xType (.paramRef var_e) .siteBorrowMut)]
  returnType := []
  locals := [
    { name := var_x, type := .ref .u64 (.refid 1) .siteBorrowMut },
    { name := var_x2, type := .ref .u64 (.refid 2) .siteBorrowMut },
    { name := var_y, type := .ref .u64 (.refid 3) .siteBorrowMut }
  ]
  blocks := [
    { label := "b0"
      body :=
        (letsite (s 0) ← copy var_e) ;;
        unpackVariant("One", [(⟨"x"⟩, (s 1)), (⟨"y"⟩, (s 2))], (s 0)) ;;
        (var_x ::= (s 1)) ;;
        (var_y ::= (s 2)) ;;
        (letsite (s 3) ← move var_y) ;;
        (letsite (s 4) ← #0) ;;
        (*(s 3) ::= (s 4)) ;;
        (letsite (s 5) ← move var_e) ;;
        unpackVariant("One", [(⟨"x"⟩, (s 6)), (⟨"y"⟩, (s 7))], (s 5)) ;;
        (var_x2 ::= (s 6)) ;;
        (var_y ::= (s 7)) ;;
        (letsite (s 8) ← move var_x) ;;
        (letsite (s 9) ← #0) ;;
        (*(s 8) ::= (s 9)) ;;
        (letsite (s 10) ← move var_x2) ;;
        (letsite (s 11) ← #0) ;;
        (*(s 10) ::= (s 11)) ;;
        ret []
    }
  ]
}

#guard
  match findFunInModule (parseAndTranslate src).toOption.get!
          "o" "b" with
  | some fd => alphaEquivFunDef fd hw_b
  | none => false
