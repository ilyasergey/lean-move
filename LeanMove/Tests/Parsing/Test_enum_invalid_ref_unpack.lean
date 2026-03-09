/-
 Copyright Ilya Sergey
 Licensed under the Apache License, Version 2.0
-/

import LeanMove.Tests.Parsing.TestUtils
import LeanMove.Lang.Macros

/-! ## Parse Test: enum_invalid_ref_unpack.mvir

Alpha-equivalence tests for invalid reference unpack patterns.
All 7 modules REJECTED by Sui. 10 functions total, all single-block.
Testing representative functions: m1 (index 0), overwrite (index 2), m5 (index 4).
-/

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Lang.MoveIR.Parser
open LeanMove.Lang.MoveIR.Translate
open LeanMove.Tests.Parsing.TestUtils

private def src :=
  include_str "../MVIR/enum_invalid_ref_unpack.mvir"

#guard (parseMvir src).isOk
#guard (parseAndTranslate src).isOk
#guard (parseAndTranslate src).toOption.get!.length == 10

-- ----------------------------------------------------------------
-- Common type definitions
-- ----------------------------------------------------------------

private def var_e : Var := ⟨"e"⟩
private def var_x : Var := ⟨"x"⟩
private def var_y : Var := ⟨"y"⟩
private def var_uu : Var := ⟨"_"⟩
private def s (n : Nat) : Site := .site n

-- AssocMap.insert prepends, so entries are reversed from declaration order
private def xType : BasicMoveType := .tenum "o.X"

-- ----------------------------------------------------------------
-- m1 (index 0): writes to *move(e) while fields borrowed from copy(e)
-- ----------------------------------------------------------------

private def hw_m1 : FunDef := {
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
        unpackVariant("Two", [(⟨"x"⟩, (s 1)), (⟨"y"⟩, (s 2))], (s 0)) ;;
        (var_x ::= (s 1)) ;;
        (var_y ::= (s 2)) ;;
        (letsite (s 3) ← move var_x) ;;
        (letsite (s 4) ← #1) ;;
        (*(s 3) ::= (s 4)) ;;
        (letsite (s 5) ← copy var_e) ;;
        unpackVariant("One", [(⟨"x"⟩, (s 6))], (s 5)) ;;
        (var_x ::= (s 6)) ;;
        (letsite (s 7) ← move var_e) ;;
        (letsite (s 8) ← #0) ;;
        (letsite (s 9) ← packVariant("o.X", "One", [(⟨"x"⟩, (s 8))])) ;;
        (*(s 7) ::= (s 9)) ;;
        (letsite (s 10) ← move var_y) ;;
        (letsite (s 11) ← #3) ;;
        (*(s 10) ::= (s 11)) ;;
        (letsite (s 12) ← move var_x) ;;
        (letsite (s 13) ← #2) ;;
        (*(s 12) ::= (s 13)) ;;
        ret []
    }
  ]
}

#guard
  match findFunAt (parseAndTranslate src).toOption.get! 0 with
  | some fd => alphaEquivFunDef fd hw_m1
  | none => false

-- ----------------------------------------------------------------
-- overwrite (index 2): simple *move(e) = packVariant
-- ----------------------------------------------------------------

private def hw_overwrite : FunDef := {
  params := [(var_e, .ref xType (.paramRef var_e) .siteBorrowMut)]
  returnType := []
  locals := []
  blocks := [
    { label := "b0"
      body :=
        (letsite (s 0) ← move var_e) ;;
        (letsite (s 1) ← #0) ;;
        (letsite (s 2) ← packVariant("o.X", "One", [(⟨"x"⟩, (s 1))])) ;;
        (*(s 0) ::= (s 2)) ;;
        ret []
    }
  ]
}

#guard
  match findFunAt (parseAndTranslate src).toOption.get! 2 with
  | some fd => alphaEquivFunDef fd hw_overwrite
  | none => false
