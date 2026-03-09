/-
 Copyright Ilya Sergey
 Licensed under the Apache License, Version 2.0
-/

import LeanMove.Tests.Parsing.TestUtils
import LeanMove.Lang.Macros

/-! ## Parse Test: enum_valid_ref_unpack.mvir

Alpha-equivalence tests for valid reference unpack patterns.
Five functions: o.h, o.f, o.g, o.k, o.k1 (all single-block)
-/

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Lang.MoveIR.Parser
open LeanMove.Lang.MoveIR.Translate
open LeanMove.Tests.Parsing.TestUtils

private def src :=
  include_str "../Typechecking/expressivity/accepted/enum_valid_ref_unpack.mvir"

#guard (parseMvir src).isOk
#guard (parseAndTranslate src).isOk
#guard (parseAndTranslate src).toOption.get!.length == 5

-- ----------------------------------------------------------------
-- Common type definitions
-- ----------------------------------------------------------------

private def var_e : Var := ⟨"e"⟩
private def var_x : Var := ⟨"x"⟩
private def var_y : Var := ⟨"y"⟩
private def var_t : Var := ⟨"t"⟩
private def s (n : Nat) : Site := .site n

-- AssocMap.insert prepends, so entries are reversed from declaration order
private def xType : BasicMoveType := .tenum "o.X"

-- ----------------------------------------------------------------
-- h: Two→One unpack, write to x, unpack One, write to y, write to x
-- ----------------------------------------------------------------

private def hw_h : FunDef := {
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
        (letsite (s 5) ← move var_e) ;;
        unpackVariant("One", [(⟨"x"⟩, (s 6))], (s 5)) ;;
        (var_x ::= (s 6)) ;;
        (letsite (s 7) ← move var_y) ;;
        (letsite (s 8) ← #3) ;;
        (*(s 7) ::= (s 8)) ;;
        (letsite (s 9) ← move var_x) ;;
        (letsite (s 10) ← #2) ;;
        (*(s 9) ::= (s 10)) ;;
        ret []
    }
  ]
}

#guard
  match findFunInModule (parseAndTranslate src).toOption.get! "o" "h" with
  | some fd => alphaEquivFunDef fd hw_h
  | none => false

-- ----------------------------------------------------------------
-- f: One→Two unpack
-- ----------------------------------------------------------------

private def hw_f : FunDef := {
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
        unpackVariant("One", [(⟨"x"⟩, (s 1))], (s 0)) ;;
        (var_x ::= (s 1)) ;;
        (letsite (s 2) ← move var_x) ;;
        (letsite (s 3) ← #1) ;;
        (*(s 2) ::= (s 3)) ;;
        (letsite (s 4) ← move var_e) ;;
        unpackVariant("Two", [(⟨"x"⟩, (s 5)), (⟨"y"⟩, (s 6))], (s 4)) ;;
        (var_x ::= (s 5)) ;;
        (var_y ::= (s 6)) ;;
        (letsite (s 7) ← move var_x) ;;
        (letsite (s 8) ← #2) ;;
        (*(s 7) ::= (s 8)) ;;
        ret []
    }
  ]
}

#guard
  match findFunInModule (parseAndTranslate src).toOption.get! "o" "f" with
  | some fd => alphaEquivFunDef fd hw_f
  | none => false

-- ----------------------------------------------------------------
-- g: Two→One unpack (similar to h but different field order)
-- ----------------------------------------------------------------

private def hw_g : FunDef := {
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
        (letsite (s 5) ← move var_e) ;;
        unpackVariant("One", [(⟨"x"⟩, (s 6))], (s 5)) ;;
        (var_x ::= (s 6)) ;;
        (letsite (s 7) ← move var_x) ;;
        (letsite (s 8) ← #2) ;;
        (*(s 7) ::= (s 8)) ;;
        ret []
    }
  ]
}

#guard
  match findFunInModule (parseAndTranslate src).toOption.get! "o" "g" with
  | some fd => alphaEquivFunDef fd hw_g
  | none => false

-- ----------------------------------------------------------------
-- k: freeze + immutable unpack + writeRef via packVariant
-- ----------------------------------------------------------------

private def hw_k : FunDef := {
  params := [(var_e, .ref xType (.paramRef var_e) .siteBorrowMut)]
  returnType := []
  locals := [
    { name := var_x, type := .ref .u64 (.refid 1) .siteBorrowImm },
    { name := var_y, type := .ref .u64 (.refid 2) .siteBorrowImm }
  ]
  blocks := [
    { label := "b0"
      body :=
        (letsite (s 0) ← copy var_e) ;;
        (letsite (s 1) ← freeze (s 0)) ;;
        unpackVariant("Two", [(⟨"x"⟩, (s 2)), (⟨"y"⟩, (s 3))], (s 1)) ;;
        (var_x ::= (s 2)) ;;
        (var_y ::= (s 3)) ;;
        (letsite (s 4) ← move var_x) ;;
        release (s 4) ;;
        (letsite (s 5) ← move var_y) ;;
        release (s 5) ;;
        (letsite (s 6) ← move var_e) ;;
        (letsite (s 7) ← #0) ;;
        (letsite (s 8) ← packVariant("o.X", "One", [(⟨"x"⟩, (s 7))])) ;;
        (*(s 6) ::= (s 8)) ;;
        ret []
    }
  ]
}

#guard
  match findFunInModule (parseAndTranslate src).toOption.get! "o" "k" with
  | some fd => alphaEquivFunDef fd hw_k
  | none => false

-- ----------------------------------------------------------------
-- k1: freeze + immutable unpack + readRef + writeRef via packVariant + abort
-- ----------------------------------------------------------------

private def hw_k1 : FunDef := {
  params := [(var_e, .ref xType (.paramRef var_e) .siteBorrowMut)]
  returnType := []
  locals := [
    { name := var_x, type := .ref .u64 (.refid 1) .siteBorrowImm },
    { name := var_y, type := .ref .u64 (.refid 2) .siteBorrowImm },
    { name := var_t, type := .basic .u64 }
  ]
  blocks := [
    { label := "b0"
      body :=
        (letsite (s 0) ← copy var_e) ;;
        (letsite (s 1) ← freeze (s 0)) ;;
        unpackVariant("Two", [(⟨"x"⟩, (s 2)), (⟨"y"⟩, (s 3))], (s 1)) ;;
        (var_x ::= (s 2)) ;;
        (var_y ::= (s 3)) ;;
        (letsite (s 4) ← move var_x) ;;
        release (s 4) ;;
        (letsite (s 5) ← move var_y) ;;
        (letsite (s 6) ← *(s 5)) ;;
        (var_t ::= (s 6)) ;;
        (letsite (s 7) ← move var_e) ;;
        (letsite (s 8) ← #0) ;;
        (letsite (s 9) ← packVariant("o.X", "One", [(⟨"x"⟩, (s 8))])) ;;
        (*(s 7) ::= (s 9)) ;;
        (letsite (s 10) ← move var_t) ;;
        abort (s 10)
    }
  ]
}

#guard
  match findFunInModule (parseAndTranslate src).toOption.get! "o" "k1" with
  | some fd => alphaEquivFunDef fd hw_k1
  | none => false
