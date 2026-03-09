/-
 Copyright Ilya Sergey
 Licensed under the Apache License, Version 2.0
-/

import LeanMove.Tests.Parsing.TestUtils
import LeanMove.Tests.Typechecking.expressivity.accepted.multible_mutable_return_values

/-! ## Parse Test: multible_mutable_return_values.mvir

Tests parsing of multible_mutable_return_values — all mutable return values
of a call should be writable. Uses multi-return (return e1, e2) and
multi-assignment (x, y = call).

Alpha-equivalence tests compare the parser output against hand-written
FunDefs to validate correct translation.
-/

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Lang.MoveIR.Parser
open LeanMove.Lang.MoveIR.Translate
open LeanMove.Tests.Parsing.TestUtils
open LeanMove.Tests.Expressivity.MultipleMutableReturnValues

def multibleMutableReturnValuesMvir :=
  include_str "../MVIR/multible_mutable_return_values.mvir"

-- Parse succeeds
#guard (parseMvir multibleMutableReturnValuesMvir).isOk

-- Translation succeeds
#guard (parseAndTranslate multibleMutableReturnValuesMvir).isOk

-- ----------------------------------------------------------------
-- Hand-written FunDefs for alpha-equivalence testing
-- ----------------------------------------------------------------

-- Sites for borrow function
private def s0 : Site := .site 0   -- copy(p) for field x borrow
private def s1 : Site := .site 1   -- &mut s0.Point::x
private def s2 : Site := .site 2   -- copy(p) for field y borrow
private def s3 : Site := .site 3   -- &mut s2.Point::y

private def hw_borrow : FunDef := {
  params := [(var_p, .ref (.trecord point_entries) r0 .siteBorrowMut)]
  returnType := [⟨.u64, some true⟩, ⟨.u64, some true⟩]
  locals := []
  blocks := [
    { label := "b0"
      body :=
        (letsite s0 ← copy var_p) ;;
        (letsite s1 ← borrowMutField(s0, .trecord point_entries, field_x)) ;;
        (letsite s2 ← copy var_p) ;;
        (letsite s3 ← borrowMutField(s2, .trecord point_entries, field_y)) ;;
        ret [s1, s3]
    }
  ]
}

-- Sites for write function
private def ws0 : Site := .site 0   -- copy(p)
private def ws1 : Site := .site 1   -- call result for x
private def ws2 : Site := .site 2   -- call result for y
private def ws3 : Site := .site 3   -- copy(x)
private def ws4 : Site := .site 4   -- #0
private def ws5 : Site := .site 5   -- copy(y)
private def ws6 : Site := .site 6   -- #0
private def ws7 : Site := .site 7   -- copy(x)
private def ws8 : Site := .site 8   -- #0
private def ws9 : Site := .site 9   -- copy(y)
private def ws10 : Site := .site 10  -- #0

private def hw_write : FunDef := {
  params := [(var_p, .ref (.trecord point_entries) r0 .siteBorrowMut)]
  returnType := []
  locals := [
    { name := var_x, type := .ref .u64 (.refid 1) .siteBorrowMut },
    { name := var_y, type := .ref .u64 (.refid 2) .siteBorrowMut }
  ]
  blocks := [
    { label := "b0"
      body :=
        -- x, y = Self.borrow(copy(p))
        (letsite ws0 ← copy var_p) ;;
        (call([ws1, ws2], "Tester.borrow", [ws0])) ;;
        (var_x ::= ws1) ;;
        (var_y ::= ws2) ;;
        -- *copy(x) = 0
        (letsite ws3 ← copy var_x) ;;
        (letsite ws4 ← #0) ;;
        (*ws3 ::= ws4) ;;
        -- *copy(y) = 0
        (letsite ws5 ← copy var_y) ;;
        (letsite ws6 ← #0) ;;
        (*ws5 ::= ws6) ;;
        -- *copy(x) = 0 (again)
        (letsite ws7 ← copy var_x) ;;
        (letsite ws8 ← #0) ;;
        (*ws7 ::= ws8) ;;
        -- *copy(y) = 0 (again)
        (letsite ws9 ← copy var_y) ;;
        (letsite ws10 ← #0) ;;
        (*ws9 ::= ws10) ;;
        ret []
    }
  ]
}

-- ----------------------------------------------------------------
-- Alpha-equivalence with hand-written examples
-- ----------------------------------------------------------------

#guard
  match parseAndTranslate multibleMutableReturnValuesMvir with
  | .ok results =>
    match findFunInModule results "Tester" "borrow" with
    | some fd => alphaEquivFunDef fd hw_borrow
    | none => false
  | .error _ => false

#guard
  match parseAndTranslate multibleMutableReturnValuesMvir with
  | .ok results =>
    match findFunInModule results "Tester" "write" with
    | some fd => alphaEquivFunDef fd hw_write
    | none => false
  | .error _ => false
