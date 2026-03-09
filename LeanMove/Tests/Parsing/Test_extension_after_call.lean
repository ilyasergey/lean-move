/-
 Copyright Ilya Sergey
 Licensed under the Apache License, Version 2.0
-/

import LeanMove.Tests.Parsing.TestUtils
import LeanMove.Tests.Typechecking.expressivity.accepted.extension_after_call

/-! ## Parse Test: extension_after_call.mvir

Tests parsing of extension_after_call — writing to extension after a function call,
with struct definitions (Point, Box) and multiple functions.

Alpha-equivalence tests compare the parser output against hand-written
FunDefs to validate correct translation.
-/

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Lang.MoveIR.Parser
open LeanMove.Lang.MoveIR.Translate
open LeanMove.Tests.Parsing.TestUtils
open LeanMove.Tests.Expressivity.ExtensionAfterCall

def extensionAfterCallMvir :=
  include_str "../MVIR/extension_after_call.mvir"

-- Parse succeeds
#guard (parseMvir extensionAfterCallMvir).isOk

-- Translation succeeds
#guard (parseAndTranslate extensionAfterCallMvir).isOk

-- Check borrow function
#guard
  match parseAndTranslate extensionAfterCallMvir with
  | .ok results =>
    match findFun results "borrow" with
    | some fd =>
      fd.params.length == 1 &&
      fd.locals.length == 0 &&
      fd.returnType.length == 1 &&
      fd.blocks.length == 1
    | none => false
  | .error _ => false

-- Check write function
#guard
  match parseAndTranslate extensionAfterCallMvir with
  | .ok results =>
    match findFun results "write" with
    | some fd =>
      fd.params.length == 1 &&
      fd.locals.length == 3 &&
      fd.returnType.length == 1 &&
      fd.blocks.length == 1
    | none => false
  | .error _ => false

-- ----------------------------------------------------------------
-- Hand-written FunDefs for alpha-equivalence testing
-- ----------------------------------------------------------------

-- Variable used by MVIR's borrow param (MVIR uses "p", not "b")
private def var_p : Var := ⟨"p"⟩

-- Sites for borrow function
private def bs0 : Site := .site 0    -- copy(p)
private def bs1 : Site := .site 1    -- borrowMutField(bs0, Box, tl)

-- borrow(p: &mut Box): &mut Point
-- label b0: return &mut copy(p).Box::tl;
private def hw_borrow : FunDef := {
  params := [(var_p, .ref (.trecord box_entries) (.paramRef var_p) .siteBorrowMut)]
  returnType := [⟨.trecord point_entries, some true⟩]
  locals := []
  blocks := [
    { label := "b0"
      body :=
        (letsite bs0 ← copy var_p) ;;
        (letsite bs1 ← borrowMutField(bs0, .trecord box_entries, field_tl)) ;;
        ret [bs1]
    }
  ]
}

-- Sites for write function
private def ws0 : Site := .site 10   -- copy(b)
private def ws1 : Site := .site 11   -- call output: borrow(copy(b))
private def ws2 : Site := .site 12   -- copy(p)
private def ws3 : Site := .site 13   -- borrowMutField(ws2, Point, x)
private def ws4 : Site := .site 14   -- move(x)
private def ws5 : Site := .site 15   -- integer literal 0
private def ws6 : Site := .site 16   -- copy(p) for y
private def ws7 : Site := .site 17   -- borrowMutField(ws6, Point, y)
private def ws8 : Site := .site 18   -- move(y)
private def ws9 : Site := .site 19   -- integer literal 0
private def ws10 : Site := .site 20  -- move(p) for return

-- write(b: &mut Box): &mut Point
-- label b0:
--   p = Self.borrow(copy(b));
--   x = &mut copy(p).Point::x; *move(x) = 0;
--   y = &mut copy(p).Point::y; *move(y) = 0;
--   return move(p);
private def hw_write : FunDef := {
  params := [(var_b, .ref (.trecord box_entries) (.paramRef var_b) .siteBorrowMut)]
  returnType := [⟨.trecord point_entries, some true⟩]
  locals := [
    { name := var_p, type := .ref (.trecord point_entries) (.refid 1) .siteBorrowMut },
    { name := var_x, type := .ref .u64 (.refid 2) .siteBorrowMut },
    { name := var_y, type := .ref .u64 (.refid 3) .siteBorrowMut }
  ]
  blocks := [
    { label := "b0"
      body :=
        -- p = Self.borrow(copy(b))
        (letsite ws0 ← copy var_b) ;;
        (call([ws1], "Tester.borrow", [ws0])) ;;
        (var_p ::= ws1) ;;
        -- x = &mut copy(p).Point::x
        (letsite ws2 ← copy var_p) ;;
        (letsite ws3 ← borrowMutField(ws2, .trecord point_entries, field_x)) ;;
        (var_x ::= ws3) ;;
        -- *move(x) = 0
        (letsite ws4 ← move var_x) ;;
        (letsite ws5 ← #0) ;;
        (*ws4 ::= ws5) ;;
        -- y = &mut copy(p).Point::y
        (letsite ws6 ← copy var_p) ;;
        (letsite ws7 ← borrowMutField(ws6, .trecord point_entries, field_y)) ;;
        (var_y ::= ws7) ;;
        -- *move(y) = 0
        (letsite ws8 ← move var_y) ;;
        (letsite ws9 ← #0) ;;
        (*ws8 ::= ws9) ;;
        -- return move(p)
        (letsite ws10 ← move var_p) ;;
        ret [ws10]
    }
  ]
}

-- ----------------------------------------------------------------
-- Alpha-equivalence with hand-written examples
-- ----------------------------------------------------------------

#guard
  match parseAndTranslate extensionAfterCallMvir with
  | .ok results =>
    match findFun results "borrow" with
    | some fd => alphaEquivFunDef fd hw_borrow
    | none => false
  | .error _ => false

#guard
  match parseAndTranslate extensionAfterCallMvir with
  | .ok results =>
    match findFun results "write" with
    | some fd => alphaEquivFunDef fd hw_write
    | none => false
  | .error _ => false
