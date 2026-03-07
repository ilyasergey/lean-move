/-
 Copyright Ilya Sergey
 Licensed under the Apache License, Version 2.0
-/

import LeanMove.Tests.Parsing.TestUtils
import LeanMove.Tests.Typechecking.expressivity.accepted.imm_borrow_after_mut

/-! ## Parse Test: imm_borrow_after_mut.mvir

Tests parsing of imm_borrow_after_mut — can borrow immutable after mutable.
Two modules: direct and copy_and_freeze.

Alpha-equivalence tests compare the parser output against hand-written
FunDefs to validate correct translation.
-/

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Lang.MoveIR.Parser
open LeanMove.Lang.MoveIR.Translate
open LeanMove.Tests.Parsing.TestUtils
open LeanMove.Tests.Expressivity.ImmBorrowAfterMut

def immBorrowAfterMutMvir :=
  include_str "../Typechecking/expressivity/accepted/imm_borrow_after_mut.mvir"

-- Parse succeeds
#guard (parseMvir immBorrowAfterMutMvir).isOk

-- Translation succeeds
#guard (parseAndTranslate immBorrowAfterMutMvir).isOk

-- ----------------------------------------------------------------
-- Hand-written FunDefs for alpha-equivalence testing
-- ----------------------------------------------------------------

-- Sites for direct module
private def ds0 : Site := .site 0   -- integer literal 0 (for a = 0)
private def ds1 : Site := .site 1   -- &mut a (for rmut)
private def ds2 : Site := .site 2   -- &a (for rimm)
private def ds3 : Site := .site 3   -- copy(rmut)
private def ds4 : Site := .site 4   -- integer literal 0 (for write)
private def ds5 : Site := .site 5   -- copy(rimm)
private def ds6 : Site := .site 6   -- *ds5 (readRef, discarded)

-- Module 1: direct
-- a = 0; rmut = &mut a; rimm = &a; *copy(rmut) = 0; _ = *copy(rimm); return;
private def hw_direct : FunDef := {
  params := []
  returnType := []
  locals := [
    { name := var_a, type := .basic .u64 },
    { name := var_rmut, type := .ref .u64 (.refid 1) .siteBorrowMut },
    { name := var_rimm, type := .ref .u64 (.refid 2) .siteBorrowImm }
  ]
  blocks := [
    { label := "b0"
      body :=
        (letsite ds0 ← #0) ;;
        (var_a ::= ds0) ;;
        (letsite ds1 ← &mut var_a) ;;
        (var_rmut ::= ds1) ;;
        (letsite ds2 ← &var_a) ;;
        (var_rimm ::= ds2) ;;
        (letsite ds3 ← copy var_rmut) ;;
        (letsite ds4 ← #0) ;;
        (*ds3 ::= ds4) ;;
        (letsite ds5 ← copy var_rimm) ;;
        (letsite ds6 ← *ds5) ;;
        release ds6 ;;
        ret []
    }
  ]
}

-- Sites for copy_and_freeze module
private def cs0 : Site := .site 10  -- integer literal 0 (for a = 0)
private def cs1 : Site := .site 11  -- &mut a (for rmut)
private def cs2 : Site := .site 12  -- copy(rmut)
private def cs3 : Site := .site 13  -- freeze(cs2)
private def cs4 : Site := .site 14  -- copy(rmut)
private def cs5 : Site := .site 15  -- integer literal 0 (for write)
private def cs6 : Site := .site 16  -- copy(rimm)
private def cs7 : Site := .site 17  -- *cs6 (readRef, discarded)

-- Module 2: copy_and_freeze
-- a = 0; rmut = &mut a; rimm = freeze(copy(rmut)); *copy(rmut) = 0; _ = *copy(rimm); return;
private def hw_copy_and_freeze : FunDef := {
  params := []
  returnType := []
  locals := [
    { name := var_a, type := .basic .u64 },
    { name := var_rmut, type := .ref .u64 (.refid 1) .siteBorrowMut },
    { name := var_rimm, type := .ref .u64 (.refid 2) .siteBorrowImm }
  ]
  blocks := [
    { label := "b0"
      body :=
        (letsite cs0 ← #0) ;;
        (var_a ::= cs0) ;;
        (letsite cs1 ← &mut var_a) ;;
        (var_rmut ::= cs1) ;;
        (letsite cs2 ← copy var_rmut) ;;
        (letsite cs3 ← freeze cs2) ;;
        (var_rimm ::= cs3) ;;
        (letsite cs4 ← copy var_rmut) ;;
        (letsite cs5 ← #0) ;;
        (*cs4 ::= cs5) ;;
        (letsite cs6 ← copy var_rimm) ;;
        (letsite cs7 ← *cs6) ;;
        release cs7 ;;
        ret []
    }
  ]
}

-- ----------------------------------------------------------------
-- Alpha-equivalence with hand-written examples
-- ----------------------------------------------------------------

#guard
  match parseAndTranslate immBorrowAfterMutMvir with
  | .ok results =>
    match findFunInModule results "direct" "t" with
    | some fd => alphaEquivFunDef fd hw_direct
    | none => false
  | .error _ => false

#guard
  match parseAndTranslate immBorrowAfterMutMvir with
  | .ok results =>
    match findFunInModule results "copy_and_freeze" "t" with
    | some fd => alphaEquivFunDef fd hw_copy_and_freeze
    | none => false
  | .error _ => false
