/-
 Copyright Ilya Sergey
 Licensed under the Apache License, Version 2.0
-/

import LeanMove.Tests.Parsing.TestUtils
import LeanMove.Tests.Typechecking.expressivity.accepted.alias_writes

/-! ## Parse Test: alias_writes.mvir

Tests parsing and translation of the alias_writes Move IR example.
Four modules: borrow_local_twice, borrow_local_twice_reverse,
borrow_local_and_copy_ref, borrow_local_and_copy_ref_reverse.

Alpha-equivalence tests compare the parser output against hand-written
FunDefs to validate correct translation.
-/

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Lang.MoveIR.Parser
open LeanMove.Lang.MoveIR.Translate
open LeanMove.Tests.Parsing.TestUtils
open LeanMove.Tests.Expressivity.AliasWrites

def aliasWritesMvir :=
  include_str "../MVIR/alias_writes.mvir"

-- Parse succeeds
#guard (parseMvir aliasWritesMvir).isOk

-- Correct number of modules
#guard (parseMvir aliasWritesMvir).toOption.get!.modules.length == 4

-- Translation succeeds
#guard (parseAndTranslate aliasWritesMvir).isOk

-- ----------------------------------------------------------------
-- Hand-written FunDefs for alpha-equivalence testing
-- ----------------------------------------------------------------

-- Sites
private def s0 : Site := .site 0   -- integer literal 0 (for a = 0)
private def s1 : Site := .site 1   -- &mut a (for x)
private def s2 : Site := .site 2   -- &mut a or copy(x) (for y)
private def s3 : Site := .site 3   -- move(x) or move(y) for first write
private def s4 : Site := .site 4   -- integer literal 0 (for first write)
private def s5 : Site := .site 5   -- move(y) or move(x) for second write
private def s6 : Site := .site 6   -- integer literal 0 (for second write)

-- Module 1: borrow_local_twice
-- a = 0; x = &mut a; y = &mut a; *move(x) = 0; *move(y) = 0; return;
private def hw_borrow_local_twice : FunDef := {
  params := []
  returnType := []
  locals := [
    { name := var_a, type := .basic .u64 },
    { name := var_x, type := .ref .u64 (.refid 1) .siteBorrowMut },
    { name := var_y, type := .ref .u64 (.refid 2) .siteBorrowMut }
  ]
  blocks := [
    { label := "b0"
      body :=
        (letsite s0 ← #0) ;;
        (var_a ::= s0) ;;
        (letsite s1 ← &mut var_a) ;;
        (var_x ::= s1) ;;
        (letsite s2 ← &mut var_a) ;;
        (var_y ::= s2) ;;
        (letsite s3 ← move var_x) ;;
        (letsite s4 ← #0) ;;
        (*s3 ::= s4) ;;
        (letsite s5 ← move var_y) ;;
        (letsite s6 ← #0) ;;
        (*s5 ::= s6) ;;
        ret []
    }
  ]
}

-- Module 2: borrow_local_twice_reverse
-- a = 0; x = &mut a; y = &mut a; *move(y) = 0; *move(x) = 0; return;
private def hw_borrow_local_twice_reverse : FunDef := {
  params := []
  returnType := []
  locals := [
    { name := var_a, type := .basic .u64 },
    { name := var_x, type := .ref .u64 (.refid 1) .siteBorrowMut },
    { name := var_y, type := .ref .u64 (.refid 2) .siteBorrowMut }
  ]
  blocks := [
    { label := "b0"
      body :=
        (letsite s0 ← #0) ;;
        (var_a ::= s0) ;;
        (letsite s1 ← &mut var_a) ;;
        (var_x ::= s1) ;;
        (letsite s2 ← &mut var_a) ;;
        (var_y ::= s2) ;;
        (letsite s3 ← move var_y) ;;
        (letsite s4 ← #0) ;;
        (*s3 ::= s4) ;;
        (letsite s5 ← move var_x) ;;
        (letsite s6 ← #0) ;;
        (*s5 ::= s6) ;;
        ret []
    }
  ]
}

-- Module 3: borrow_local_and_copy_ref
-- a = 0; x = &mut a; y = copy(x); *move(x) = 0; *move(y) = 0; return;
private def hw_borrow_local_and_copy_ref : FunDef := {
  params := []
  returnType := []
  locals := [
    { name := var_a, type := .basic .u64 },
    { name := var_x, type := .ref .u64 (.refid 1) .siteBorrowMut },
    { name := var_y, type := .ref .u64 (.refid 2) .siteBorrowMut }
  ]
  blocks := [
    { label := "b0"
      body :=
        (letsite s0 ← #0) ;;
        (var_a ::= s0) ;;
        (letsite s1 ← &mut var_a) ;;
        (var_x ::= s1) ;;
        (letsite s2 ← copy var_x) ;;
        (var_y ::= s2) ;;
        (letsite s3 ← move var_x) ;;
        (letsite s4 ← #0) ;;
        (*s3 ::= s4) ;;
        (letsite s5 ← move var_y) ;;
        (letsite s6 ← #0) ;;
        (*s5 ::= s6) ;;
        ret []
    }
  ]
}

-- Module 4: borrow_local_and_copy_ref_reverse
-- a = 0; x = &mut a; y = copy(x); *move(y) = 0; *move(x) = 0; return;
private def hw_borrow_local_and_copy_ref_reverse : FunDef := {
  params := []
  returnType := []
  locals := [
    { name := var_a, type := .basic .u64 },
    { name := var_x, type := .ref .u64 (.refid 1) .siteBorrowMut },
    { name := var_y, type := .ref .u64 (.refid 2) .siteBorrowMut }
  ]
  blocks := [
    { label := "b0"
      body :=
        (letsite s0 ← #0) ;;
        (var_a ::= s0) ;;
        (letsite s1 ← &mut var_a) ;;
        (var_x ::= s1) ;;
        (letsite s2 ← copy var_x) ;;
        (var_y ::= s2) ;;
        (letsite s3 ← move var_y) ;;
        (letsite s4 ← #0) ;;
        (*s3 ::= s4) ;;
        (letsite s5 ← move var_x) ;;
        (letsite s6 ← #0) ;;
        (*s5 ::= s6) ;;
        ret []
    }
  ]
}

-- ----------------------------------------------------------------
-- Alpha-equivalence with hand-written examples
-- ----------------------------------------------------------------

#guard
  match parseAndTranslate aliasWritesMvir with
  | .ok results =>
    match findFunInModule results "borrow_local_twice" "t" with
    | some fd => alphaEquivFunDef fd hw_borrow_local_twice
    | none => false
  | .error _ => false

#guard
  match parseAndTranslate aliasWritesMvir with
  | .ok results =>
    match findFunInModule results "borrow_local_twice_reverse" "t" with
    | some fd => alphaEquivFunDef fd hw_borrow_local_twice_reverse
    | none => false
  | .error _ => false

#guard
  match parseAndTranslate aliasWritesMvir with
  | .ok results =>
    match findFunInModule results "borrow_local_and_copy_ref" "t" with
    | some fd => alphaEquivFunDef fd hw_borrow_local_and_copy_ref
    | none => false
  | .error _ => false

#guard
  match parseAndTranslate aliasWritesMvir with
  | .ok results =>
    match findFunInModule results "borrow_local_and_copy_ref_reverse" "t" with
    | some fd => alphaEquivFunDef fd hw_borrow_local_and_copy_ref_reverse
    | none => false
  | .error _ => false
