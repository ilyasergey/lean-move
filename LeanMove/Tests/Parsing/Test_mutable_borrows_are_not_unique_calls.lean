/-
 Copyright Ilya Sergey
 Licensed under the Apache License, Version 2.0
-/

import LeanMove.Tests.Parsing.TestUtils
import LeanMove.Tests.Typechecking.expressivity.rejected.mutable_borrows_are_not_unique_calls_invalid

/-! ## Parse Test: mutable_borrows_are_not_unique_calls.mvir (REJECTED)

Tests parsing of mutable_borrows_are_not_unique_calls — mutable borrows are not unique,
even with calls, as long as arguments have no extensions at call time.
Three modules: call (create), call_and_write_invalid (write), call_and_write_valid (write).

Alpha-equivalence tests compare the parser output against hand-written
FunDefs to validate correct translation.
-/

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Lang.MoveIR.Parser
open LeanMove.Lang.MoveIR.Translate
open LeanMove.Tests.Parsing.TestUtils
open LeanMove.Tests.Expressivity.MutableBorrowsNotUniqueCallsInvalid

def mutableBorrowsAreNotUniqueCallsMvir :=
  include_str "../MVIR/mutable_borrows_are_not_unique_calls.mvir"

-- Parse succeeds
#guard (parseMvir mutableBorrowsAreNotUniqueCallsMvir).isOk

-- 3 modules
#guard (parseMvir mutableBorrowsAreNotUniqueCallsMvir).toOption.get!.modules.length == 3

-- Translation succeeds
#guard (parseAndTranslate mutableBorrowsAreNotUniqueCallsMvir).isOk

-- ----------------------------------------------------------------
-- Hand-written FunDefs for alpha-equivalence testing
-- ----------------------------------------------------------------

-- Sites for borrow_f function
private def bs0 : Site := .site 0   -- move(s) in borrow_f
private def bs1 : Site := .site 1   -- &mut bs0.S::f in borrow_f

private def hw_borrow_f : FunDef := {
  params := [(var_s, .ref (.trecord s_entries) (.paramRef var_s) .siteBorrowMut)]
  returnType := [⟨.u64, some true⟩]
  locals := []
  blocks := [
    { label := "b0"
      body :=
        (letsite bs0 ← move var_s) ;;
        (letsite bs1 ← borrowMutField(bs0, .trecord s_entries, field_f)) ;;
        ret [bs1]
    }
  ]
}

-- Sites for call_and_write_invalid function
private def s0 : Site := .site 0   -- copy(s) for call argument
private def s1 : Site := .site 1   -- result site from call to borrow_f
private def s2 : Site := .site 2   -- copy(s) for f
private def s3 : Site := .site 3   -- &mut s2.S::f (for f)
private def s4 : Site := .site 4   -- copy(call)
private def s5 : Site := .site 5   -- integer literal 0 for first write
private def s6 : Site := .site 6   -- copy(f)
private def s7 : Site := .site 7   -- integer literal 0 for second write

private def hw_call_and_write_invalid : FunDef := {
  params := [(var_s, .ref (.trecord s_entries) (.paramRef var_s) .siteBorrowMut)]
  returnType := []
  locals := [
    { name := var_call, type := .ref .u64 (.refid 1) .siteBorrowMut },
    { name := var_f, type := .ref .u64 (.refid 2) .siteBorrowMut }
  ]
  blocks := [
    { label := "b0"
      body :=
        -- call = Self.borrow_f(copy(s))
        (letsite s0 ← copy var_s) ;;
        (call([s1], "call_and_write_invalid.borrow_f", [s0])) ;;
        (var_call ::= s1) ;;
        -- f = &mut copy(s).S::f
        (letsite s2 ← copy var_s) ;;
        (letsite s3 ← borrowMutField(s2, .trecord s_entries, field_f)) ;;
        (var_f ::= s3) ;;
        -- *copy(call) = 0 -- ERROR: relationship with f unknown
        (letsite s4 ← copy var_call) ;;
        (letsite s5 ← #0) ;;
        (*s4 ::= s5) ;;
        -- *copy(f) = 0 -- ERROR: relationship with call unknown
        (letsite s6 ← copy var_f) ;;
        (letsite s7 ← #0) ;;
        (*s6 ::= s7) ;;
        ret []
    }
  ]
}

-- ----------------------------------------------------------------
-- Alpha-equivalence with hand-written examples
-- ----------------------------------------------------------------

#guard
  match parseAndTranslate mutableBorrowsAreNotUniqueCallsMvir with
  | .ok results =>
    match findFunInModule results "call_and_write_invalid" "borrow_f" with
    | some fd => alphaEquivFunDef fd hw_borrow_f
    | none => false
  | .error _ => false

#guard
  match parseAndTranslate mutableBorrowsAreNotUniqueCallsMvir with
  | .ok results =>
    match findFunInModule results "call_and_write_invalid" "write" with
    | some fd => alphaEquivFunDef fd hw_call_and_write_invalid
    | none => false
  | .error _ => false
