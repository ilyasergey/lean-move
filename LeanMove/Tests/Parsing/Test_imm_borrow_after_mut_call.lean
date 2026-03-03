/-
 Copyright Ilya Sergey
 Licensed under the Apache License, Version 2.0
-/

import LeanMove.Tests.Parsing.TestUtils
import LeanMove.Tests.Typechecking.expressivity.rejected.imm_borrow_after_mut_call_invalid

/-! ## Parse Test: imm_borrow_after_mut_call.mvir (REJECTED)

Tests parsing of imm_borrow_after_mut_call — can create an immutable extension
via a call after a mut borrow, but if the mut is a parent, it won't be writable.
Two modules: valid and invalid.

Alpha-equivalence tests compare the parser output against hand-written
FunDefs to validate correct translation.
-/

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Lang.MoveIR.Parser
open LeanMove.Lang.MoveIR.Translate
open LeanMove.Tests.Parsing.TestUtils
open LeanMove.Tests.Expressivity.ImmBorrowAfterMutCallInvalid

def immBorrowAfterMutCallMvir :=
  include_str "../Typechecking/expressivity/rejected/imm_borrow_after_mut_call.mvir"

-- Parse succeeds
#guard (parseMvir immBorrowAfterMutCallMvir).isOk

-- 2 modules
#guard (parseMvir immBorrowAfterMutCallMvir).toOption.get!.modules.length == 2

-- Translation succeeds
#guard (parseAndTranslate immBorrowAfterMutCallMvir).isOk

-- ----------------------------------------------------------------
-- Hand-written FunDef for alpha-equivalence testing
-- ----------------------------------------------------------------

-- Sites for invalid module's t function
private def s0 : Site := .site 0   -- integer literal 0 for a
private def s1 : Site := .site 1   -- &mut a
private def s2 : Site := .site 2   -- copy(r) [input to id_mut]
private def s3 : Site := .site 3   -- output of id_mut
private def s4 : Site := .site 4   -- &a [input to id]
private def s5 : Site := .site 5   -- output of id
private def s6 : Site := .site 6   -- copy(mut1)
private def s7 : Site := .site 7   -- integer literal 0 for write

-- invalid module: cannot write to mut1 because a has immutable alias imm1
private def hw_invalid : FunDef := {
  params := []
  returnType := []
  locals := [
    { name := var_a, type := .basic .u64 },
    { name := var_r, type := .ref .u64 (.refid 0) .siteBorrowMut },
    { name := var_mut1, type := .ref .u64 (.refid 1) .siteBorrowMut },
    { name := var_imm1, type := .ref .u64 (.refid 2) .siteBorrowImm }
  ]
  blocks := [
    { label := "b0"
      body :=
        -- a = 0
        (letsite s0 ← #0) ;;
        (var_a ::= s0) ;;
        -- r = &mut a
        (letsite s1 ← &mut var_a) ;;
        (var_r ::= s1) ;;
        -- mut1 = Self.id_mut(copy(r))
        (letsite s2 ← copy var_r) ;;
        (call([s3], "invalid.id_mut", [s2])) ;;
        (var_mut1 ::= s3) ;;
        -- imm1 = Self.id(&a)
        (letsite s4 ← &var_a) ;;
        (call([s5], "invalid.id", [s4])) ;;
        (var_imm1 ::= s5) ;;
        -- *copy(mut1) = 0 -- ERROR
        (letsite s6 ← copy var_mut1) ;;
        (letsite s7 ← #0) ;;
        (*s6 ::= s7) ;;
        ret []
    }
  ]
}

-- ----------------------------------------------------------------
-- Alpha-equivalence with hand-written example
-- ----------------------------------------------------------------

#guard
  match parseAndTranslate immBorrowAfterMutCallMvir with
  | .ok results =>
    match findFunInModule results "invalid" "t" with
    | some fd => alphaEquivFunDef fd hw_invalid
    | none => false
  | .error _ => false
