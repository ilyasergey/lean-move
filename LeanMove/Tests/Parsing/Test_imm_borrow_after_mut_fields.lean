/-
 Copyright Ilya Sergey
 Licensed under the Apache License, Version 2.0
-/

import LeanMove.Tests.Parsing.TestUtils
import LeanMove.Tests.Typechecking.expressivity.rejected.imm_borrow_after_mut_fields_invalid

/-! ## Parse Test: imm_borrow_after_mut_fields.mvir (REJECTED)

Tests parsing of imm_borrow_after_mut_fields — can borrow imm fields after a mut borrow,
but if the mut is a parent, it won't be writable.
Three modules: field (0x2), field (0x3), invalid_write (0x4).

Alpha-equivalence tests compare the parser output against hand-written
FunDefs to validate correct translation.
-/

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Lang.MoveIR.Parser
open LeanMove.Lang.MoveIR.Translate
open LeanMove.Tests.Parsing.TestUtils
open LeanMove.Tests.Expressivity.ImmBorrowAfterMutFieldsInvalid

def immBorrowAfterMutFieldsMvir :=
  include_str "../Typechecking/expressivity/rejected/imm_borrow_after_mut_fields.mvir"

-- Parse succeeds
#guard (parseMvir immBorrowAfterMutFieldsMvir).isOk

-- 3 modules
#guard (parseMvir immBorrowAfterMutFieldsMvir).toOption.get!.modules.length == 3

-- Translation succeeds
#guard (parseAndTranslate immBorrowAfterMutFieldsMvir).isOk

-- ----------------------------------------------------------------
-- Hand-written FunDef for alpha-equivalence testing
-- ----------------------------------------------------------------

-- Sites for invalid_write module's t function
private def s0 : Site := .site 0   -- &s (for s_imm)
private def s1 : Site := .site 1   -- &mut s (for s_mut)
private def s2 : Site := .site 2   -- copy(s_imm)
private def s3 : Site := .site 3   -- borrowField(s2, S, f)
private def s4 : Site := .site 4   -- copy(s_mut)
private def s5 : Site := .site 5   -- integer literal 0 for field
private def s6 : Site := .site 6   -- pack("S", [(f, s5)])

-- invalid_write module: cannot write to s_mut because of f_imm
private def hw_invalid_write : FunDef := {
  params := [(var_s, .basic (.trecord s_entries))]
  returnType := []
  locals := [
    { name := var_s_imm, type := .ref (.trecord s_entries) (.refid 0) .siteBorrowImm },
    { name := var_s_mut, type := .ref (.trecord s_entries) (.refid 1) .siteBorrowMut },
    { name := var_f_imm, type := .ref .u64 (.refid 2) .siteBorrowImm }
  ]
  blocks := [
    { label := "b0"
      body :=
        -- s_imm = &s
        (letsite s0 ← &var_s) ;;
        (var_s_imm ::= s0) ;;
        -- s_mut = &mut s
        (letsite s1 ← &mut var_s) ;;
        (var_s_mut ::= s1) ;;
        -- f_imm = &copy(s_imm).S::f
        (letsite s2 ← copy var_s_imm) ;;
        (letsite s3 ← borrowField(s2, .trecord s_entries, field_f)) ;;
        (var_f_imm ::= s3) ;;
        -- *copy(s_mut) = S { f: 0 } -- ERROR
        (letsite s4 ← copy var_s_mut) ;;
        (letsite s5 ← #0) ;;
        (letsite s6 ← pack("S", [(field_f, s5)])) ;;
        (*s4 ::= s6) ;;
        ret []
    }
  ]
}

-- ----------------------------------------------------------------
-- Alpha-equivalence with hand-written example
-- ----------------------------------------------------------------

#guard
  match parseAndTranslate immBorrowAfterMutFieldsMvir with
  | .ok results =>
    match findFunInModule results "invalid_write" "t" with
    | some fd => alphaEquivFunDef fd hw_invalid_write
    | none => false
  | .error _ => false
