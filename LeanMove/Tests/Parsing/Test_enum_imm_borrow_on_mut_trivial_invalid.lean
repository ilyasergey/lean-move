/-
 Copyright Ilya Sergey
 Licensed under the Apache License, Version 2.0
-/

import LeanMove.Tests.Parsing.TestUtils
import LeanMove.Lang.Macros

/-! ## Parse Test: enum_imm_borrow_on_mut_trivial_invalid.mvir

Alpha-equivalence tests for trivial immutable borrow on mutable ref.
Two functions: Tester.bump_and_give, Tester.contrived_example_no (both single-block).
REJECTED by Sui: FIELD_EXISTS_MUTABLE_BORROW_ERROR
-/

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Lang.MoveIR.Parser
open LeanMove.Lang.MoveIR.Translate
open LeanMove.Tests.Parsing.TestUtils

private def src :=
  include_str "../Typechecking/expressivity/accepted/enum_imm_borrow_on_mut_trivial_invalid.mvir"

#guard (parseMvir src).isOk
#guard (parseAndTranslate src).isOk
#guard (parseAndTranslate src).toOption.get!.length == 2

-- ----------------------------------------------------------------
-- Common type definitions
-- ----------------------------------------------------------------

private def var_x_ref : Var := ⟨"x_ref"⟩
private def var_f_ref : Var := ⟨"f_ref"⟩
private def var_returned_ref : Var := ⟨"returned_ref"⟩
private def s (n : Nat) : Site := .site n

private def xVariants : AssocMap Id (AssocMap Field BasicMoveType) :=
  AssocMap.mk [("V", AssocMap.mk [(⟨"f"⟩, .u64)])]

private def xType : BasicMoveType := .tenum "X" xVariants

-- ----------------------------------------------------------------
-- bump_and_give: unpack, write, freeze, return
-- ----------------------------------------------------------------

private def hw_bump : FunDef := {
  params := [(var_x_ref, .ref xType (.paramRef var_x_ref) .siteBorrowMut)]
  returnType := [⟨.u64, some false⟩]
  locals := [
    { name := var_f_ref, type := .ref .u64 (.refid 1) .siteBorrowMut }
  ]
  blocks := [
    { label := "b0"
      body :=
        (letsite (s 0) ← move var_x_ref) ;;
        unpackVariant("V", [(⟨"f"⟩, (s 1))], (s 0)) ;;
        (var_f_ref ::= (s 1)) ;;
        (letsite (s 2) ← copy var_f_ref) ;;
        (letsite (s 3) ← copy var_f_ref) ;;
        (letsite (s 4) ← *(s 3)) ;;
        (letsite (s 5) ← #1) ;;
        (letsite (s 6) ← binop(.add, (s 4), (s 5))) ;;
        (*(s 2) ::= (s 6)) ;;
        (letsite (s 7) ← move var_f_ref) ;;
        (letsite (s 8) ← freeze (s 7)) ;;
        ret [(s 8)]
    }
  ]
}

#guard
  match findFunAt (parseAndTranslate src).toOption.get! 0 with
  | some fd => alphaEquivFunDef fd hw_bump
  | none => false

-- ----------------------------------------------------------------
-- contrived_example_no: call bump_and_give, then unpack (should be rejected)
-- ----------------------------------------------------------------

private def hw_contrived : FunDef := {
  params := [(var_x_ref, .ref xType (.paramRef var_x_ref) .siteBorrowMut)]
  returnType := [⟨.u64, some false⟩]
  locals := [
    { name := var_returned_ref, type := .ref .u64 (.refid 1) .siteBorrowImm },
    { name := var_f_ref, type := .ref .u64 (.refid 2) .siteBorrowMut }
  ]
  blocks := [
    { label := "b0"
      body :=
        (letsite (s 0) ← copy var_x_ref) ;;
        (call([(s 1)], "Tester.bump_and_give", [(s 0)])) ;;
        (var_returned_ref ::= (s 1)) ;;
        (letsite (s 2) ← move var_x_ref) ;;
        unpackVariant("V", [(⟨"f"⟩, (s 3))], (s 2)) ;;
        (var_f_ref ::= (s 3)) ;;
        (letsite (s 4) ← move var_returned_ref) ;;
        ret [(s 4)]
    }
  ]
}

#guard
  match findFunAt (parseAndTranslate src).toOption.get! 1 with
  | some fd => alphaEquivFunDef fd hw_contrived
  | none => false
