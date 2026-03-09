/-
 Copyright Ilya Sergey
 Licensed under the Apache License, Version 2.0
-/

import LeanMove.Tests.Parsing.TestUtils
import LeanMove.Lang.Macros

/-! ## Parse Test: vec_double_borrow.mvir

Alpha-equivalence tests for the vector double borrow rejection tests.
Three modules: imm_then_mut, mut_then_imm, mut_then_mut.
-/

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Lang.MoveIR.Parser
open LeanMove.Lang.MoveIR.Translate
open LeanMove.Tests.Parsing.TestUtils

private def vecDoubleBorrowMvir :=
  include_str "../MVIR/vec_double_borrow.mvir"

#guard (parseMvir vecDoubleBorrowMvir).isOk
#guard (parseAndTranslate vecDoubleBorrowMvir).isOk
#guard (parseAndTranslate vecDoubleBorrowMvir).toOption.get!.length == 3

-- ----------------------------------------------------------------
-- Hand-written FunDefs for alpha-equivalence testing
-- ----------------------------------------------------------------

private def var_v : Var := ⟨"v"⟩
private def var_e_imm1 : Var := ⟨"e_imm1"⟩
private def var_e_mut2 : Var := ⟨"e_mut2"⟩
private def var_e_mut1 : Var := ⟨"e_mut1"⟩
private def var_e_imm2 : Var := ⟨"e_imm2"⟩

private def s0  : Site := .site 0
private def s1  : Site := .site 1
private def s2  : Site := .site 2
private def s3  : Site := .site 3
private def s4  : Site := .site 4
private def s5  : Site := .site 5
private def s6  : Site := .site 6
private def s7  : Site := .site 7
private def s8  : Site := .site 8
private def s9  : Site := .site 9
private def s10 : Site := .site 10

-- Module 0: imm_then_mut
private def hw_imm_then_mut : FunDef := {
  params := []
  returnType := []
  locals := [
    { name := var_v, type := .basic (.tvec .u64) },
    { name := var_e_imm1, type := .ref .u64 (.refid 1) .siteBorrowImm },
    { name := var_e_mut2, type := .ref .u64 (.refid 2) .siteBorrowMut }
  ]
  blocks := [
    { label := "b0"
      body :=
        (letsite s0 ← vecPack(.u64, [])) ;;
        (var_v ::= s0) ;;
        (letsite s1 ← &mut var_v) ;;
        (letsite s2 ← #0) ;;
        vecPushBack(s1, s2) ;;
        (letsite s3 ← &mut var_v) ;;
        (letsite s4 ← #1) ;;
        vecPushBack(s3, s4) ;;
        (letsite s5 ← & var_v) ;;
        (letsite s6 ← #0) ;;
        (letsite s7 ← vecImmBorrow(s5, s6)) ;;
        (var_e_imm1 ::= s7) ;;
        (letsite s8 ← &mut var_v) ;;
        (letsite s9 ← #1) ;;
        (letsite s10 ← vecMutBorrow(s8, s9)) ;;
        (var_e_mut2 ::= s10) ;;
        ret []
    }
  ]
}

-- Module 1: mut_then_imm
private def hw_mut_then_imm : FunDef := {
  params := []
  returnType := []
  locals := [
    { name := var_v, type := .basic (.tvec .u64) },
    { name := var_e_mut1, type := .ref .u64 (.refid 1) .siteBorrowMut },
    { name := var_e_imm2, type := .ref .u64 (.refid 2) .siteBorrowImm }
  ]
  blocks := [
    { label := "b0"
      body :=
        (letsite s0 ← vecPack(.u64, [])) ;;
        (var_v ::= s0) ;;
        (letsite s1 ← &mut var_v) ;;
        (letsite s2 ← #0) ;;
        vecPushBack(s1, s2) ;;
        (letsite s3 ← &mut var_v) ;;
        (letsite s4 ← #1) ;;
        vecPushBack(s3, s4) ;;
        (letsite s5 ← &mut var_v) ;;
        (letsite s6 ← #0) ;;
        (letsite s7 ← vecMutBorrow(s5, s6)) ;;
        (var_e_mut1 ::= s7) ;;
        (letsite s8 ← & var_v) ;;
        (letsite s9 ← #1) ;;
        (letsite s10 ← vecImmBorrow(s8, s9)) ;;
        (var_e_imm2 ::= s10) ;;
        ret []
    }
  ]
}

-- Module 2: mut_then_mut
private def hw_mut_then_mut : FunDef := {
  params := []
  returnType := []
  locals := [
    { name := var_v, type := .basic (.tvec .u64) },
    { name := var_e_mut1, type := .ref .u64 (.refid 1) .siteBorrowMut },
    { name := var_e_mut2, type := .ref .u64 (.refid 2) .siteBorrowMut }
  ]
  blocks := [
    { label := "b0"
      body :=
        (letsite s0 ← vecPack(.u64, [])) ;;
        (var_v ::= s0) ;;
        (letsite s1 ← &mut var_v) ;;
        (letsite s2 ← #0) ;;
        vecPushBack(s1, s2) ;;
        (letsite s3 ← &mut var_v) ;;
        (letsite s4 ← #1) ;;
        vecPushBack(s3, s4) ;;
        (letsite s5 ← &mut var_v) ;;
        (letsite s6 ← #0) ;;
        (letsite s7 ← vecMutBorrow(s5, s6)) ;;
        (var_e_mut1 ::= s7) ;;
        (letsite s8 ← &mut var_v) ;;
        (letsite s9 ← #1) ;;
        (letsite s10 ← vecMutBorrow(s8, s9)) ;;
        (var_e_mut2 ::= s10) ;;
        ret []
    }
  ]
}

-- ----------------------------------------------------------------
-- Alpha-equivalence tests
-- ----------------------------------------------------------------

#guard
  match findFunAt (parseAndTranslate vecDoubleBorrowMvir).toOption.get! 0 with
  | some fd => alphaEquivFunDef fd hw_imm_then_mut
  | none => false

#guard
  match findFunAt (parseAndTranslate vecDoubleBorrowMvir).toOption.get! 1 with
  | some fd => alphaEquivFunDef fd hw_mut_then_imm
  | none => false

#guard
  match findFunAt (parseAndTranslate vecDoubleBorrowMvir).toOption.get! 2 with
  | some fd => alphaEquivFunDef fd hw_mut_then_mut
  | none => false
