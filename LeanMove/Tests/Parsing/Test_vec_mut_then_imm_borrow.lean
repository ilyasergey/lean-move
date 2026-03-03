/-
 Copyright Ilya Sergey
 Licensed under the Apache License, Version 2.0
-/

import LeanMove.Tests.Parsing.TestUtils
import LeanMove.Lang.Macros

/-! ## Parse Test: vec_mut_then_imm_borrow.mvir

Alpha-equivalence test for vector mut-then-imm borrow (accepted).
-/

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Lang.MoveIR.Parser
open LeanMove.Lang.MoveIR.Translate
open LeanMove.Tests.Parsing.TestUtils

private def vecMutThenImmBorrowMvir :=
  include_str "../Typechecking/expressivity/accepted/vec_mut_then_imm_borrow.mvir"

#guard (parseMvir vecMutThenImmBorrowMvir).isOk
#guard (parseAndTranslate vecMutThenImmBorrowMvir).isOk
#guard (parseAndTranslate vecMutThenImmBorrowMvir).toOption.get!.length == 1

-- ----------------------------------------------------------------
-- Hand-written FunDef
-- ----------------------------------------------------------------

private def var_v : Var := ⟨"v"⟩
private def var_e_mut1 : Var := ⟨"e_mut1"⟩
private def var_e_imm2 : Var := ⟨"e_imm2"⟩
private def s (n : Nat) : Site := .site n

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
        (letsite (s 0) ← vecPack(.u64, [])) ;;
        (var_v ::= (s 0)) ;;
        (letsite (s 1) ← &mut var_v) ;;
        (letsite (s 2) ← #0) ;;
        vecPushBack((s 1), (s 2)) ;;
        (letsite (s 3) ← &mut var_v) ;;
        (letsite (s 4) ← #1) ;;
        vecPushBack((s 3), (s 4)) ;;
        (letsite (s 5) ← &mut var_v) ;;
        (letsite (s 6) ← #0) ;;
        (letsite (s 7) ← vecMutBorrow((s 5), (s 6))) ;;
        (var_e_mut1 ::= (s 7)) ;;
        (letsite (s 8) ← & var_v) ;;
        (letsite (s 9) ← #1) ;;
        (letsite (s 10) ← vecImmBorrow((s 8), (s 9))) ;;
        (var_e_imm2 ::= (s 10)) ;;
        ret []
    }
  ]
}

-- ----------------------------------------------------------------
-- Alpha-equivalence test
-- ----------------------------------------------------------------

#guard
  match findFunAt (parseAndTranslate vecMutThenImmBorrowMvir).toOption.get! 0 with
  | some fd => alphaEquivFunDef fd hw_mut_then_imm
  | none => false
