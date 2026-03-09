/-
 Copyright Ilya Sergey
 Licensed under the Apache License, Version 2.0
-/

import LeanMove.Tests.Parsing.TestUtils
import LeanMove.Lang.Macros

/-! ## Parse Test: vec_move_after_borrow.mvir

Alpha-equivalence tests for vector move after borrow rejection tests.
Two modules: move after imm borrow, move after mut borrow.
-/

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Lang.MoveIR.Parser
open LeanMove.Lang.MoveIR.Translate
open LeanMove.Tests.Parsing.TestUtils

private def vecMoveAfterBorrowMvir :=
  include_str "../MVIR/vec_move_after_borrow.mvir"

#guard (parseMvir vecMoveAfterBorrowMvir).isOk
#guard (parseAndTranslate vecMoveAfterBorrowMvir).isOk
#guard (parseAndTranslate vecMoveAfterBorrowMvir).toOption.get!.length == 2

-- ----------------------------------------------------------------
-- Hand-written FunDefs
-- ----------------------------------------------------------------

private def var_v : Var := ⟨"v"⟩
private def var_e_imm : Var := ⟨"e_imm"⟩
private def var_e_mut : Var := ⟨"e_mut"⟩
private def s (n : Nat) : Site := .site n

-- Module 0: move after imm borrow
-- v = vec_pack_0<u64>();
-- vec_push_back<u64>(&mut v, 0);
-- e_imm = vec_imm_borrow<u64>(&v, 0);
-- _ = move(v);
-- return;
private def hw_move_after_imm : FunDef := {
  params := []
  returnType := []
  locals := [
    { name := var_v, type := .basic (.tvec .u64) },
    { name := var_e_imm, type := .ref .u64 (.refid 1) .siteBorrowImm }
  ]
  blocks := [
    { label := "b0"
      body :=
        (letsite (s 0) ← vecPack(.u64, [])) ;;
        (var_v ::= (s 0)) ;;
        (letsite (s 1) ← &mut var_v) ;;
        (letsite (s 2) ← #0) ;;
        vecPushBack((s 1), (s 2)) ;;
        (letsite (s 3) ← & var_v) ;;
        (letsite (s 4) ← #0) ;;
        (letsite (s 5) ← vecImmBorrow((s 3), (s 4))) ;;
        (var_e_imm ::= (s 5)) ;;
        (letsite (s 6) ← move var_v) ;;
        release (s 6) ;;
        ret []
    }
  ]
}

-- Module 1: move after mut borrow
-- v = vec_pack_0<u64>();
-- vec_push_back<u64>(&mut v, 0);
-- e_mut = vec_mut_borrow<u64>(&mut v, 0);
-- _ = move(v);
-- return;
private def hw_move_after_mut : FunDef := {
  params := []
  returnType := []
  locals := [
    { name := var_v, type := .basic (.tvec .u64) },
    { name := var_e_mut, type := .ref .u64 (.refid 1) .siteBorrowMut }
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
        (letsite (s 4) ← #0) ;;
        (letsite (s 5) ← vecMutBorrow((s 3), (s 4))) ;;
        (var_e_mut ::= (s 5)) ;;
        (letsite (s 6) ← move var_v) ;;
        release (s 6) ;;
        ret []
    }
  ]
}

-- ----------------------------------------------------------------
-- Alpha-equivalence tests
-- ----------------------------------------------------------------

#guard
  match findFunAt (parseAndTranslate vecMoveAfterBorrowMvir).toOption.get! 0 with
  | some fd => alphaEquivFunDef fd hw_move_after_imm
  | none => false

#guard
  match findFunAt (parseAndTranslate vecMoveAfterBorrowMvir).toOption.get! 1 with
  | some fd => alphaEquivFunDef fd hw_move_after_mut
  | none => false
