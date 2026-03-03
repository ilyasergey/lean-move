/-
 Copyright Ilya Sergey
 Licensed under the Apache License, Version 2.0
-/

import LeanMove.Tests.Parsing.TestUtils
import LeanMove.Lang.Macros

/-! ## Parse Test: vec_dangling_borrow.mvir

Alpha-equivalence tests for vector dangling borrow rejection tests.
Three modules: vec_push_while_borrow, vec_pop_while_borrow, vec_write_while_borrow.
-/

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Lang.MoveIR.Parser
open LeanMove.Lang.MoveIR.Translate
open LeanMove.Tests.Parsing.TestUtils

private def vecDanglingBorrowMvir :=
  include_str "../Typechecking/expressivity/rejected/vec_dangling_borrow.mvir"

#guard (parseMvir vecDanglingBorrowMvir).isOk
#guard (parseAndTranslate vecDanglingBorrowMvir).isOk
#guard (parseAndTranslate vecDanglingBorrowMvir).toOption.get!.length == 3

-- ----------------------------------------------------------------
-- Hand-written FunDefs
-- ----------------------------------------------------------------

private def var_v : Var := ⟨"v"⟩
private def var_r : Var := ⟨"r"⟩
private def var_val : Var := ⟨"val"⟩
private def s (n : Nat) : Site := .site n

-- Module 0: vec_push_while_borrow
-- t(v: &mut vector<u64>) {
--   r = vec_imm_borrow<u64>(copy(v), 0);
--   val = 42;
--   _ = vec_push_back<u64>(copy(v), move(val));
--   return;
-- }
private def hw_push_while_borrow : FunDef := {
  params := [(var_v, .ref (.tvec .u64) (.paramRef var_v) .siteBorrowMut)]
  returnType := []
  locals := [
    { name := var_r, type := .ref .u64 (.refid 1) .siteBorrowImm },
    { name := var_val, type := .basic .u64 }
  ]
  blocks := [
    { label := "b0"
      body :=
        (letsite (s 0) ← copy var_v) ;;
        (letsite (s 1) ← #0) ;;
        (letsite (s 2) ← vecImmBorrow((s 0), (s 1))) ;;
        (var_r ::= (s 2)) ;;
        (letsite (s 3) ← #42) ;;
        (var_val ::= (s 3)) ;;
        (letsite (s 4) ← copy var_v) ;;
        (letsite (s 5) ← move var_val) ;;
        vecPushBack((s 4), (s 5)) ;;
        ret []
    }
  ]
}

-- Module 1: vec_pop_while_borrow
-- t(v: &mut vector<u64>) {
--   r = vec_imm_borrow<u64>(copy(v), 0);
--   val = vec_pop_back<u64>(copy(v));
--   return;
-- }
private def hw_pop_while_borrow : FunDef := {
  params := [(var_v, .ref (.tvec .u64) (.paramRef var_v) .siteBorrowMut)]
  returnType := []
  locals := [
    { name := var_r, type := .ref .u64 (.refid 1) .siteBorrowImm },
    { name := var_val, type := .basic .u64 }
  ]
  blocks := [
    { label := "b0"
      body :=
        (letsite (s 0) ← copy var_v) ;;
        (letsite (s 1) ← #0) ;;
        (letsite (s 2) ← vecImmBorrow((s 0), (s 1))) ;;
        (var_r ::= (s 2)) ;;
        (letsite (s 3) ← copy var_v) ;;
        (letsite (s 4) ← vecPopBack((s 3))) ;;
        (var_val ::= (s 4)) ;;
        ret []
    }
  ]
}

-- Module 2: vec_write_while_borrow
-- t(v: &mut vector<u64>) {
--   r = vec_mut_borrow<u64>(copy(v), 0);
--   *copy(v) = vec_pack_0<u64>();
--   return;
-- }
private def hw_write_while_borrow : FunDef := {
  params := [(var_v, .ref (.tvec .u64) (.paramRef var_v) .siteBorrowMut)]
  returnType := []
  locals := [
    { name := var_r, type := .ref .u64 (.refid 1) .siteBorrowMut }
  ]
  blocks := [
    { label := "b0"
      body :=
        (letsite (s 0) ← copy var_v) ;;
        (letsite (s 1) ← #0) ;;
        (letsite (s 2) ← vecMutBorrow((s 0), (s 1))) ;;
        (var_r ::= (s 2)) ;;
        (letsite (s 3) ← copy var_v) ;;
        (letsite (s 4) ← vecPack(.u64, [])) ;;
        Stmt.writeRef (s 3) (s 4) (ret [])
    }
  ]
}

-- ----------------------------------------------------------------
-- Alpha-equivalence tests
-- ----------------------------------------------------------------

#guard
  match findFunInModule (parseAndTranslate vecDanglingBorrowMvir).toOption.get!
          "vec_push_while_borrow" "t" with
  | some fd => alphaEquivFunDef fd hw_push_while_borrow
  | none => false

#guard
  match findFunInModule (parseAndTranslate vecDanglingBorrowMvir).toOption.get!
          "vec_pop_while_borrow" "t" with
  | some fd => alphaEquivFunDef fd hw_pop_while_borrow
  | none => false

#guard
  match findFunInModule (parseAndTranslate vecDanglingBorrowMvir).toOption.get!
          "vec_write_while_borrow" "t" with
  | some fd => alphaEquivFunDef fd hw_write_while_borrow
  | none => false
