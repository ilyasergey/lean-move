/-
 Copyright Ilya Sergey
 Licensed under the Apache License, Version 2.0
-/

import LeanMove.Tests.Parsing.TestUtils
import LeanMove.Lang.Macros

/-! ## Parse Test: vec_borrow_sequential.mvir

Alpha-equivalence tests for sequential vector borrow operations (accepted).
Three modules: vec_imm_borrow_read, vec_multi_imm_borrow, vec_mut_borrow_write.
-/

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Lang.MoveIR.Parser
open LeanMove.Lang.MoveIR.Translate
open LeanMove.Tests.Parsing.TestUtils

private def vecBorrowSeqMvir :=
  include_str "../MVIR/vec_borrow_sequential.mvir"

#guard (parseMvir vecBorrowSeqMvir).isOk
#guard (parseAndTranslate vecBorrowSeqMvir).isOk
#guard (parseAndTranslate vecBorrowSeqMvir).toOption.get!.length == 3

-- ----------------------------------------------------------------
-- Hand-written FunDefs
-- ----------------------------------------------------------------

private def var_v : Var := ⟨"v"⟩
private def var_r : Var := ⟨"r"⟩
private def var_r1 : Var := ⟨"r1"⟩
private def var_r2 : Var := ⟨"r2"⟩
private def s (n : Nat) : Site := .site n

-- Module 0: vec_imm_borrow_read
-- t(v: &vector<u64>): u64 {
--   r = vec_imm_borrow<u64>(copy(v), 0);
--   return *move(r);
-- }
private def hw_imm_borrow_read : FunDef := {
  params := [(var_v, .ref (.tvec .u64) (.paramRef var_v) .siteBorrowImm)]
  returnType := [⟨.u64, none⟩]
  locals := [
    { name := var_r, type := .ref .u64 (.refid 1) .siteBorrowImm }
  ]
  blocks := [
    { label := "b0"
      body :=
        (letsite (s 0) ← copy var_v) ;;
        (letsite (s 1) ← #0) ;;
        (letsite (s 2) ← vecImmBorrow((s 0), (s 1))) ;;
        (var_r ::= (s 2)) ;;
        (letsite (s 3) ← move var_r) ;;
        (letsite (s 4) ← *(s 3)) ;;
        ret [(s 4)]
    }
  ]
}

-- Module 1: vec_multi_imm_borrow
-- t(v: &vector<u64>): u64 {
--   r1 = vec_imm_borrow<u64>(copy(v), 0);
--   r2 = vec_imm_borrow<u64>(move(v), 1);
--   _ = *move(r1);
--   return *move(r2);
-- }
private def hw_multi_imm_borrow : FunDef := {
  params := [(var_v, .ref (.tvec .u64) (.paramRef var_v) .siteBorrowImm)]
  returnType := [⟨.u64, none⟩]
  locals := [
    { name := var_r1, type := .ref .u64 (.refid 1) .siteBorrowImm },
    { name := var_r2, type := .ref .u64 (.refid 2) .siteBorrowImm }
  ]
  blocks := [
    { label := "b0"
      body :=
        (letsite (s 0) ← copy var_v) ;;
        (letsite (s 1) ← #0) ;;
        (letsite (s 2) ← vecImmBorrow((s 0), (s 1))) ;;
        (var_r1 ::= (s 2)) ;;
        (letsite (s 3) ← move var_v) ;;
        (letsite (s 4) ← #1) ;;
        (letsite (s 5) ← vecImmBorrow((s 3), (s 4))) ;;
        (var_r2 ::= (s 5)) ;;
        -- _ = *move(r1) → discard + release
        (letsite (s 6) ← move var_r1) ;;
        (letsite (s 7) ← *(s 6)) ;;
        release (s 7) ;;
        -- return *move(r2)
        (letsite (s 8) ← move var_r2) ;;
        (letsite (s 9) ← *(s 8)) ;;
        ret [(s 9)]
    }
  ]
}

-- Module 2: vec_mut_borrow_write
-- t(v: &mut vector<u64>) {
--   r = vec_mut_borrow<u64>(copy(v), 0);
--   *move(r) = 99;
--   return;
-- }
private def hw_mut_borrow_write : FunDef := {
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
        (letsite (s 3) ← move var_r) ;;
        (letsite (s 4) ← #99) ;;
        Stmt.writeRef (s 3) (s 4) (ret [])
    }
  ]
}

-- ----------------------------------------------------------------
-- Alpha-equivalence tests
-- ----------------------------------------------------------------

#guard
  match findFunInModule (parseAndTranslate vecBorrowSeqMvir).toOption.get!
          "vec_imm_borrow_read" "t" with
  | some fd => alphaEquivFunDef fd hw_imm_borrow_read
  | none => false

#guard
  match findFunInModule (parseAndTranslate vecBorrowSeqMvir).toOption.get!
          "vec_multi_imm_borrow" "t" with
  | some fd => alphaEquivFunDef fd hw_multi_imm_borrow
  | none => false

#guard
  match findFunInModule (parseAndTranslate vecBorrowSeqMvir).toOption.get!
          "vec_mut_borrow_write" "t" with
  | some fd => alphaEquivFunDef fd hw_mut_borrow_write
  | none => false
