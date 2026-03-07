/-
 Copyright Ilya Sergey
 Licensed under the Apache License, Version 2.0
-/

import LeanMove.Tests.Parsing.TestUtils
import LeanMove.Lang.Macros

/-! ## Parse Test: vec_mixed_borrow.mvir

Alpha-equivalence tests for vector mixed borrow rejection test.
Module: 0x2.vector_ops_mixed_borrow with functions foo and test.
-/

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Lang.MoveIR.Parser
open LeanMove.Lang.MoveIR.Translate
open LeanMove.Tests.Parsing.TestUtils

private def vecMixedBorrowMvir :=
  include_str "../Typechecking/expressivity/rejected/vec_mixed_borrow.mvir"

#guard (parseMvir vecMixedBorrowMvir).isOk
#guard (parseAndTranslate vecMixedBorrowMvir).isOk

-- Two functions: foo and test
#guard (parseAndTranslate vecMixedBorrowMvir).toOption.get!.length == 2

-- ----------------------------------------------------------------
-- Hand-written FunDefs
-- ----------------------------------------------------------------

private def var_m : Var := ⟨"m"⟩
private def var_v : Var := ⟨"v"⟩
private def var_i : Var := ⟨"i"⟩
private def var_uu : Var := ⟨"_"⟩
private def s (n : Nat) : Site := .site n

-- Function: foo(m: &mut u8) { return; }
private def hw_foo : FunDef := {
  params := [(var_m, .ref .u8 (.paramRef var_m) .siteBorrowMut)]
  returnType := []
  locals := []
  blocks := [
    { label := "l0"
      body := ret []
    }
  ]
}

-- Function: test(v: &mut vector<u8>)
-- m = vec_mut_borrow<u8>(copy(v), 0);
-- i = vec_imm_borrow<u8>(move(v), 0);
-- Self.foo(move(m));
-- _ = *move(i);
-- return;
private def hw_test : FunDef := {
  params := [(var_v, .ref (.tvec .u8) (.paramRef var_v) .siteBorrowMut)]
  returnType := []
  locals := [
    { name := var_m, type := .ref .u8 (.refid 1) .siteBorrowMut },
    { name := var_i, type := .ref .u8 (.refid 2) .siteBorrowImm }
  ]
  blocks := [
    { label := "l0"
      body :=
        (letsite (s 0) ← copy var_v) ;;
        (letsite (s 1) ← #0) ;;
        (letsite (s 2) ← vecMutBorrow((s 0), (s 1))) ;;
        (var_m ::= (s 2)) ;;
        (letsite (s 3) ← move var_v) ;;
        (letsite (s 4) ← #0) ;;
        (letsite (s 5) ← vecImmBorrow((s 3), (s 4))) ;;
        (var_i ::= (s 5)) ;;
        -- Self.foo(move(m)) → call with result site and assign to "_"
        (letsite (s 6) ← move var_m) ;;
        Stmt.call [(s 7)] "vector_ops_mixed_borrow.foo" [(s 6)]
          (Stmt.assign var_uu (s 7)
        -- _ = *move(i) → discard + release
        ((letsite (s 8) ← move var_i) ;;
         (letsite (s 9) ← *(s 8)) ;;
         release (s 9) ;;
         ret []))
    }
  ]
}

-- ----------------------------------------------------------------
-- Alpha-equivalence tests
-- ----------------------------------------------------------------

#guard
  match findFunInModule (parseAndTranslate vecMixedBorrowMvir).toOption.get!
          "vector_ops_mixed_borrow" "foo" with
  | some fd => alphaEquivFunDef fd hw_foo
  | none => false

#guard
  match findFunInModule (parseAndTranslate vecMixedBorrowMvir).toOption.get!
          "vector_ops_mixed_borrow" "test" with
  | some fd => alphaEquivFunDef fd hw_test
  | none => false
