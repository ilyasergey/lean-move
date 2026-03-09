/-
 Copyright Ilya Sergey
 Licensed under the Apache License, Version 2.0
-/

import LeanMove.Tests.Parsing.TestUtils
import LeanMove.Lang.Macros

/-! ## Parse Test: vec_basic_ops.mvir

Alpha-equivalence tests for basic vector operations (accepted).
Seven modules: vec_pack_empty, vec_pack_elems, vec_len, vec_push,
vec_pop, vec_swap, vec_unpack.
-/

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Lang.MoveIR.Parser
open LeanMove.Lang.MoveIR.Translate
open LeanMove.Tests.Parsing.TestUtils

private def vecBasicOpsMvir :=
  include_str "../MVIR/vec_basic_ops.mvir"

#guard (parseMvir vecBasicOpsMvir).isOk
#guard (parseAndTranslate vecBasicOpsMvir).isOk
#guard (parseAndTranslate vecBasicOpsMvir).toOption.get!.length == 7

-- ----------------------------------------------------------------
-- Hand-written FunDefs
-- ----------------------------------------------------------------

private def var_v : Var := ⟨"v"⟩
private def var_a : Var := ⟨"a"⟩
private def var_b : Var := ⟨"b"⟩
private def var_val : Var := ⟨"val"⟩
private def var_i : Var := ⟨"i"⟩
private def var_j : Var := ⟨"j"⟩
private def s (n : Nat) : Site := .site n

-- Module 0: vec_pack_empty
-- t(): vector<u64> {
--   return vec_pack_0<u64>();
-- }
private def hw_pack_empty : FunDef := {
  params := []
  returnType := [⟨.tvec .u64, none⟩]
  locals := []
  blocks := [
    { label := "b0"
      body :=
        (letsite (s 0) ← vecPack(.u64, [])) ;;
        ret [(s 0)]
    }
  ]
}

-- Module 1: vec_pack_elems
-- t(): vector<u64> {
--   a = 0; b = 1;
--   return vec_pack_2<u64>(copy(a), copy(b));
-- }
private def hw_pack_elems : FunDef := {
  params := []
  returnType := [⟨.tvec .u64, none⟩]
  locals := [
    { name := var_a, type := .basic .u64 },
    { name := var_b, type := .basic .u64 }
  ]
  blocks := [
    { label := "b0"
      body :=
        (letsite (s 0) ← #0) ;;
        (var_a ::= (s 0)) ;;
        (letsite (s 1) ← #1) ;;
        (var_b ::= (s 1)) ;;
        (letsite (s 2) ← copy var_a) ;;
        (letsite (s 3) ← copy var_b) ;;
        (letsite (s 4) ← vecPack(.u64, [(s 2), (s 3)])) ;;
        ret [(s 4)]
    }
  ]
}

-- Module 2: vec_len
-- t(v: &vector<u64>): u64 {
--   return vec_len<u64>(move(v));
-- }
private def hw_len : FunDef := {
  params := [(var_v, .ref (.tvec .u64) (.paramRef var_v) .siteBorrowImm)]
  returnType := [⟨.u64, none⟩]
  locals := []
  blocks := [
    { label := "b0"
      body :=
        (letsite (s 0) ← move var_v) ;;
        (letsite (s 1) ← vecLen((s 0))) ;;
        ret [(s 1)]
    }
  ]
}

-- Module 3: vec_push
-- t(v: &mut vector<u64>) {
--   val = 42;
--   _ = vec_push_back<u64>(move(v), move(val));
--   return;
-- }
private def hw_push : FunDef := {
  params := [(var_v, .ref (.tvec .u64) (.paramRef var_v) .siteBorrowMut)]
  returnType := []
  locals := [
    { name := var_val, type := .basic .u64 }
  ]
  blocks := [
    { label := "b0"
      body :=
        (letsite (s 0) ← #42) ;;
        (var_val ::= (s 0)) ;;
        (letsite (s 1) ← move var_v) ;;
        (letsite (s 2) ← move var_val) ;;
        vecPushBack((s 1), (s 2)) ;;
        ret []
    }
  ]
}

-- Module 4: vec_pop
-- t(v: &mut vector<u64>): u64 {
--   val = vec_pop_back<u64>(move(v));
--   return move(val);
-- }
private def hw_pop : FunDef := {
  params := [(var_v, .ref (.tvec .u64) (.paramRef var_v) .siteBorrowMut)]
  returnType := [⟨.u64, none⟩]
  locals := [
    { name := var_val, type := .basic .u64 }
  ]
  blocks := [
    { label := "b0"
      body :=
        (letsite (s 0) ← move var_v) ;;
        (letsite (s 1) ← vecPopBack((s 0))) ;;
        (var_val ::= (s 1)) ;;
        (letsite (s 2) ← move var_val) ;;
        ret [(s 2)]
    }
  ]
}

-- Module 5: vec_swap
-- t(v: &mut vector<u64>) {
--   i = 0; j = 1;
--   _ = vec_swap<u64>(move(v), move(i), move(j));
--   return;
-- }
private def hw_swap : FunDef := {
  params := [(var_v, .ref (.tvec .u64) (.paramRef var_v) .siteBorrowMut)]
  returnType := []
  locals := [
    { name := var_i, type := .basic .u64 },
    { name := var_j, type := .basic .u64 }
  ]
  blocks := [
    { label := "b0"
      body :=
        (letsite (s 0) ← #0) ;;
        (var_i ::= (s 0)) ;;
        (letsite (s 1) ← #1) ;;
        (var_j ::= (s 1)) ;;
        (letsite (s 2) ← move var_v) ;;
        (letsite (s 3) ← move var_i) ;;
        (letsite (s 4) ← move var_j) ;;
        vecSwap((s 2), (s 3), (s 4)) ;;
        ret []
    }
  ]
}

-- Module 6: vec_unpack
-- t(v: vector<u64>): u64 * u64 {
--   a, b = vec_unpack_2<u64>(move(v));
--   return move(a), move(b);
-- }
private def hw_unpack : FunDef := {
  params := [(var_v, .basic (.tvec .u64))]
  returnType := [⟨.u64, none⟩, ⟨.u64, none⟩]
  locals := [
    { name := var_a, type := .basic .u64 },
    { name := var_b, type := .basic .u64 }
  ]
  blocks := [
    { label := "b0"
      body :=
        (letsite (s 0) ← move var_v) ;;
        vecUnpack(.u64, [(s 1), (s 2)], (s 0)) ;;
        (var_a ::= (s 1)) ;;
        (var_b ::= (s 2)) ;;
        (letsite (s 3) ← move var_a) ;;
        (letsite (s 4) ← move var_b) ;;
        ret [(s 3), (s 4)]
    }
  ]
}

-- ----------------------------------------------------------------
-- Alpha-equivalence tests
-- ----------------------------------------------------------------

#guard
  match findFunInModule (parseAndTranslate vecBasicOpsMvir).toOption.get!
          "vec_pack_empty" "t" with
  | some fd => alphaEquivFunDef fd hw_pack_empty
  | none => false

#guard
  match findFunInModule (parseAndTranslate vecBasicOpsMvir).toOption.get!
          "vec_pack_elems" "t" with
  | some fd => alphaEquivFunDef fd hw_pack_elems
  | none => false

#guard
  match findFunInModule (parseAndTranslate vecBasicOpsMvir).toOption.get!
          "vec_len" "t" with
  | some fd => alphaEquivFunDef fd hw_len
  | none => false

#guard
  match findFunInModule (parseAndTranslate vecBasicOpsMvir).toOption.get!
          "vec_push" "t" with
  | some fd => alphaEquivFunDef fd hw_push
  | none => false

#guard
  match findFunInModule (parseAndTranslate vecBasicOpsMvir).toOption.get!
          "vec_pop" "t" with
  | some fd => alphaEquivFunDef fd hw_pop
  | none => false

#guard
  match findFunInModule (parseAndTranslate vecBasicOpsMvir).toOption.get!
          "vec_swap" "t" with
  | some fd => alphaEquivFunDef fd hw_swap
  | none => false

#guard
  match findFunInModule (parseAndTranslate vecBasicOpsMvir).toOption.get!
          "vec_unpack" "t" with
  | some fd => alphaEquivFunDef fd hw_unpack
  | none => false
