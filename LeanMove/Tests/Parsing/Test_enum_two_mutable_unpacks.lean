/-
 Copyright Ilya Sergey
 Licensed under the Apache License, Version 2.0
-/

import LeanMove.Tests.Parsing.TestUtils
import LeanMove.Lang.Macros

/-! ## Parse Test: enum_two_mutable_unpacks.mvir

Alpha-equivalence test for two successive mutable variant unpacks.
One module: M.create_mutable_field_addresses (single block)
-/

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Lang.MoveIR.Parser
open LeanMove.Lang.MoveIR.Translate
open LeanMove.Tests.Parsing.TestUtils

private def src :=
  include_str "../Typechecking/expressivity/accepted/enum_two_mutable_unpacks.mvir"

#guard (parseMvir src).isOk
#guard (parseAndTranslate src).isOk
#guard (parseAndTranslate src).toOption.get!.length == 1

-- ----------------------------------------------------------------
-- Hand-written FunDef
-- ----------------------------------------------------------------

private def var_addr : Var := ⟨"addr"⟩
private def var_a_ref : Var := ⟨"a_ref"⟩
private def var_b_ref : Var := ⟨"b_ref"⟩
private def var_aa_ref : Var := ⟨"aa_ref"⟩
private def var_bb_ref : Var := ⟨"bb_ref"⟩
private def s (n : Nat) : Site := .site n

private def fooVariants : AssocMap Id (AssocMap Field BasicMoveType) :=
  AssocMap.mk [
    ("V", AssocMap.mk [(⟨"b"⟩, .u64), (⟨"a"⟩, .u64)])
  ]

private def fooType : BasicMoveType := .tenum "Foo" fooVariants

private def hw_fn : FunDef := {
  params := [(var_addr, .ref fooType (.paramRef var_addr) .siteBorrowMut)]
  returnType := []
  locals := [
    { name := var_a_ref, type := .ref .u64 (.refid 1) .siteBorrowMut },
    { name := var_b_ref, type := .ref .u64 (.refid 2) .siteBorrowMut },
    { name := var_aa_ref, type := .ref .u64 (.refid 3) .siteBorrowMut },
    { name := var_bb_ref, type := .ref .u64 (.refid 4) .siteBorrowMut }
  ]
  blocks := [
    { label := "b0"
      body :=
        (letsite (s 0) ← copy var_addr) ;;
        unpackVariant("V", [(⟨"a"⟩, (s 1)), (⟨"b"⟩, (s 2))], (s 0)) ;;
        (var_a_ref ::= (s 1)) ;;
        (var_b_ref ::= (s 2)) ;;
        (letsite (s 3) ← copy var_addr) ;;
        unpackVariant("V", [(⟨"a"⟩, (s 4)), (⟨"b"⟩, (s 5))], (s 3)) ;;
        (var_aa_ref ::= (s 4)) ;;
        (var_bb_ref ::= (s 5)) ;;
        (letsite (s 6) ← move var_a_ref) ;;
        release (s 6) ;;
        (letsite (s 7) ← move var_b_ref) ;;
        release (s 7) ;;
        (letsite (s 8) ← move var_aa_ref) ;;
        release (s 8) ;;
        (letsite (s 9) ← move var_bb_ref) ;;
        release (s 9) ;;
        (letsite (s 10) ← move var_addr) ;;
        release (s 10) ;;
        ret []
    }
  ]
}

-- Alpha-equivalence test
#guard
  match findFunInModule (parseAndTranslate src).toOption.get!
          "M" "create_mutable_field_addresses" with
  | some fd => alphaEquivFunDef fd hw_fn
  | none => false
