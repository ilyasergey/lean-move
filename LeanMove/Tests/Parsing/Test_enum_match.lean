/-
 Copyright Ilya Sergey
 Licensed under the Apache License, Version 2.0
-/

import LeanMove.Tests.Parsing.TestUtils
import LeanMove.Lang.Macros

/-! ## Parse Test: enum_match.mvir

Alpha-equivalence tests for basic enum variant_switch (accepted).
One module: m.t0
-/

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Lang.MoveIR.Parser
open LeanMove.Lang.MoveIR.Translate
open LeanMove.Tests.Parsing.TestUtils

private def enumMatchMvir :=
  include_str "../Typechecking/expressivity/accepted/enum_match.mvir"

#guard (parseMvir enumMatchMvir).isOk
#guard (parseAndTranslate enumMatchMvir).isOk
#guard (parseAndTranslate enumMatchMvir).toOption.get!.length == 1

-- ----------------------------------------------------------------
-- Hand-written FunDef for m.t0
-- ----------------------------------------------------------------

private def var_loc3 : Var := ⟨"loc3"⟩
private def var_loc1 : Var := ⟨"loc1"⟩
private def var_inner : Var := ⟨"inner"⟩
private def var_copier : Var := ⟨"copier"⟩
private def s (n : Nat) : Site := .site n

private def threesType : BasicMoveType :=
  .tenum "m.Threes"

private def hw_t0 : FunDef := {
  params := []
  returnType := [⟨.u64, none⟩]
  locals := [
    { name := var_loc3, type := .basic .u64 },
    { name := var_loc1, type := .basic threesType },
    { name := var_inner, type := .basic .u64 },
    { name := var_copier, type := .basic .u64 }
  ]
  blocks := [
    { label := "b0"
      body :=
        (letsite (s 0) ← #0) ;;
        (letsite (s 1) ← packVariant("m.Threes", "Three", [(⟨"pos0"⟩, (s 0))])) ;;
        (var_loc1 ::= (s 1)) ;;
        (fun cont => Stmt.letBind (s 2) (Expr.usage (Usage.borrowImm var_loc1)) cont) ;;
        Stmt.variantSwitch (s 2) [("One", "b1"), ("Two", "b2"), ("Three", "b3")]
    },
    { label := "b1"
      body :=
        (letsite (s 3) ← move var_loc1) ;;
        unpackVariant("One", [(⟨"pos0"⟩, (s 4))], (s 3)) ;;
        (var_copier ::= (s 4)) ;;
        (letsite (s 5) ← #1) ;;
        (var_loc3 ::= (s 5)) ;;
        jump "b4"
    },
    { label := "b2"
      body :=
        (letsite (s 6) ← move var_loc1) ;;
        unpackVariant("Two", [], (s 6)) ;;
        (letsite (s 7) ← #1) ;;
        (var_loc3 ::= (s 7)) ;;
        jump "b4"
    },
    { label := "b3"
      body :=
        (letsite (s 8) ← move var_loc1) ;;
        unpackVariant("Three", [(⟨"pos0"⟩, (s 9))], (s 8)) ;;
        (var_inner ::= (s 9)) ;;
        (letsite (s 10) ← copy var_inner) ;;
        (var_copier ::= (s 10)) ;;
        (letsite (s 11) ← copy var_copier) ;;
        (var_loc3 ::= (s 11)) ;;
        jump "b4"
    },
    { label := "b4"
      body :=
        (letsite (s 12) ← move var_loc3) ;;
        ret [(s 12)]
    }
  ]
}

-- ----------------------------------------------------------------
-- Alpha-equivalence test
-- ----------------------------------------------------------------

#guard
  match findFunInModule (parseAndTranslate enumMatchMvir).toOption.get!
          "m" "t0" with
  | some fd => alphaEquivFunDef fd hw_t0
  | none => false
