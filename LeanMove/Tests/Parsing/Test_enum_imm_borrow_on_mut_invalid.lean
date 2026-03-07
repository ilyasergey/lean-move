/-
 Copyright Ilya Sergey
 Licensed under the Apache License, Version 2.0
-/

import LeanMove.Tests.Parsing.TestUtils
import LeanMove.Lang.Macros

/-! ## Parse Test: enum_imm_borrow_on_mut_invalid.mvir

Both modules REJECTED by Sui.
6 functions total. Testing bump_and_give (single-block) with alpha-equivalence.
-/

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Lang.MoveIR.Parser
open LeanMove.Lang.MoveIR.Translate
open LeanMove.Tests.Parsing.TestUtils

private def src :=
  include_str "../Typechecking/expressivity/accepted/enum_imm_borrow_on_mut_invalid.mvir"

#guard (parseMvir src).isOk
#guard (parseAndTranslate src).isOk
#guard (parseAndTranslate src).toOption.get!.length == 6

-- ----------------------------------------------------------------
-- bump_and_give (index 1): *copy(u) = *copy(u) + 1; return freeze(move(u))
-- ----------------------------------------------------------------

private def var_u : Var := ⟨"u"⟩
private def s (n : Nat) : Site := .site n

private def hw_bump : FunDef := {
  params := [(var_u, .ref .u64 (.paramRef var_u) .siteBorrowMut)]
  returnType := [⟨.u64, some false⟩]
  locals := []
  blocks := [
    { label := "b0"
      body :=
        (letsite (s 0) ← copy var_u) ;;
        (letsite (s 1) ← copy var_u) ;;
        (letsite (s 2) ← *(s 1)) ;;
        (letsite (s 3) ← #1) ;;
        (letsite (s 4) ← binop(.add, (s 2), (s 3))) ;;
        (*(s 0) ::= (s 4)) ;;
        (letsite (s 5) ← move var_u) ;;
        (letsite (s 6) ← freeze (s 5)) ;;
        ret [(s 6)]
    }
  ]
}

#guard
  match findFunAt (parseAndTranslate src).toOption.get! 1 with
  | some fd => alphaEquivFunDef fd hw_bump
  | none => false

-- Verify block counts for multi-block functions
#guard
  match findFunAt (parseAndTranslate src).toOption.get! 0 with
  | some fd => fd.blocks.length == 3
  | none => false

#guard
  match findFunAt (parseAndTranslate src).toOption.get! 3 with
  | some fd => fd.blocks.length == 3
  | none => false
