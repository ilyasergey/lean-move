/-
 Copyright Ilya Sergey
 Licensed under the Apache License, Version 2.0
-/

import LeanMove.Tests.Parsing.TestUtils
import LeanMove.Lang.Macros

/-! ## Parse Test: comparison_ops.mvir

Regression test for the six comparison instructions `Eq`, `Neq`, `Lt`, `Gt`,
`Le` and `Ge`.

`!=`, `>`, `<=` and `>=` are the interesting ones: they have always parsed, but
until the corresponding opcodes existed the translator mapped them through a
`_ => Binop.add` fallback, silently turning every one of them into integer
addition. Alpha-equivalence against hand-written ASTs pins each operator to its
own opcode, so the fallback cannot reappear unnoticed.
-/

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Lang.MoveIR.Parser
open LeanMove.Lang.MoveIR.Translate
open LeanMove.Tests.Parsing.TestUtils

private def src :=
  include_str "../MVIR/comparison_ops.mvir"

#guard (parseMvir src).isOk
#guard (parseAndTranslate src).isOk
#guard (parseAndTranslate src).toOption.get!.length == 8

private def var_a : Var := ⟨"a"⟩
private def var_b : Var := ⟨"b"⟩
private def s (n : Nat) : Site := .site n

/-- `cmp(a, b)` for a comparison `op` on two `u64` parameters:
    `return copy(a) op copy(b);` -/
private def hw_cmp (op : Binop) (argType : BasicMoveType := .u64) : FunDef := {
  params := [(var_a, .basic argType), (var_b, .basic argType)]
  returnType := [⟨.tbool, none⟩]
  locals := []
  blocks := [
    { label := "b0"
      body :=
        (letsite (s 0) ← copy var_a) ;;
        (letsite (s 1) ← copy var_b) ;;
        (letsite (s 2) ← binop(op, (s 0), (s 1))) ;;
        ret [(s 2)]
    }
  ]
}

private def parsedAt (i : Nat) : FunDef :=
  (findFunAt (parseAndTranslate src).toOption.get! i).get!

-- Each operator maps to its own opcode, in source order:
-- eq, neq, lt, gt, le, ge, neq_bool, ge_branch.
#guard alphaEquivFunDef (parsedAt 0) (hw_cmp .eq)
#guard alphaEquivFunDef (parsedAt 1) (hw_cmp .neq)
#guard alphaEquivFunDef (parsedAt 2) (hw_cmp .lt)
#guard alphaEquivFunDef (parsedAt 3) (hw_cmp .gt)
#guard alphaEquivFunDef (parsedAt 4) (hw_cmp .le)
#guard alphaEquivFunDef (parsedAt 5) (hw_cmp .ge)

-- `Neq` is defined at every comparable type, `bool` included.
#guard alphaEquivFunDef (parsedAt 6) (hw_cmp .neq .tbool)

-- ... and the operators really are distinguished from one another: the old
-- fallback collapsed all four of `!=`, `>`, `<=`, `>=` onto `add`.
#guard !alphaEquivFunDef (parsedAt 1) (hw_cmp .add)
#guard !alphaEquivFunDef (parsedAt 3) (hw_cmp .add)
#guard !alphaEquivFunDef (parsedAt 4) (hw_cmp .add)
#guard !alphaEquivFunDef (parsedAt 5) (hw_cmp .add)

-- ----------------------------------------------------------------
-- ge_branch: a comparison feeding a `jump_if`
-- ----------------------------------------------------------------

private def hw_ge_branch : FunDef := {
  params := [(var_a, .basic .u64), (var_b, .basic .u64)]
  returnType := [⟨.u64, none⟩]
  locals := []
  blocks := [
    { label := "b0"
      body :=
        (letsite (s 0) ← copy var_a) ;;
        (letsite (s 1) ← copy var_b) ;;
        (letsite (s 2) ← binop(.ge, (s 0), (s 1))) ;;
        branch (s 2) "b2" "b1"
    },
    { label := "b1"
      body :=
        (letsite (s 3) ← copy var_b) ;;
        ret [(s 3)]
    },
    { label := "b2"
      body :=
        (letsite (s 4) ← copy var_a) ;;
        ret [(s 4)]
    }
  ]
}

#guard alphaEquivFunDef (parsedAt 7) hw_ge_branch
