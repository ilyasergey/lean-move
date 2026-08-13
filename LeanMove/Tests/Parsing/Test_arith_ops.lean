/-
 Copyright Ilya Sergey
 Licensed under the Apache License, Version 2.0
-/

import LeanMove.Tests.Parsing.TestUtils
import LeanMove.Lang.Macros

/-! ## Parse Test: arith_ops.mvir

Regression test for infix `*` (`Mul`).

`*` is the only operator spelling MVIR overloads: prefix it is dereference,
infix it is multiplication. The grammar resolves this positionally rather than
by lookahead — `parseUnaryExpr` consumes a prefix `*` before `parseExpr`
consults `binaryOperators`, so a `*` reaching `parseBinOp` always follows a
complete operand. These guards pin down the three places that could go wrong:

* `mul_derefs` — `*copy(a) * *copy(b)`, prefix and infix `*` adjacent;
* `scale` — infix `*` inside the value of a `*`-prefixed write target;
* `mul_pair` — a `*`-separated *return type* list, which is parsed by
  `starSep1 parseType` and must not be swallowed as multiplication.
-/

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Lang.MoveIR.Parser
open LeanMove.Lang.MoveIR.Translate
open LeanMove.Tests.Parsing.TestUtils

private def src :=
  include_str "../MVIR/arith_ops.mvir"

#guard (parseMvir src).isOk
#guard (parseAndTranslate src).isOk
#guard (parseAndTranslate src).toOption.get!.length == 5

private def var_a : Var := ⟨"a"⟩
private def var_b : Var := ⟨"b"⟩
private def var_c : Var := ⟨"c"⟩
private def var_k : Var := ⟨"k"⟩
private def var_r : Var := ⟨"r"⟩
private def s (n : Nat) : Site := .site n

private def parsedAt (i : Nat) : FunDef :=
  (findFunAt (parseAndTranslate src).toOption.get! i).get!

-- ----------------------------------------------------------------
-- mul: the plain infix case, `return copy(a) * copy(b);`
-- ----------------------------------------------------------------

/-- `arith(a, b)` for a `u64` arithmetic `op`: `return copy(a) op copy(b);` -/
private def hw_arith (op : Binop) : FunDef := {
  params := [(var_a, .basic .u64), (var_b, .basic .u64)]
  returnType := [⟨.u64, none⟩]
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

#guard alphaEquivFunDef (parsedAt 0) (hw_arith .mul)

-- `*` is its own opcode, not the `.add` the translator falls back to.
#guard !alphaEquivFunDef (parsedAt 0) (hw_arith .add)

-- ----------------------------------------------------------------
-- mul_derefs: `*copy(a) * *copy(b)` — prefix `*` on both operands
--
-- The shape the disambiguation exists for. Each prefix `*` becomes a
-- `readRef`, and the middle `*` becomes the `Mul`.
-- ----------------------------------------------------------------

private def hw_mul_derefs : FunDef := {
  params := [(var_a, .ref .u64 (.paramRef var_a) .siteBorrowImm),
             (var_b, .ref .u64 (.paramRef var_b) .siteBorrowImm)]
  returnType := [⟨.u64, none⟩]
  locals := []
  blocks := [
    { label := "b0"
      body :=
        (letsite (s 0) ← copy var_a) ;;
        (letsite (s 1) ← *(s 0)) ;;
        (letsite (s 2) ← copy var_b) ;;
        (letsite (s 3) ← *(s 2)) ;;
        (letsite (s 4) ← binop(.mul, (s 1), (s 3))) ;;
        ret [(s 4)]
    }
  ]
}

#guard alphaEquivFunDef (parsedAt 1) hw_mul_derefs

-- ----------------------------------------------------------------
-- scale: infix `*` in the value of a `*`-prefixed write target
-- ----------------------------------------------------------------

private def hw_scale : FunDef := {
  params := [(var_r, .ref .u64 (.paramRef var_r) .siteBorrowMut),
             (var_k, .basic .u64)]
  returnType := []
  locals := []
  blocks := [
    { label := "b0"
      body :=
        (letsite (s 0) ← copy var_r) ;;
        (letsite (s 1) ← copy var_k) ;;
        (letsite (s 2) ← copy var_k) ;;
        (letsite (s 3) ← binop(.mul, (s 1), (s 2))) ;;
        (*(s 0) ::= (s 3)) ;;
        ret []
    }
  ]
}

#guard alphaEquivFunDef (parsedAt 2) hw_scale

-- ----------------------------------------------------------------
-- mul_add: `(copy(a) * copy(b)) + copy(c)`
-- ----------------------------------------------------------------

private def hw_mul_add : FunDef := {
  params := [(var_a, .basic .u64), (var_b, .basic .u64), (var_c, .basic .u64)]
  returnType := [⟨.u64, none⟩]
  locals := []
  blocks := [
    { label := "b0"
      body :=
        (letsite (s 0) ← copy var_a) ;;
        (letsite (s 1) ← copy var_b) ;;
        (letsite (s 2) ← binop(.mul, (s 0), (s 1))) ;;
        (letsite (s 3) ← copy var_c) ;;
        (letsite (s 4) ← binop(.add, (s 2), (s 3))) ;;
        ret [(s 4)]
    }
  ]
}

#guard alphaEquivFunDef (parsedAt 3) hw_mul_add

-- ----------------------------------------------------------------
-- mul_pair: `mul_pair(a, b): u64 * u64`
--
-- The `*` in the *signature* separates two return types. If it were read as
-- multiplication the function would have a single return value, so the arity
-- below is the real assertion.
-- ----------------------------------------------------------------

private def hw_mul_pair : FunDef := {
  params := [(var_a, .basic .u64), (var_b, .basic .u64)]
  returnType := [⟨.u64, none⟩, ⟨.u64, none⟩]
  locals := []
  blocks := [
    { label := "b0"
      body :=
        (letsite (s 0) ← copy var_a) ;;
        (letsite (s 1) ← copy var_b) ;;
        (letsite (s 2) ← binop(.mul, (s 0), (s 1))) ;;
        (letsite (s 3) ← copy var_a) ;;
        (letsite (s 4) ← copy var_b) ;;
        (letsite (s 5) ← binop(.add, (s 3), (s 4))) ;;
        ret [(s 2), (s 5)]
    }
  ]
}

#guard alphaEquivFunDef (parsedAt 4) hw_mul_pair
#guard (parsedAt 4).returnType.length == 2
