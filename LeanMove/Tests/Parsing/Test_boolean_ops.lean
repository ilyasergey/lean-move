/-
 Copyright Ilya Sergey
 Licensed under the Apache License, Version 2.0
-/

import LeanMove.Tests.Parsing.TestUtils
import LeanMove.Lang.Macros

/-! ## Parse Test: boolean_ops.mvir

End-to-end coverage for the prefix `!`, the only unary operator the MVIR
concrete syntax admits.

Until this test no `.mvir` file in the repository contained a `!`, so neither
the `'!'` branch of `parseUnaryExpr` nor `translateUnop` was ever executed:
`Unop.not` was reachable only from hand-written ASTs. The branch also has to
tell `!` apart from the binary `!=`, which shares its first character — so
`neq` is parsed from the same file, pinning the split from both sides.
-/

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Lang.MoveIR.Parser
open LeanMove.Lang.MoveIR.Translate
open LeanMove.Tests.Parsing.TestUtils

private def src :=
  include_str "../MVIR/boolean_ops.mvir"

#guard (parseMvir src).isOk
#guard (parseAndTranslate src).isOk
#guard (parseAndTranslate src).toOption.get!.length == 7

private def var_a : Var := ⟨"a"⟩
private def var_b : Var := ⟨"b"⟩
private def var_p : Var := ⟨"p"⟩
private def s (n : Nat) : Site := .site n

private def parsedAt (i : Nat) : FunDef :=
  (findFunAt (parseAndTranslate src).toOption.get! i).get!

-- ----------------------------------------------------------------
-- `!(a == b)` — the bare prefix operator
-- ----------------------------------------------------------------

private def hw_not : FunDef := {
  params := [(var_a, .basic .u64), (var_b, .basic .u64)]
  returnType := [⟨.tbool, none⟩]
  locals := []
  blocks := [
    { label := "b0"
      body :=
        (letsite (s 0) ← copy var_a) ;;
        (letsite (s 1) ← copy var_b) ;;
        (letsite (s 2) ← binop(.eq, (s 0), (s 1))) ;;
        (letsite (s 3) ← unop(.not, (s 2))) ;;
        ret [(s 3)]
    }
  ]
}

#guard alphaEquivFunDef (parsedAt 0) hw_not

-- The `!` is not silently dropped: without it the function is a plain `eq`.
private def hw_eq : FunDef := {
  params := [(var_a, .basic .u64), (var_b, .basic .u64)]
  returnType := [⟨.tbool, none⟩]
  locals := []
  blocks := [
    { label := "b0"
      body :=
        (letsite (s 0) ← copy var_a) ;;
        (letsite (s 1) ← copy var_b) ;;
        (letsite (s 2) ← binop(.eq, (s 0), (s 1))) ;;
        ret [(s 2)]
    }
  ]
}

#guard !alphaEquivFunDef (parsedAt 0) hw_eq

-- ----------------------------------------------------------------
-- `!!(a == b)` — `!` composed with itself
-- ----------------------------------------------------------------

private def hw_double_negation : FunDef := {
  params := [(var_a, .basic .u64), (var_b, .basic .u64)]
  returnType := [⟨.tbool, none⟩]
  locals := []
  blocks := [
    { label := "b0"
      body :=
        (letsite (s 0) ← copy var_a) ;;
        (letsite (s 1) ← copy var_b) ;;
        (letsite (s 2) ← binop(.eq, (s 0), (s 1))) ;;
        (letsite (s 3) ← unop(.not, (s 2))) ;;
        (letsite (s 4) ← unop(.not, (s 3))) ;;
        ret [(s 4)]
    }
  ]
}

#guard alphaEquivFunDef (parsedAt 1) hw_double_negation

-- A doubled `!` really does yield two `Unop.not` nodes, not one.
#guard !alphaEquivFunDef (parsedAt 1) hw_not

-- ----------------------------------------------------------------
-- `!copy(p)` — `!` applied to a variable, not to a parenthesised expression
-- ----------------------------------------------------------------

private def hw_not_var : FunDef := {
  params := [(var_p, .basic .tbool)]
  returnType := [⟨.tbool, none⟩]
  locals := []
  blocks := [
    { label := "b0"
      body :=
        (letsite (s 0) ← copy var_p) ;;
        (letsite (s 1) ← unop(.not, (s 0))) ;;
        ret [(s 1)]
    }
  ]
}

#guard alphaEquivFunDef (parsedAt 2) hw_not_var

-- ----------------------------------------------------------------
-- `!` under `&&` and under `||`
-- ----------------------------------------------------------------

private def hw_and_not : FunDef := {
  params := [(var_a, .basic .u64), (var_b, .basic .u64)]
  returnType := [⟨.tbool, none⟩]
  locals := []
  blocks := [
    { label := "b0"
      body :=
        (letsite (s 0) ← copy var_a) ;;
        (letsite (s 1) ← copy var_b) ;;
        (letsite (s 2) ← binop(.eq, (s 0), (s 1))) ;;
        (letsite (s 3) ← copy var_a) ;;
        (letsite (s 4) ← copy var_b) ;;
        (letsite (s 5) ← binop(.lt, (s 3), (s 4))) ;;
        (letsite (s 6) ← unop(.not, (s 5))) ;;
        (letsite (s 7) ← binop(.and, (s 2), (s 6))) ;;
        ret [(s 7)]
    }
  ]
}

#guard alphaEquivFunDef (parsedAt 3) hw_and_not

private def hw_or_not : FunDef := {
  params := [(var_a, .basic .u64), (var_b, .basic .u64)]
  returnType := [⟨.tbool, none⟩]
  locals := []
  blocks := [
    { label := "b0"
      body :=
        (letsite (s 0) ← copy var_a) ;;
        (letsite (s 1) ← copy var_b) ;;
        (letsite (s 2) ← binop(.eq, (s 0), (s 1))) ;;
        (letsite (s 3) ← unop(.not, (s 2))) ;;
        (letsite (s 4) ← copy var_a) ;;
        (letsite (s 5) ← copy var_b) ;;
        (letsite (s 6) ← binop(.lt, (s 4), (s 5))) ;;
        (letsite (s 7) ← binop(.or, (s 3), (s 6))) ;;
        ret [(s 7)]
    }
  ]
}

#guard alphaEquivFunDef (parsedAt 4) hw_or_not

-- `&&` and `||` are distinguished from one another.
#guard !alphaEquivFunDef (parsedAt 3) hw_or_not
#guard !alphaEquivFunDef (parsedAt 4) hw_and_not

-- ----------------------------------------------------------------
-- `!` in branch position
-- ----------------------------------------------------------------

private def hw_not_branch : FunDef := {
  params := [(var_a, .basic .u64), (var_b, .basic .u64)]
  returnType := [⟨.u64, none⟩]
  locals := []
  blocks := [
    { label := "b0"
      body :=
        (letsite (s 0) ← copy var_a) ;;
        (letsite (s 1) ← copy var_b) ;;
        (letsite (s 2) ← binop(.eq, (s 0), (s 1))) ;;
        (letsite (s 3) ← unop(.not, (s 2))) ;;
        branch (s 3) "b2" "b1"
    },
    { label := "b1"
      body :=
        (letsite (s 4) ← copy var_a) ;;
        ret [(s 4)]
    },
    { label := "b2"
      body :=
        (letsite (s 5) ← copy var_b) ;;
        ret [(s 5)]
    }
  ]
}

#guard alphaEquivFunDef (parsedAt 5) hw_not_branch

-- ----------------------------------------------------------------
-- `!=` still parses as the binary operator, in the same file
-- ----------------------------------------------------------------

private def hw_neq : FunDef := {
  params := [(var_a, .basic .u64), (var_b, .basic .u64)]
  returnType := [⟨.tbool, none⟩]
  locals := []
  blocks := [
    { label := "b0"
      body :=
        (letsite (s 0) ← copy var_a) ;;
        (letsite (s 1) ← copy var_b) ;;
        (letsite (s 2) ← binop(.neq, (s 0), (s 1))) ;;
        ret [(s 2)]
    }
  ]
}

#guard alphaEquivFunDef (parsedAt 6) hw_neq

-- ----------------------------------------------------------------
-- The `!` / `!=` split
-- ----------------------------------------------------------------

/-- A single function body, wrapped in enough module scaffolding to parse. -/
private def wrap (body : String) : String :=
  "//# publish\nmodule 0x51.T {\n  f(a: u64, b: u64): bool {\n  label b0:\n    " ++
  body ++ "\n  }\n}\n"

/-- Modules successfully parsed from `s`. `parseMvir` is lenient: a module it
    cannot parse is dropped rather than reported, so the result is still `.ok`
    and only the module count distinguishes accepted from rejected input. -/
private def moduleCount (s : String) : Nat :=
  match parseMvir s with
  | .ok p => p.modules.length
  | .error _ => 0

-- `!` binds to what follows it, with or without intervening whitespace, and
-- whether the operand is parenthesised or not.
#guard moduleCount (wrap "return !copy(b);") == 1
#guard moduleCount (wrap "return ! copy(b);") == 1
#guard moduleCount (wrap "return !(copy(a) == copy(b));") == 1

-- `!=` is the binary operator and needs a left operand.
#guard moduleCount (wrap "return copy(a) != copy(b);") == 1
#guard moduleCount (wrap "return != copy(b);") == 0
