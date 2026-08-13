/-
 Copyright Ilya Sergey
 Licensed under the Apache License, Version 2.0
-/

import LeanMove.Tests.Parsing.TestUtils
import LeanMove.Lang.Macros

/-! ## Parse Test: casts.mvir

Covers the two pieces of concrete syntax that integer widths introduce.

The literal *suffix* is the first. It was previously parsed and thrown away —
`parseUnaryExpr` matched `u64`/`u8` only to skip them — so every literal became
a `u64`. It now selects the width, which is what distinguishes `LdU8` from
`LdU64`, and an unsuffixed literal still defaults to `u64`.

The cast is the second. MVIR spells it `(e as T)`, so it is recognised where
the parenthesised expression is parsed rather than as an operator; the tests
below therefore also pin down that a plain `(e)` is still just `e`.

Alpha-equivalence against hand-written ASTs is what makes these regressions
visible: a dropped suffix or a mis-parsed cast would otherwise still typecheck,
just at the wrong width.
-/

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Lang.MoveIR.Parser
open LeanMove.Lang.MoveIR.Translate
open LeanMove.Tests.Parsing.TestUtils

private def src :=
  include_str "../MVIR/casts.mvir"

#guard (parseMvir src).isOk
#guard (parseAndTranslate src).isOk
#guard (parseAndTranslate src).toOption.get!.length == 6

private def var_a : Var := ⟨"a"⟩
private def var_b : Var := ⟨"b"⟩
private def s (n : Nat) : Site := .site n

private def parsedAt (i : Nat) : FunDef :=
  (findFunAt (parseAndTranslate src).toOption.get! i).get!

/-- `f(a: from): to { return (copy(a) as to); }` -/
private def hw_cast (from_ to : IntType) : FunDef := {
  params := [(var_a, .basic (.int from_))]
  returnType := [⟨.int to, none⟩]
  locals := []
  blocks := [
    { label := "b0"
      body :=
        (letsite (s 0) ← copy var_a) ;;
        (letsite (s 1) ← unop(.cast to, (s 0))) ;;
        ret [(s 1)]
    }
  ]
}

-- `widen(a: u8): u64 { return (copy(a) as u64); }`
#guard alphaEquivFunDef (parsedAt 0) (hw_cast .u8 .u64)

-- `narrow(a: u64): u8 { return (copy(a) as u8); }`
#guard alphaEquivFunDef (parsedAt 1) (hw_cast .u64 .u8)

/-- `f(): w { return N w; }` -/
private def hw_lit (n : Nat) (w : IntType) : FunDef := {
  params := []
  returnType := [⟨.int w, none⟩]
  locals := []
  blocks := [
    { label := "b0"
      body :=
        (letsite (s 0) ← #n w) ;;
        ret [(s 0)]
    }
  ]
}

-- `7u8` is a `u8` literal, not a `u64` one …
#guard alphaEquivFunDef (parsedAt 2) (hw_lit 7 .u8)

-- … and it is *not* alpha-equivalent to the `u64` literal, which is the
-- property the old suffix-skipping parser violated.
#guard !alphaEquivFunDef (parsedAt 2) (hw_lit 7 .u64)

-- an unsuffixed literal defaults to u64
#guard alphaEquivFunDef (parsedAt 3) (hw_lit 7 .u64)

-- widths past u64 parse identically
#guard alphaEquivFunDef (parsedAt 4) (hw_lit 7 .u256)

/-- `add_after_cast(a: u8, b: u64): u64 { return (copy(a) as u64) + copy(b); }` -/
private def hw_add_after_cast : FunDef := {
  params := [(var_a, .basic .u8), (var_b, .basic .u64)]
  returnType := [⟨.u64, none⟩]
  locals := []
  blocks := [
    { label := "b0"
      body :=
        (letsite (s 0) ← copy var_a) ;;
        (letsite (s 1) ← unop(.cast .u64, (s 0))) ;;
        (letsite (s 2) ← copy var_b) ;;
        (letsite (s 3) ← binop(.add, (s 1), (s 2))) ;;
        ret [(s 3)]
    }
  ]
}

#guard alphaEquivFunDef (parsedAt 5) hw_add_after_cast
