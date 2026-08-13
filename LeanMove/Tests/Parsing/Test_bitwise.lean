/-
 Copyright Ilya Sergey
 Licensed under the Apache License, Version 2.0
-/

import LeanMove.Tests.Parsing.TestUtils
import LeanMove.Lang.Macros

/-! ## Parse Test: bitwise.mvir

Regression test for `BitAnd`, `BitOr` and `Xor`, and specifically for the three
readings of the `&` character in MVIR: prefix borrow, infix `BitAnd`, and the
first half of `&&`.

`parseBinOp` folds `binaryOperators` into a chain of alternatives and `keyword`
does no word-boundary check, so `&&` and `||` only keep working because they
precede `&` and `|` in that list. The `conj`/`disj` cases below are what would
catch a reordering: with `&` first, `a && b` would parse as `a & (&b)` or fail
outright, and either way the alpha-equivalence check against `Binop.and` fails.
-/

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Lang.MoveIR.Parser
open LeanMove.Lang.MoveIR.Translate
open LeanMove.Tests.Parsing.TestUtils

private def src :=
  include_str "../MVIR/bitwise.mvir"

#guard (parseMvir src).isOk
#guard (parseAndTranslate src).isOk
#guard (parseAndTranslate src).toOption.get!.length == 7

private def var_a : Var := ⟨"a"⟩
private def var_b : Var := ⟨"b"⟩
private def s (n : Nat) : Site := .site n

private def parsedAt (i : Nat) : FunDef :=
  (findFunAt (parseAndTranslate src).toOption.get! i).get!

/-- `f(a: t, b: t): r { return copy(a) op copy(b); }` -/
private def hw_bin (op : Binop) (t : BasicMoveType) (r : BasicMoveType) : FunDef := {
  params := [(var_a, .basic t), (var_b, .basic t)]
  returnType := [⟨r, none⟩]
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

-- Each spelling maps to its own opcode.
#guard alphaEquivFunDef (parsedAt 0) (hw_bin .bitand .u64 .u64)
#guard alphaEquivFunDef (parsedAt 1) (hw_bin .bitor .u64 .u64)
#guard alphaEquivFunDef (parsedAt 2) (hw_bin .bitxor .u64 .u64)
#guard alphaEquivFunDef (parsedAt 3) (hw_bin .bitand .u8 .u8)

/-- `band_derefs(a: &u64, b: &u64): u64 { return *copy(a) & *copy(b); }` -/
private def hw_band_derefs : FunDef := {
  params := [(var_a, .ref .u64 (.paramRef var_a) .siteBorrowImm),
             (var_b, .ref .u64 (.paramRef var_b) .siteBorrowImm)]
  returnType := [⟨.u64, none⟩]
  locals := []
  blocks := [
    { label := "b0"
      body :=
        (letsite (s 0) ← copy var_a) ;;
        (letsite (s 1) ← * (s 0)) ;;
        (letsite (s 2) ← copy var_b) ;;
        (letsite (s 3) ← * (s 2)) ;;
        (letsite (s 4) ← binop(.bitand, (s 1), (s 3))) ;;
        ret [(s 4)]
    }
  ]
}

#guard alphaEquivFunDef (parsedAt 4) hw_band_derefs

-- `&&` and `||` still win the longest match against `&` and `|`.
#guard alphaEquivFunDef (parsedAt 5) (hw_bin .and .tbool .tbool)
#guard alphaEquivFunDef (parsedAt 6) (hw_bin .or .tbool .tbool)

-- …and are genuinely distinct from the bitwise opcodes.
#guard !alphaEquivFunDef (parsedAt 5) (hw_bin .bitand .tbool .tbool)
#guard !alphaEquivFunDef (parsedAt 6) (hw_bin .bitor .tbool .tbool)
