/-
 Copyright Ilya Sergey
 Licensed under the Apache License, Version 2.0
-/

import LeanMove.Tests.Parsing.TestUtils
import LeanMove.Tests.Typechecking.expressivity.accepted.alias_write_after_join

/-! ## Parse Test: alias_write_after_join.mvir

Tests parsing of alias_write_after_join — writing to alias after join with branching.

Alpha-equivalence tests compare the parser output against hand-written
FunDefs to validate correct translation.
-/

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Lang.MoveIR.Parser
open LeanMove.Lang.MoveIR.Translate
open LeanMove.Tests.Parsing.TestUtils
open LeanMove.Tests.Expressivity.AliasWriteAfterJoin

def aliasWriteAfterJoinMvir :=
  include_str "../Typechecking/expressivity/accepted/alias_write_after_join.mvir"

-- Parse succeeds
#guard (parseMvir aliasWriteAfterJoinMvir).isOk

-- Translation succeeds
#guard (parseAndTranslate aliasWriteAfterJoinMvir).isOk

-- ----------------------------------------------------------------
-- Hand-written FunDef for alpha-equivalence testing
-- ----------------------------------------------------------------

-- Sites (distinct per block for alpha-equiv bijection)
-- l0: initialization and branch
private def s0 : Site := .site 0    -- integer literal 0 for a
private def s1 : Site := .site 1    -- integer literal 0 for b
private def s2 : Site := .site 2    -- move(cond)
-- l1 (false branch)
private def s3 : Site := .site 3    -- &mut a (for x)
private def s4 : Site := .site 4    -- &mut b (for y)
-- l2 (true branch)
private def s5 : Site := .site 5    -- &mut b (for x)
private def s6 : Site := .site 6    -- &mut a (for y)
-- l3: writes and return
private def s7 : Site := .site 7    -- &mut a (for z)
private def s8 : Site := .site 8    -- move(z)
private def s9 : Site := .site 9    -- integer literal 0 (first write)
private def s10 : Site := .site 10  -- move(x)
private def s11 : Site := .site 11  -- integer literal 0 (second write)
private def s12 : Site := .site 12  -- move(y)
private def s13 : Site := .site 13  -- integer literal 0 (third write)

private def hw_t : FunDef := {
  params := [(var_cond, .basic .tbool)]
  returnType := []
  locals := [
    { name := var_a, type := .basic .u64 },
    { name := var_b, type := .basic .u64 },
    { name := var_x, type := .ref .u64 (.refid 1) .siteBorrowMut },
    { name := var_y, type := .ref .u64 (.refid 2) .siteBorrowMut },
    { name := var_z, type := .ref .u64 (.refid 3) .siteBorrowMut }
  ]
  blocks := [
    -- l0: a = 0; b = 0; jump_if (move(cond)) l2;
    { label := "l0"
      body :=
        (letsite s0 ← #0) ;;
        (var_a ::= s0) ;;
        (letsite s1 ← #0) ;;
        (var_b ::= s1) ;;
        (letsite s2 ← move var_cond) ;;
        branch s2 "l2" "l1"
    },
    -- l1 (false branch): x = &mut a; y = &mut b; jump l3
    { label := "l1"
      body :=
        (letsite s3 ← &mut var_a) ;;
        (var_x ::= s3) ;;
        (letsite s4 ← &mut var_b) ;;
        (var_y ::= s4) ;;
        jump "l3"
    },
    -- l2 (true branch): x = &mut b; y = &mut a; jump l3
    { label := "l2"
      body :=
        (letsite s5 ← &mut var_b) ;;
        (var_x ::= s5) ;;
        (letsite s6 ← &mut var_a) ;;
        (var_y ::= s6) ;;
        jump "l3"
    },
    -- l3: z = &mut a; *move(z) = 0; *move(x) = 0; *move(y) = 0; return
    { label := "l3"
      body :=
        (letsite s7 ← &mut var_a) ;;
        (var_z ::= s7) ;;
        (letsite s8 ← move var_z) ;;
        (letsite s9 ← #0) ;;
        (*s8 ::= s9) ;;
        (letsite s10 ← move var_x) ;;
        (letsite s11 ← #0) ;;
        (*s10 ::= s11) ;;
        (letsite s12 ← move var_y) ;;
        (letsite s13 ← #0) ;;
        (*s12 ::= s13) ;;
        ret []
    }
  ]
}

-- ----------------------------------------------------------------
-- Alpha-equivalence with hand-written example
-- ----------------------------------------------------------------

#guard
  match parseAndTranslate aliasWriteAfterJoinMvir with
  | .ok results =>
    match findFun results "t" with
    | some fd => alphaEquivFunDef fd hw_t
    | none => false
  | .error _ => false
