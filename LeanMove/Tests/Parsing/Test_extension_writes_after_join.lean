/-
 Copyright Ilya Sergey
 Licensed under the Apache License, Version 2.0
-/

import LeanMove.Tests.Parsing.TestUtils
import LeanMove.Tests.Typechecking.expressivity.accepted.extension_writes_after_join

/-! ## Parse Test: extension_writes_after_join.mvir

Tests parsing of extension_writes_after_join — writing to extension after join
with struct S and conditional branching.

Alpha-equivalence tests compare the parser output against hand-written
FunDefs to validate correct translation.
-/

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Lang.MoveIR.Parser
open LeanMove.Lang.MoveIR.Translate
open LeanMove.Tests.Parsing.TestUtils
open LeanMove.Tests.Expressivity.ExtensionWritesAfterJoin

def extensionWritesAfterJoinMvir :=
  include_str "../Typechecking/expressivity/accepted/extension_writes_after_join.mvir"

-- Parse succeeds
#guard (parseMvir extensionWritesAfterJoinMvir).isOk

-- Translation succeeds
#guard (parseAndTranslate extensionWritesAfterJoinMvir).isOk

-- ----------------------------------------------------------------
-- Hand-written FunDef for alpha-equivalence testing
-- ----------------------------------------------------------------

-- Sites (distinct per block)
-- l0: branch
private def s0 : Site := .site 0    -- move(cond)
-- l1 (false branch): x = move(a); y = move(b)
private def s1 : Site := .site 1    -- move(a)
private def s2 : Site := .site 2    -- move(b)
-- l2 (true branch): x = move(b); y = move(a)
private def s3 : Site := .site 3    -- move(b)
private def s4 : Site := .site 4    -- move(a)
-- l3: f = &mut copy(x).S::f; *copy(y) = S { f: *copy(f) }; *copy(f) = 0; return move(y)
private def s5 : Site := .site 5    -- copy(x)
private def s6 : Site := .site 6    -- borrowMutField(s5, S, f)
private def s7 : Site := .site 7    -- copy(f)
private def s8 : Site := .site 8    -- *s7 (readRef)
private def s9 : Site := .site 9    -- pack("S", [(f, s8)])
private def s10 : Site := .site 10  -- copy(y)
private def s11 : Site := .site 11  -- copy(f)
private def s12 : Site := .site 12  -- #0
private def s13 : Site := .site 13  -- move(y)

private def hw_t : FunDef := {
  params := [
    (var_cond, .basic .tbool),
    (var_a, .ref (.trecord s_entries) (.paramRef var_a) .siteBorrowMut),
    (var_b, .ref (.trecord s_entries) (.paramRef var_b) .siteBorrowMut)
  ]
  returnType := [⟨.trecord s_entries, some true⟩]
  locals := [
    { name := var_x, type := .ref (.trecord s_entries) (.refid 1) .siteBorrowMut },
    { name := var_y, type := .ref (.trecord s_entries) (.refid 2) .siteBorrowMut },
    { name := var_f, type := .ref .u64 (.refid 3) .siteBorrowMut }
  ]
  blocks := [
    -- l0: jump_if (move(cond)) l2;
    { label := "l0"
      body :=
        (letsite s0 ← move var_cond) ;;
        branch s0 "l2" "l1"
    },
    -- l1 (false branch): x = move(a); y = move(b); jump l3
    { label := "l1"
      body :=
        (letsite s1 ← move var_a) ;;
        (var_x ::= s1) ;;
        (letsite s2 ← move var_b) ;;
        (var_y ::= s2) ;;
        jump "l3"
    },
    -- l2 (true branch): x = move(b); y = move(a); jump l3
    { label := "l2"
      body :=
        (letsite s3 ← move var_b) ;;
        (var_x ::= s3) ;;
        (letsite s4 ← move var_a) ;;
        (var_y ::= s4) ;;
        jump "l3"
    },
    -- l3: f = &mut copy(x).S::f; *copy(y) = S { f: *copy(f) }; *copy(f) = 0; return move(y)
    { label := "l3"
      body :=
        -- f = &mut copy(x).S::f
        (letsite s5 ← copy var_x) ;;
        (letsite s6 ← borrowMutField(s5, .trecord s_entries, field_f)) ;;
        (var_f ::= s6) ;;
        -- *copy(y) = S { f: *copy(f) }
        (letsite s7 ← copy var_f) ;;
        (letsite s8 ← *s7) ;;
        (letsite s9 ← pack("S", [(field_f, s8)])) ;;
        (letsite s10 ← copy var_y) ;;
        (*s10 ::= s9) ;;
        -- *copy(f) = 0
        (letsite s11 ← copy var_f) ;;
        (letsite s12 ← #0) ;;
        (*s11 ::= s12) ;;
        -- return move(y)
        (letsite s13 ← move var_y) ;;
        ret [s13]
    }
  ]
}

-- ----------------------------------------------------------------
-- Alpha-equivalence with hand-written example
-- ----------------------------------------------------------------

#guard
  match parseAndTranslate extensionWritesAfterJoinMvir with
  | .ok results =>
    match findFun results "t" with
    | some fd => alphaEquivFunDef fd hw_t
    | none => false
  | .error _ => false
