/-
 Copyright Ilya Sergey
 Licensed under the Apache License, Version 2.0
-/

import LeanMove.Tests.Parsing.TestUtils
import LeanMove.Tests.Typechecking.expressivity.rejected.simple_dangling

/-! ## Parse Test: simple_dangling.mvir (REJECTED)

Tests parsing of simple_dangling — the verifier stops creation of dangling references.
Five modules: field, nested_field, vector, simple_call, field_call.
Note: the vector module uses vec_mut_borrow/vec_pack_0 which are not fully supported
in translation, but parsing should succeed.

Alpha-equivalence tests compare the parser output against hand-written
FunDefs to validate correct translation.
-/

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Lang.MoveIR.Parser
open LeanMove.Lang.MoveIR.Translate
open LeanMove.Tests.Parsing.TestUtils
open LeanMove.Tests.Expressivity.SimpleDangling

def simpleDanglingMvir :=
  include_str "../Typechecking/expressivity/rejected/simple_dangling.mvir"

-- Parse succeeds
#guard (parseMvir simpleDanglingMvir).isOk

-- 5 modules
#guard (parseMvir simpleDanglingMvir).toOption.get!.modules.length == 5

-- Translation succeeds
#guard (parseAndTranslate simpleDanglingMvir).isOk

-- ----------------------------------------------------------------
-- Hand-written FunDefs for alpha-equivalence testing
-- ----------------------------------------------------------------

-- Sites for field module (t(s: &mut S))
-- f = &copy(s).S::f; *move(s) = S { f: 0 }; return;
private def fs0 : Site := .site 0    -- copy(s)
private def fs1 : Site := .site 1    -- borrowField(fs0, S, f)
private def fs2 : Site := .site 2    -- move(s)
private def fs3 : Site := .site 3    -- integer literal 0
private def fs4 : Site := .site 4    -- pack("S", [(f, fs3)])

private def hw_field_t : FunDef := {
  params := [(var_s, .ref (.trecord s_entries) (.paramRef var_s) .siteBorrowMut)]
  returnType := []
  locals := [
    { name := var_f, type := .ref .u64 (.refid 0) .siteBorrowImm }
  ]
  blocks := [
    { label := "b0"
      body :=
        -- f = &copy(s).S::f
        (letsite fs0 ← copy var_s) ;;
        (letsite fs1 ← borrowField(fs0, .trecord s_entries, field_f)) ;;
        (var_f ::= fs1) ;;
        -- *move(s) = S { f: 0 }
        (letsite fs2 ← move var_s) ;;
        (letsite fs3 ← #0) ;;
        (letsite fs4 ← pack("S", [(field_f, fs3)])) ;;
        (*fs2 ::= fs4) ;;
        ret []
    }
  ]
}

-- Sites for nested_field module (t(p: &mut P))
-- s = &mut copy(p).P::s; f = &copy(s).S::f; *move(p) = P { s: S { f: 0 } }; return;
private def ns0 : Site := .site 10   -- copy(p)
private def ns1 : Site := .site 11   -- borrowMutField(ns0, P, s)
private def ns2 : Site := .site 12   -- copy(s)
private def ns3 : Site := .site 13   -- borrowField(ns2, S, f)
private def ns4 : Site := .site 14   -- move(p)
private def ns5 : Site := .site 15   -- integer literal 0
private def ns6 : Site := .site 16   -- pack("S", [(f, ns5)])
private def ns7 : Site := .site 17   -- pack("P", [(s, ns6)])

private def hw_nested_field_t : FunDef := {
  params := [(var_p, .ref (.trecord p_entries) (.paramRef var_p) .siteBorrowMut)]
  returnType := []
  locals := [
    { name := var_s, type := .ref (.trecord s_entries) (.refid 1) .siteBorrowMut },
    { name := var_f, type := .ref .u64 (.refid 2) .siteBorrowImm }
  ]
  blocks := [
    { label := "b0"
      body :=
        -- s = &mut copy(p).P::s
        (letsite ns0 ← copy var_p) ;;
        (letsite ns1 ← borrowMutField(ns0, .trecord p_entries, field_s)) ;;
        (var_s ::= ns1) ;;
        -- f = &copy(s).S::f
        (letsite ns2 ← copy var_s) ;;
        (letsite ns3 ← borrowField(ns2, .trecord s_entries, field_f)) ;;
        (var_f ::= ns3) ;;
        -- *move(p) = P { s: S { f: 0 } }
        (letsite ns4 ← move var_p) ;;
        (letsite ns5 ← #0) ;;
        (letsite ns6 ← pack("S", [(field_f, ns5)])) ;;
        (letsite ns7 ← pack("P", [(field_s, ns6)])) ;;
        (*ns4 ::= ns7) ;;
        ret []
    }
  ]
}

-- Sites for simple_call module (t())
-- a = 0; m = &mut a; i = Self.f(copy(m)); *copy(m) = 0; return;
private def scs0 : Site := .site 20  -- integer literal 0
private def scs1 : Site := .site 21  -- &mut a
private def scs2 : Site := .site 22  -- copy(m)
private def scs3 : Site := .site 23  -- call output: f(copy(m))
private def scs4 : Site := .site 24  -- copy(m)
private def scs5 : Site := .site 25  -- integer literal 0 for write

private def hw_simple_call_t : FunDef := {
  params := []
  returnType := []
  locals := [
    { name := var_a, type := .basic .u64 },
    { name := var_m, type := .ref .u64 (.refid 5) .siteBorrowMut },
    { name := var_i, type := .ref .u64 (.refid 6) .siteBorrowImm }
  ]
  blocks := [
    { label := "b0"
      body :=
        -- a = 0
        (letsite scs0 ← #0) ;;
        (var_a ::= scs0) ;;
        -- m = &mut a
        (letsite scs1 ← &mut var_a) ;;
        (var_m ::= scs1) ;;
        -- i = Self.f(copy(m))
        (letsite scs2 ← copy var_m) ;;
        (call([scs3], "f", [scs2])) ;;
        (var_i ::= scs3) ;;
        -- *copy(m) = 0
        (letsite scs4 ← copy var_m) ;;
        (letsite scs5 ← #0) ;;
        (*scs4 ::= scs5) ;;
        ret []
    }
  ]
}

-- Sites for field_call module (t(s: &mut S))
-- f = Self.f(copy(s)); *copy(s) = S { f: 0 }; return;
private def fcs0 : Site := .site 30  -- copy(s)
private def fcs1 : Site := .site 31  -- call output: f(copy(s))
private def fcs2 : Site := .site 32  -- copy(s)
private def fcs3 : Site := .site 33  -- integer literal 0
private def fcs4 : Site := .site 34  -- pack("S", [(f, fcs3)])

private def hw_field_call_t : FunDef := {
  params := [(var_s, .ref (.trecord s_entries) (.paramRef var_s) .siteBorrowMut)]
  returnType := []
  locals := [
    { name := var_f, type := .ref .u64 (.refid 0) .siteBorrowImm }
  ]
  blocks := [
    { label := "b0"
      body :=
        -- f = Self.f(copy(s))
        (letsite fcs0 ← copy var_s) ;;
        (call([fcs1], "f", [fcs0])) ;;
        (var_f ::= fcs1) ;;
        -- *copy(s) = S { f: 0 }
        (letsite fcs2 ← copy var_s) ;;
        (letsite fcs3 ← #0) ;;
        (letsite fcs4 ← pack("S", [(field_f, fcs3)])) ;;
        (*fcs2 ::= fcs4) ;;
        ret []
    }
  ]
}

-- ----------------------------------------------------------------
-- Alpha-equivalence with hand-written examples
-- ----------------------------------------------------------------

#guard
  match parseAndTranslate simpleDanglingMvir with
  | .ok results =>
    match findFunInModule results "field" "t" with
    | some fd => alphaEquivFunDef fd hw_field_t
    | none => false
  | .error _ => false

#guard
  match parseAndTranslate simpleDanglingMvir with
  | .ok results =>
    match findFunInModule results "nested_field" "t" with
    | some fd => alphaEquivFunDef fd hw_nested_field_t
    | none => false
  | .error _ => false

-- Note: vector module skipped (vec_mut_borrow/vec_pack_0 not supported in translation)

#guard
  match parseAndTranslate simpleDanglingMvir with
  | .ok results =>
    match findFunInModule results "simple_call" "t" with
    | some fd => alphaEquivFunDef fd hw_simple_call_t
    | none => false
  | .error _ => false

#guard
  match parseAndTranslate simpleDanglingMvir with
  | .ok results =>
    match findFunInModule results "field_call" "t" with
    | some fd => alphaEquivFunDef fd hw_field_call_t
    | none => false
  | .error _ => false
