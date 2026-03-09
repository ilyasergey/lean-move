/-
 Copyright Ilya Sergey
 Licensed under the Apache License, Version 2.0
-/

import LeanMove.Tests.Parsing.TestUtils
import LeanMove.Tests.Typechecking.expressivity.accepted.mutable_borrows_are_not_unique

/-! ## Parse Test: mutable_borrows_are_not_unique.mvir

Tests parsing of mutable_borrows_are_not_unique — demonstrates that mutable borrows
are not unique, with nested struct field borrows. Two modules: fields (create) and
fields_write (write).

Alpha-equivalence tests compare the parser output against hand-written
FunDefs to validate correct translation.
-/

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Lang.MoveIR.Parser
open LeanMove.Lang.MoveIR.Translate
open LeanMove.Tests.Parsing.TestUtils
open LeanMove.Tests.Expressivity.MutableBorrowsNotUnique

def mutableBorrowsAreNotUniqueMvir :=
  include_str "../MVIR/mutable_borrows_are_not_unique.mvir"

-- Parse succeeds
#guard (parseMvir mutableBorrowsAreNotUniqueMvir).isOk

-- Translation succeeds
#guard (parseAndTranslate mutableBorrowsAreNotUniqueMvir).isOk

-- ----------------------------------------------------------------
-- Hand-written FunDefs for alpha-equivalence testing
-- ----------------------------------------------------------------

-- Sites (temporaries for A-normal form)
private def s0 : Site := .site 0
private def s1 : Site := .site 1
private def s2 : Site := .site 2
private def s3 : Site := .site 3
private def s4 : Site := .site 4
private def s5 : Site := .site 5
private def s6 : Site := .site 6
private def s7 : Site := .site 7
private def s8 : Site := .site 8
private def s9 : Site := .site 9
private def s10 : Site := .site 10
private def s11 : Site := .site 11
private def s12 : Site := .site 12
private def s13 : Site := .site 13
private def s14 : Site := .site 14
private def s15 : Site := .site 15
private def s16 : Site := .site 16
private def s17 : Site := .site 17
private def s18 : Site := .site 18
private def s19 : Site := .site 19
private def s20 : Site := .site 20
private def s21 : Site := .site 21
private def s22 : Site := .site 22
private def s23 : Site := .site 23
private def s24 : Site := .site 24
private def s25 : Site := .site 25
private def s26 : Site := .site 26
private def s27 : Site := .site 27
private def s28 : Site := .site 28
private def s29 : Site := .site 29
private def s30 : Site := .site 30
private def s31 : Site := .site 31
private def s32 : Site := .site 32
private def s33 : Site := .site 33
private def s34 : Site := .site 34
private def s35 : Site := .site 35
private def s36 : Site := .site 36

/-
  Module 1: fields
  Creates multiple mutable references to nested fields without writing.
-/
private def hw_fields : FunDef := {
  params := [(var_p, .ref (.trecord pair_entries) r0 .siteBorrowMut)]
  returnType := []
  locals := [
    { name := var_p2, type := .ref (.trecord pair_entries) (.refid 5) .siteBorrowMut },
    { name := var_s1_1, type := .ref (.trecord s_entries) (.refid 1) .siteBorrowMut },
    { name := var_s1_2, type := .ref (.trecord s_entries) (.refid 6) .siteBorrowMut },
    { name := var_s2_1, type := .ref (.trecord s_entries) (.refid 2) .siteBorrowMut },
    { name := var_s2_2, type := .ref (.trecord s_entries) (.refid 7) .siteBorrowMut },
    { name := var_f_1_1, type := .ref .u64 (.refid 3) .siteBorrowMut },
    { name := var_f_1_2, type := .ref .u64 (.refid 8) .siteBorrowMut },
    { name := var_f_2_1, type := .ref .u64 (.refid 4) .siteBorrowMut },
    { name := var_f_2_2, type := .ref .u64 (.refid 9) .siteBorrowMut }
  ]
  blocks := [
    { label := "b0"
      body :=
        -- s1_1 = &mut copy(p).Pair::s1
        (letsite s0 ← copy var_p) ;;
        (letsite s1 ← borrowMutField(s0, .trecord pair_entries, field_s1)) ;;
        (var_s1_1 ::= s1) ;;
        -- s2_1 = &mut copy(p).Pair::s2
        (letsite s2 ← copy var_p) ;;
        (letsite s3 ← borrowMutField(s2, .trecord pair_entries, field_s2)) ;;
        (var_s2_1 ::= s3) ;;
        -- f_1_1 = &mut copy(s1_1).S::f
        (letsite s4 ← copy var_s1_1) ;;
        (letsite s5 ← borrowMutField(s4, .trecord s_entries, field_f)) ;;
        (var_f_1_1 ::= s5) ;;
        -- f_2_1 = &mut copy(s2_1).S::f
        (letsite s6 ← copy var_s2_1) ;;
        (letsite s7 ← borrowMutField(s6, .trecord s_entries, field_f)) ;;
        (var_f_2_1 ::= s7) ;;
        -- p2 = copy(p)
        (letsite s8 ← copy var_p) ;;
        (var_p2 ::= s8) ;;
        -- s1_2 = &mut copy(p2).Pair::s1
        (letsite s9 ← copy var_p2) ;;
        (letsite s10 ← borrowMutField(s9, .trecord pair_entries, field_s1)) ;;
        (var_s1_2 ::= s10) ;;
        -- s2_2 = &mut copy(p2).Pair::s2
        (letsite s11 ← copy var_p2) ;;
        (letsite s12 ← borrowMutField(s11, .trecord pair_entries, field_s2)) ;;
        (var_s2_2 ::= s12) ;;
        -- f_1_2 = &mut copy(s1_2).S::f
        (letsite s13 ← copy var_s1_2) ;;
        (letsite s14 ← borrowMutField(s13, .trecord s_entries, field_f)) ;;
        (var_f_1_2 ::= s14) ;;
        -- f_2_2 = &mut copy(s2_2).S::f
        (letsite s15 ← copy var_s2_2) ;;
        (letsite s16 ← borrowMutField(s15, .trecord s_entries, field_f)) ;;
        (var_f_2_2 ::= s16) ;;
        ret []
    }
  ]
}

/-
  Module 2: fields_write
  Same as fields but also writes through all references.
  The writes are safe because "order does not matter as long as
  the reference has no extensions."
-/
private def hw_fields_write : FunDef := {
  params := [(var_p, .ref (.trecord pair_entries) r0 .siteBorrowMut)]
  returnType := []
  locals := [
    { name := var_p2, type := .ref (.trecord pair_entries) (.refid 5) .siteBorrowMut },
    { name := var_s1_1, type := .ref (.trecord s_entries) (.refid 1) .siteBorrowMut },
    { name := var_s1_2, type := .ref (.trecord s_entries) (.refid 6) .siteBorrowMut },
    { name := var_s2_1, type := .ref (.trecord s_entries) (.refid 2) .siteBorrowMut },
    { name := var_s2_2, type := .ref (.trecord s_entries) (.refid 7) .siteBorrowMut },
    { name := var_f_1_1, type := .ref .u64 (.refid 3) .siteBorrowMut },
    { name := var_f_1_2, type := .ref .u64 (.refid 8) .siteBorrowMut },
    { name := var_f_2_1, type := .ref .u64 (.refid 4) .siteBorrowMut },
    { name := var_f_2_2, type := .ref .u64 (.refid 9) .siteBorrowMut }
  ]
  blocks := [
    { label := "b0"
      body :=
        -- s1_1 = &mut copy(p).Pair::s1
        (letsite s0 ← copy var_p) ;;
        (letsite s1 ← borrowMutField(s0, .trecord pair_entries, field_s1)) ;;
        (var_s1_1 ::= s1) ;;
        -- s2_1 = &mut copy(p).Pair::s2
        (letsite s2 ← copy var_p) ;;
        (letsite s3 ← borrowMutField(s2, .trecord pair_entries, field_s2)) ;;
        (var_s2_1 ::= s3) ;;
        -- f_1_1 = &mut copy(s1_1).S::f
        (letsite s4 ← copy var_s1_1) ;;
        (letsite s5 ← borrowMutField(s4, .trecord s_entries, field_f)) ;;
        (var_f_1_1 ::= s5) ;;
        -- f_2_1 = &mut copy(s2_1).S::f
        (letsite s6 ← copy var_s2_1) ;;
        (letsite s7 ← borrowMutField(s6, .trecord s_entries, field_f)) ;;
        (var_f_2_1 ::= s7) ;;
        -- p2 = copy(p)
        (letsite s8 ← copy var_p) ;;
        (var_p2 ::= s8) ;;
        -- s1_2 = &mut copy(p2).Pair::s1
        (letsite s9 ← copy var_p2) ;;
        (letsite s10 ← borrowMutField(s9, .trecord pair_entries, field_s1)) ;;
        (var_s1_2 ::= s10) ;;
        -- s2_2 = &mut copy(p2).Pair::s2
        (letsite s11 ← copy var_p2) ;;
        (letsite s12 ← borrowMutField(s11, .trecord pair_entries, field_s2)) ;;
        (var_s2_2 ::= s12) ;;
        -- f_1_2 = &mut copy(s1_2).S::f
        (letsite s13 ← copy var_s1_2) ;;
        (letsite s14 ← borrowMutField(s13, .trecord s_entries, field_f)) ;;
        (var_f_1_2 ::= s14) ;;
        -- f_2_2 = &mut copy(s2_2).S::f
        (letsite s15 ← copy var_s2_2) ;;
        (letsite s16 ← borrowMutField(s15, .trecord s_entries, field_f)) ;;
        (var_f_2_2 ::= s16) ;;
        -- Writes: order does not matter as long as the reference has no extensions
        -- *move(f_2_2) = 0
        (letsite s17 ← move var_f_2_2) ;;
        (letsite s25 ← #0) ;;
        (*s17 ::= s25) ;;
        -- *move(f_2_1) = 0
        (letsite s18 ← move var_f_2_1) ;;
        (letsite s26 ← #0) ;;
        (*s18 ::= s26) ;;
        -- *move(f_1_2) = 0
        (letsite s19 ← move var_f_1_2) ;;
        (letsite s27 ← #0) ;;
        (*s19 ::= s27) ;;
        -- *move(f_1_1) = 0
        (letsite s20 ← move var_f_1_1) ;;
        (letsite s28 ← #0) ;;
        (*s20 ::= s28) ;;
        -- *move(s1_1) = S { f: 0 }
        (letsite s21 ← move var_s1_1) ;;
        (letsite s29 ← #0) ;;
        (letsite s30 ← pack("S", [(field_f, s29)])) ;;
        (*s21 ::= s30) ;;
        -- *move(s2_1) = S { f: 0 }
        (letsite s22 ← move var_s2_1) ;;
        (letsite s31 ← #0) ;;
        (letsite s32 ← pack("S", [(field_f, s31)])) ;;
        (*s22 ::= s32) ;;
        -- *move(s1_2) = S { f: 0 }
        (letsite s23 ← move var_s1_2) ;;
        (letsite s33 ← #0) ;;
        (letsite s34 ← pack("S", [(field_f, s33)])) ;;
        (*s23 ::= s34) ;;
        -- *move(s2_2) = S { f: 0 }
        (letsite s24 ← move var_s2_2) ;;
        (letsite s35 ← #0) ;;
        (letsite s36 ← pack("S", [(field_f, s35)])) ;;
        (*s24 ::= s36) ;;
        ret []
    }
  ]
}

-- ----------------------------------------------------------------
-- Alpha-equivalence with hand-written examples
-- ----------------------------------------------------------------

#guard
  match parseAndTranslate mutableBorrowsAreNotUniqueMvir with
  | .ok results =>
    match findFunInModule results "fields" "create" with
    | some fd => alphaEquivFunDef fd hw_fields
    | none => false
  | .error _ => false

#guard
  match parseAndTranslate mutableBorrowsAreNotUniqueMvir with
  | .ok results =>
    match findFunInModule results "fields_write" "write" with
    | some fd => alphaEquivFunDef fd hw_fields_write
    | none => false
  | .error _ => false
