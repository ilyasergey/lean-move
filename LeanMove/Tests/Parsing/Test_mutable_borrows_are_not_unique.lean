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
-/

open LeanMove.Lang.MoveLight
open LeanMove.Lang.MoveIR.Parser
open LeanMove.Lang.MoveIR.Translate
open LeanMove.Tests.Parsing.TestUtils
open LeanMove.Tests.Expressivity.MutableBorrowsNotUnique

def mutableBorrowsAreNotUniqueMvir := "
// mutable borrows are not unique

//# publish
module 0x2.fields {

    struct S has copy, drop { f: u64 }
    struct Pair has copy, drop { s1: Self.S, s2: Self.S }

    create(p: &mut Self.Pair) {
        let p2: &mut Self.Pair;
        let s1_1: &mut Self.S;
        let s1_2: &mut Self.S;
        let s2_1: &mut Self.S;
        let s2_2: &mut Self.S;
        let f_1_1: &mut u64;
        let f_1_2: &mut u64;
        let f_2_1: &mut u64;
        let f_2_2: &mut u64;
    label b0:
        s1_1 = &mut copy(p).Pair::s1;
        s2_1 = &mut copy(p).Pair::s2;
        f_1_1 = &mut copy(s1_1).S::f;
        f_2_1 = &mut copy(s2_1).S::f;

        p2 = copy(p);
        s1_2 = &mut copy(p2).Pair::s1;
        s2_2 = &mut copy(p2).Pair::s2;
        f_1_2 = &mut copy(s1_2).S::f;
        f_2_2 = &mut copy(s2_2).S::f;

        return;
    }
}

//# publish
module 0x3.fields_write {

    struct S has copy, drop { f: u64 }
    struct Pair has copy, drop { s1: Self.S, s2: Self.S }

    write(p: &mut Self.Pair) {
        let p2: &mut Self.Pair;
        let s1_1: &mut Self.S;
        let s1_2: &mut Self.S;
        let s2_1: &mut Self.S;
        let s2_2: &mut Self.S;
        let f_1_1: &mut u64;
        let f_1_2: &mut u64;
        let f_2_1: &mut u64;
        let f_2_2: &mut u64;
    label b0:
        s1_1 = &mut copy(p).Pair::s1;
        s2_1 = &mut copy(p).Pair::s2;
        f_1_1 = &mut copy(s1_1).S::f;
        f_2_1 = &mut copy(s2_1).S::f;

        p2 = copy(p);
        s1_2 = &mut copy(p2).Pair::s1;
        s2_2 = &mut copy(p2).Pair::s2;
        f_1_2 = &mut copy(s1_2).S::f;
        f_2_2 = &mut copy(s2_2).S::f;

        *move(f_2_2) = 0;
        *move(f_2_1) = 0;
        *move(f_1_2) = 0;
        *move(f_1_1) = 0;
        *move(s1_1) = S { f: 0 };
        *move(s2_1) = S { f: 0 };
        *move(s1_2) = S { f: 0 };
        *move(s2_2) = S { f: 0 };

        return;
    }
}
"

-- Parse succeeds
#guard (parseMvir mutableBorrowsAreNotUniqueMvir).isOk

-- Translation succeeds
#guard (parseAndTranslate mutableBorrowsAreNotUniqueMvir).isOk

-- Alpha-equivalence with hand-written examples
#guard
  match parseAndTranslate mutableBorrowsAreNotUniqueMvir with
  | .ok results =>
    match findFunInModule results "fields" "create" with
    | some fd => alphaEquivFunDef fd parsed_fields
    | none => false
  | .error _ => false

#guard
  match parseAndTranslate mutableBorrowsAreNotUniqueMvir with
  | .ok results =>
    match findFunInModule results "fields_write" "write" with
    | some fd => alphaEquivFunDef fd parsed_fields_write
    | none => false
  | .error _ => false
