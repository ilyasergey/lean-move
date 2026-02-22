/-
 Copyright Ilya Sergey

 Licensed under the Apache License, Version 2.0 (the "License");
 you may not use this file except in compliance with the License.
 You may obtain a copy of the License at

      https://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software
 distributed under the License is distributed on an "AS IS" BASIS,
 WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 See the License for the specific language governing permissions and
 limitations under the License.
-/


import LeanMove.Lang.MoveLight
import LeanMove.Typing.TypeChecking
import LeanMove.Typing.Algorithmic.DecidableTypeEnv
import LeanMove.Lang.Macros
import LeanMove.Tests.Parsing.TestUtils

/-!
# Mutable Borrows Are Not Unique

Source: https://github.com/tnowacki/sui/blob/example-tests/external-crates/move/crates/bytecode-verifier-transactional-tests/tests/reference_safety/expressivity/mutable_borrows_are_not_unique.mvir

Two modules demonstrating that mutable variables/references are not unique and
don't take ownership over their memory:

1. fields: Creates multiple mutable refs to nested fields
2. fields_write: Same but also performs writes through all refs

The key insight is that "order does not matter as long as the reference has no extensions."

Original MVIR (module fields):
```
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
```

Original MVIR (module fields_write):
```
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

    // order here does not matter as long as the reference has no extensions
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
```

The local variable types must use `.refid N` Arefs matching the order in which
`nextFreshRef` generates them during algorithmic type checking. The assignment
order in the body determines the refid values, not the declaration order.
-/

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Typing
open AssocMap
open Regex

namespace LeanMove.Tests.Expressivity.MutableBorrowsNotUnique

-- Fields for structs
def field_f : Field := ⟨"f"⟩
def field_s1 : Field := ⟨"s1"⟩
def field_s2 : Field := ⟨"s2"⟩

-- Types for nested structs
-- S { f: u64 }
def s_entries : AssocMap Field BasicMoveType := insert empty field_f .u64

-- Pair { s1: S, s2: S }
def pair_entries : AssocMap Field BasicMoveType :=
  insert (insert empty field_s1 (.trecord s_entries)) field_s2 (.trecord s_entries)

-- Abstract reference for the parameter
def r0 : Aref := .paramRef ⟨"p"⟩

-- Variables (matching MVIR naming)
def var_p : Var := ⟨"p"⟩
def var_p2 : Var := ⟨"p2"⟩
def var_s1_1 : Var := ⟨"s1_1"⟩
def var_s1_2 : Var := ⟨"s1_2"⟩
def var_s2_1 : Var := ⟨"s2_1"⟩
def var_s2_2 : Var := ⟨"s2_2"⟩
def var_f_1_1 : Var := ⟨"f_1_1"⟩
def var_f_1_2 : Var := ⟨"f_1_2"⟩
def var_f_2_1 : Var := ⟨"f_2_1"⟩
def var_f_2_2 : Var := ⟨"f_2_2"⟩

-- Sites (temporaries for A-normal form)
def s0 : Site := .site 0
def s1 : Site := .site 1
def s2 : Site := .site 2
def s3 : Site := .site 3
def s4 : Site := .site 4
def s5 : Site := .site 5
def s6 : Site := .site 6
def s7 : Site := .site 7
def s8 : Site := .site 8
def s9 : Site := .site 9
def s10 : Site := .site 10
def s11 : Site := .site 11
def s12 : Site := .site 12
def s13 : Site := .site 13
def s14 : Site := .site 14
def s15 : Site := .site 15
def s16 : Site := .site 16
def s17 : Site := .site 17
def s18 : Site := .site 18
def s19 : Site := .site 19
def s20 : Site := .site 20
def s21 : Site := .site 21
def s22 : Site := .site 22
def s23 : Site := .site 23
def s24 : Site := .site 24
-- Additional sites for integer literals and packed structs
def s25 : Site := .site 25 -- integer literal 0 for f_2_2 write
def s26 : Site := .site 26 -- integer literal 0 for f_2_1 write
def s27 : Site := .site 27 -- integer literal 0 for f_1_2 write
def s28 : Site := .site 28 -- integer literal 0 for f_1_1 write
def s29 : Site := .site 29 -- integer literal 0 for S { f: 0 } (s1_1)
def s30 : Site := .site 30 -- packed S for s1_1 write
def s31 : Site := .site 31 -- integer literal 0 for S { f: 0 } (s2_1)
def s32 : Site := .site 32 -- packed S for s2_1 write
def s33 : Site := .site 33 -- integer literal 0 for S { f: 0 } (s1_2)
def s34 : Site := .site 34 -- packed S for s1_2 write
def s35 : Site := .site 35 -- integer literal 0 for S { f: 0 } (s2_2)
def s36 : Site := .site 36 -- packed S for s2_2 write

/-
  Module 1: fields
  Creates multiple mutable references to nested fields without writing.

  Refid assignment order (determined by nextFreshRef during body execution):
    1: s1_1 = &mut copy(p).Pair::s1
    2: s2_1 = &mut copy(p).Pair::s2
    3: f_1_1 = &mut copy(s1_1).S::f
    4: f_2_1 = &mut copy(s2_1).S::f
    5: p2 = copy(p)  (ref copy creates a fresh ref)
    6: s1_2 = &mut copy(p2).Pair::s1
    7: s2_2 = &mut copy(p2).Pair::s2
    8: f_1_2 = &mut copy(s1_2).S::f
    9: f_2_2 = &mut copy(s2_2).S::f
-/
def fields : FunDef := {
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
  The writes are safe because "order does not matter as long as the reference has no extensions."
-/
def fields_write : FunDef := {
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

-- -----------------------------------------------------
-- -           Algorithmic Type Checking Tests        --
-- -----------------------------------------------------

-- Initial environments (decidable)
def fields_lenvDec := mkLabelEnvDec fields

def fields_write_lenvDec := mkLabelEnvDec fields_write

-- Theorems: both functions type check algorithmically
set_option maxRecDepth 4096 in
theorem fields_check : check_fun_dec fields fields_lenvDec = true := by rfl

set_option maxRecDepth 4096 in
theorem fields_write_check : check_fun_dec fields_write fields_write_lenvDec = true := by rfl

-- -----------------------------------------------------
-- -           Relational Type Checking Theorems      --
-- -----------------------------------------------------

theorem fields_welltyped : ∃ lenv, typecheck_fun fields lenv :=
  ⟨_, check_fun_dec_sound _ _ fields_check⟩

theorem fields_write_welltyped : ∃ lenv, typecheck_fun fields_write lenv :=
  ⟨_, check_fun_dec_sound _ _ fields_write_check⟩

-- -----------------------------------------------------
-- -    Type Checking Parsed MVIR Programs             --
-- -----------------------------------------------------

open LeanMove.Tests.Parsing.TestUtils

private def mutableBorrowsNotUniqueMvir := "
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

private def parsedFuns := (parseAndTranslate mutableBorrowsNotUniqueMvir).toOption.get!

private def parsed_fields :=
  (findFunInModule parsedFuns "fields" "create").get!

private def parsed_fields_write :=
  (findFunInModule parsedFuns "fields_write" "write").get!

#guard check_fun_dec parsed_fields (mkLabelEnvDec parsed_fields)

set_option maxRecDepth 4096 in
#guard check_fun_dec parsed_fields_write (mkLabelEnvDec parsed_fields_write)

end LeanMove.Tests.Expressivity.MutableBorrowsNotUnique
