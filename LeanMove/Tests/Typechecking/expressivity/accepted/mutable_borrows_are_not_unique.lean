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
import LeanMove.Lang.MoveIR.PrettyPrint
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

-- Hand-written FunDefs moved to Tests/Parsing/Test_mutable_borrows_are_not_unique.lean

-- -----------------------------------------------------
-- -    Parsed MVIR Programs                           --
-- -----------------------------------------------------

open LeanMove.Tests.Parsing.TestUtils

private def mutableBorrowsNotUniqueMvir :=
  include_str "../../../MVIR/mutable_borrows_are_not_unique.mvir"

private def parsedFuns := (parseAndTranslate mutableBorrowsNotUniqueMvir).toOption.get!

def parsed_fields :=
  (findFunInModule parsedFuns "fields" "create").get!

def parsed_fields_write :=
  (findFunInModule parsedFuns "fields_write" "write").get!

-- Uncomment to pretty-print the parsed FunDefs:
-- #eval IO.println (ppFunDef "create" parsed_fields)
-- #eval IO.println (ppFunDef "write" parsed_fields_write)

-- -----------------------------------------------------
-- -           Algorithmic Type Checking Tests        --
-- -----------------------------------------------------

-- Initial environments (decidable)
def fields_lenvDec := mkLabelEnvDec parsed_fields

def fields_write_lenvDec := mkLabelEnvDec parsed_fields_write

-- Theorems: both functions type check algorithmically
theorem fields_check : check_fun_dec parsed_fields fields_lenvDec = true := by native_decide

set_option maxRecDepth 4096 in
theorem fields_write_check : check_fun_dec parsed_fields_write fields_write_lenvDec = true := by native_decide

-- -----------------------------------------------------
-- -           Relational Type Checking Theorems      --
-- -----------------------------------------------------

theorem fields_welltyped : ∃ lenv, typecheck_fun parsed_fields lenv AssocMap.empty :=
  ⟨_, check_fun_dec_sound _ _ _ fields_check⟩

theorem fields_write_welltyped : ∃ lenv, typecheck_fun parsed_fields_write lenv AssocMap.empty :=
  ⟨_, check_fun_dec_sound _ _ _ fields_write_check⟩

end LeanMove.Tests.Expressivity.MutableBorrowsNotUnique
