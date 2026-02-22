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
import LeanMove.Typing.Algorithmic.AlgorithmicTypeChecking
import LeanMove.Typing.Algorithmic.AlgorithmicTypingSoundness
import LeanMove.Lang.Macros

/-!
# Genuine Dangling Pointer Example

This file demonstrates a genuine dangling pointer: a field reference that becomes
invalid at runtime because the parent struct is overwritten with a different struct type.

Unlike the `simple_dangling` examples (which the runtime handles fine because the
overwritten struct still has the same fields), here the parent struct is replaced with
a struct that has *different fields*, causing the field path to become invalid.

Original Move-like pseudocode:
```
module 0x1.dangling {

    struct S has copy, drop { f: u64 }
    struct T has copy, drop { g: u64 }

    foo() {
        let s: S;
        let r: &mut S;
        let f_ref: &u64;
        let dummy: u64;
    label b0:
        s = S { f: 42 };
        r = &mut s;
        f_ref = &copy(r).S::f;       // borrow field f
        *move(r) = T { g: 0 };       // overwrite with different struct!
        dummy = *copy(f_ref);         // DANGLING: field "f" no longer exists
        return;
    }
}
```
-/

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Typing
open AssocMap
open Regex

namespace LeanMove.Tests.DanglingRef

-- Field definitions
def field_f : Field := ⟨"f"⟩
def field_g : Field := ⟨"g"⟩

-- S { f: u64 }
def s_entries : AssocMap Field BasicMoveType := insert empty field_f .u64

-- T { g: u64 }
def t_entries : AssocMap Field BasicMoveType := insert empty field_g .u64

-- Variables
def var_s : Var := ⟨"s"⟩
def var_r : Var := ⟨"r"⟩
def var_f_ref : Var := ⟨"f_ref"⟩
def var_dummy : Var := ⟨"dummy"⟩

-- Sites
def s0 : Site := .site 0   -- integer literal 42
def s1 : Site := .site 1   -- pack S { f: s0 }
def s2 : Site := .site 2   -- &mut s
def s3 : Site := .site 3   -- copy(r)
def s4 : Site := .site 4   -- &copy(r).S::f (borrow field)
def s5 : Site := .site 5   -- move(r)
def s6 : Site := .site 6   -- integer literal 0
def s7 : Site := .site 7   -- pack T { g: s6 }
def s8 : Site := .site 8   -- copy(f_ref)
def s9 : Site := .site 9   -- *copy(f_ref) (readRef)

/-
  foo() — genuine dangling pointer

  foo() {
      let s: S;             -- S = { f: u64 }
      let r: &mut S;
      let f_ref: &u64;
      let dummy: u64;
  label b0:
      s = S { f: 42 };
      r = &mut s;
      f_ref = &copy(r).S::f;       // borrow field "f" → ref loc [field "f"]
      *move(r) = T { g: 0 };       // overwrite: heap now has {g: 0}, field "f" gone!
      dummy = *copy(f_ref);         // DANGLING: readPath {g:0} [field "f"] → none!
      return;
  }
-/
def foo : FunDef := {
  params := []
  returnType := []
  locals := [
    { name := var_s, type := .basic (.trecord s_entries) },
    { name := var_r, type := .ref (.trecord s_entries) (.paramRef var_s) .siteBorrowMut },
    { name := var_f_ref, type := .ref .u64 (.paramRef var_s) .siteBorrowImm },
    { name := var_dummy, type := .basic .u64 }
  ]
  blocks := [
    { label := "b0"
      body :=
        -- s = S { f: 42 }
        (letsite s0 ← #42) ;;
        (letsite s1 ← pack("S", [(field_f, s0)])) ;;
        (var_s ::= s1) ;;
        -- r = &mut s
        (letsite s2 ← &mut var_s) ;;
        (var_r ::= s2) ;;
        -- f_ref = &copy(r).S::f
        (letsite s3 ← copy var_r) ;;
        (letsite s4 ← borrowField(s3, .trecord s_entries, field_f)) ;;
        (var_f_ref ::= s4) ;;
        -- *move(r) = T { g: 0 }  — overwrites S{f:42} with T{g:0}!
        (letsite s5 ← move var_r) ;;
        (letsite s6 ← #0) ;;
        (letsite s7 ← pack("T", [(field_g, s6)])) ;;
        (*s5 ::= s7) ;;
        -- dummy = *copy(f_ref)  — DANGLING: field "f" no longer exists
        (letsite s8 ← copy var_f_ref) ;;
        (letsite s9 ← *s8) ;;
        (var_dummy ::= s9) ;;
        ret []
    }
  ]
}

/-!
## Why this is rejected by the type checker

The `writeRef` at `*move(r) = T { g: 0 }` is rejected by `check_outbound_bool`:
after `f_ref = &copy(r).S::f`, the PathEnv records that `f_ref`'s reference extends
`r`'s reference via `[.field "f"]`. When `writeRef` through `move(r)` is checked,
`check_outbound_bool` finds this outbound edge and rejects the write — it could
invalidate the borrow held by `f_ref`.

## Why this fails at runtime

Unlike the `simple_dangling` examples where the overwritten struct still has the same
fields (so the runtime succeeds), here the struct is replaced with `T { g: 0 }` which
has *different* fields. The field reference `f_ref` holds path `[field "f"]`, but
`readPath` on `record [(g, 0)]` finds no field `"f"` and returns `none`, producing
a `danglingRef` runtime error. This is a genuine dangling pointer.
-/

-- -----------------------------------------------------
-- -           Algorithmic Type Checking Tests        --
-- -----------------------------------------------------

def foo_lenv := mkLabelEnv foo

-- Debug
#eval check_fun foo foo_lenv

-- Test: algorithmic checker rejects foo
#guard !check_fun foo foo_lenv

end LeanMove.Tests.DanglingRef
