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
# Simple Dangling Reference Examples

Source: https://github.com/tnowacki/sui/blob/example-tests/external-crates/move/crates/bytecode-verifier-transactional-tests/tests/reference_safety/expressivity/simple_dangling.mvir

This file contains modules that fail because they create dangling references.
All are REJECTED by the type checker.

Original MVIR:
```
// simple tests that the verifier stops the creation of a dangling reference

//# publish
module 0x2.field {
    struct S has copy, drop { f: u64 }
    t(s: &mut Self.S) {
        let f: &u64;
    label b0:
        f = &copy(s).S::f;
        *move(s) = S { f: 0 };
        return;
    }
}

//# publish
module 0x3.nested_field {
    struct S has copy, drop { f: u64 }
    struct P has copy, drop { s: Self.S }
    t(p: &mut Self.P) {
        let s: &mut Self.S;
        let f: &u64;
    label b0:
        s = &mut copy(p).P::s;
        f = &copy(s).S::f;
        *move(p) = P { s: S { f: 0 } };
        return;
    }
}

//# publish
module 0x4.vector {
    t(v: &mut vector<u64>) {
        let r: &mut u64;
    label b0:
        r = vec_mut_borrow<u64>(copy(v), 0);
        *move(v) = vec_pack_0<u64>();
        return;
    }
}

//# publish
module 0x5.simple_call {
    f(r: &mut u64): &u64 {
    label b0:
        return freeze(move(r));
    }

    t() {
        let a: u64;
        let m: &mut u64;
        let i: &u64;
    label b0:
        a = 0;
        m = &mut a;
        i = Self.f(copy(m));
        *copy(m) = 0;
        return;
    }
}

//# publish
module 0x5.field_
 {
    struct S has copy, drop { f: u64 }

    f(r: &mut Self.S): &u64 {
    label b0:
        return &move(r).S::f;
    }

    t(s: &mut Self.S) {
        let f: &u64;
    label b0:
        f = Self.f(copy(s));
        *copy(s) = S { f: 0 };
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

namespace LeanMove.Tests.Expressivity.SimpleDangling

-- Fields for structs
def field_f : Field := ⟨"f"⟩
def field_s : Field := ⟨"s"⟩

-- S { f: u64 }
def s_entries : AssocMap Field BasicMoveType := insert empty field_f .u64

-- P { s: S }
def p_entries : AssocMap Field BasicMoveType :=
  insert empty field_s (.trecord s_entries)

-- Variables
def var_s : Var := ⟨"s"⟩
def var_p : Var := ⟨"p"⟩
def var_f : Var := ⟨"f"⟩
def var_a : Var := ⟨"a"⟩
def var_m : Var := ⟨"m"⟩
def var_i : Var := ⟨"i"⟩

-- Sites
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

/-
  Module 1: field
  Takes mutable ref to struct, borrows field immutably, then writes through the ref.

  t(s: &mut Self.S) {
      let f: &u64;
  label b0:
      f = &copy(s).S::f;       // immutable borrow of field
      *move(s) = S { f: 0 };   // ERROR: writing while f borrows from s
      return;
  }
-/
def field_dangling : FunDef := {
  params := [(var_s, .ref (.trecord s_entries) (.paramRef var_s) .siteBorrowMut)]
  returnType := []
  locals := [
    { name := var_f, type := .ref .u64 (.refid 0) .siteBorrowImm }
  ]
  blocks := [
    { label := "b0"
      body :=
        -- f = &copy(s).S::f (immutable borrow of field)
        (letsite s0 ← copy var_s) ;;
        (letsite s1 ← borrowField(s0, .trecord s_entries, field_f)) ;;
        (var_f ::= s1) ;;
        -- *move(s) = S { f: 0 } -- ERROR: s is borrowed via f
        (letsite s2 ← move var_s) ;;
        (letsite s3 ← #0) ;;
        (letsite s4 ← pack("S", [(field_f, s3)])) ;;
        (*s2 ::= s4) ;;
        ret []
    }
  ]
}

/-
  Module 2: nested_field
  Takes mutable ref to P, borrows nested field, then writes through outer ref.

  t(p: &mut Self.P) {
      let s: &mut Self.S;
      let f: &u64;
  label b0:
      s = &mut copy(p).P::s;
      f = &copy(s).S::f;
      *move(p) = P { s: S { f: 0 } };  // ERROR: p borrowed via s and f
      return;
  }
-/
def nested_field_dangling : FunDef := {
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
        (letsite s0 ← copy var_p) ;;
        (letsite s1 ← borrowMutField(s0, .trecord p_entries, field_s)) ;;
        (var_s ::= s1) ;;
        -- f = &copy(s).S::f
        (letsite s2 ← copy var_s) ;;
        (letsite s3 ← borrowField(s2, .trecord s_entries, field_f)) ;;
        (var_f ::= s3) ;;
        -- *move(p) = P { s: S { f: 0 } } -- ERROR: p is borrowed
        (letsite s4 ← move var_p) ;;
        (letsite s5 ← #0) ;;
        (letsite s6 ← pack("S", [(field_f, s5)])) ;;
        (letsite s7 ← pack("P", [(field_s, s6)])) ;;
        (*s4 ::= s7) ;;
        ret []
    }
  ]
}

-- Module 3: vector - Skipped (MoveLight doesn't have native vector support)

-- Function signature for f(r: &mut u64): &u64
def simple_call_funSig : FunSig := ⟨[⟨.u64, some true⟩], [⟨.u64, some false⟩]⟩

/-
  Module 4: simple_call
  Creates local, borrows it, passes to function returning immutable ref,
  then tries to write through the mutable ref.

  f(r: &mut u64): &u64 { return freeze(move(r)); }

  t() {
      let a: u64;
      let m: &mut u64;
      let i: &u64;
  label b0:
      a = 0;
      m = &mut a;
      i = Self.f(copy(m));      // f returns freeze(move(r)), creating imm ref
      *copy(m) = 0;             // ERROR: can't write while i exists
      return;
  }
-/
def simple_call_dangling : FunDef := {
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
        (letsite s0 ← #0) ;;
        (var_a ::= s0) ;;
        -- m = &mut a
        (letsite s1 ← &mut var_a) ;;
        (var_m ::= s1) ;;
        -- i = Self.f(copy(m))  [using call macro]
        (letsite s2 ← copy var_m) ;;
        (call([s3], "f", [s2])) ;;
        (var_i ::= s3) ;;
        -- *copy(m) = 0 -- ERROR: m has immutable alias i
        (letsite s4 ← copy var_m) ;;
        (letsite s5 ← #0) ;;
        (*s4 ::= s5) ;;
        ret []
    }
  ]
}

-- Function signature for f(r: &mut S): &u64
def field_call_funSig : FunSig := ⟨[⟨.trecord s_entries, some true⟩], [⟨.u64, some false⟩]⟩

/-
  Module 5: field_call
  Takes mutable ref to struct, calls function that borrows field immutably,
  then tries to write through the original ref.

  f(r: &mut Self.S): &u64 { return &move(r).S::f; }

  t(s: &mut Self.S) {
      let f: &u64;
  label b0:
      f = Self.f(copy(s));      // f returns &move(r).S::f
      *copy(s) = S { f: 0 };    // ERROR: s borrowed via f
      return;
  }
-/
def field_call_dangling : FunDef := {
  params := [(var_s, .ref (.trecord s_entries) (.paramRef var_s) .siteBorrowMut)]
  returnType := []
  locals := [
    { name := var_f, type := .ref .u64 (.refid 0) .siteBorrowImm }
  ]
  blocks := [
    { label := "b0"
      body :=
        -- f = Self.f(copy(s))  [using call macro]
        (letsite s0 ← copy var_s) ;;
        (call([s1], "f", [s0])) ;;
        (var_f ::= s1) ;;
        -- *copy(s) = S { f: 0 } -- ERROR: s is borrowed via f
        (letsite s2 ← copy var_s) ;;
        (letsite s3 ← #0) ;;
        (letsite s4 ← pack("S", [(field_f, s3)])) ;;
        (*s2 ::= s4) ;;
        ret []
    }
  ]
}

/-!
## Why these are rejected

All four functions are rejected at `writeRef` by `check_outbound_bool`, which checks
whether the written-through reference has any outbound edges in the PathEnv. In each case,
a field borrow or call-derived output ref creates a non-empty path from the write target's
reference to another live reference, so the write is rejected:

- **field_dangling:** After `f = &copy(s).S::f`, the PathEnv records that `f`'s reference
  extends `s`'s reference via `[.field "f"]`. The `writeRef` through `move(s)` fails because
  `check_outbound_bool` finds this outbound edge.

- **nested_field_dangling:** After `s = &mut copy(p).P::s` and `f = &copy(s).S::f`, `p`'s
  reference has outbound paths to both `s`'s and (transitively) `f`'s references. The
  `writeRef` through `move(p)` fails.

- **simple_call_dangling:** After `call([s3], "f", [s2])`, `call_connect_inputs_outputs`
  creates paths from the input ref (via copy(m)) to the immutable output ref (s3).
  `check_outbound_bool` on the subsequent `copy(m)` finds these outbound edges, so the
  `writeRef` is rejected.

- **field_call_dangling:** After `call([s1], "f", [s0])`, the output ref (s1) is
  connected to the input ref (via copy(s)). `check_outbound_bool` on the subsequent
  `copy(s)` finds the path to the output ref and rejects the `writeRef`.

## Runtime behavior

All four functions halt successfully. The interpreter performs heap writes without checking
reference aliasing. The "dangling" references still point to valid heap locations (just with
updated values). No runtime error occurs because borrow tracking is purely a static safety
mechanism — the small-step semantics intentionally does not enforce it.
-/

-- -----------------------------------------------------
-- -           Algorithmic Type Checking Tests        --
-- -----------------------------------------------------

def field_dangling_lenv := mkLabelEnv field_dangling

#eval check_fun field_dangling field_dangling_lenv

#guard !check_fun field_dangling field_dangling_lenv

def nested_field_dangling_lenv := mkLabelEnv nested_field_dangling

#eval check_fun nested_field_dangling nested_field_dangling_lenv

#guard !check_fun nested_field_dangling nested_field_dangling_lenv

-- Function environment for simple_call (contains signature of f)
def simple_call_funEnv : FunEnv :=
  AssocMap.insert AssocMap.empty "f" simple_call_funSig

def simple_call_dangling_lenv := mkLabelEnv simple_call_dangling simple_call_funEnv

#eval check_fun simple_call_dangling simple_call_dangling_lenv

#guard !check_fun simple_call_dangling simple_call_dangling_lenv

-- Function environment for field_call (contains signature of f)
def field_call_funEnv : FunEnv :=
  AssocMap.insert AssocMap.empty "f" field_call_funSig

def field_call_dangling_lenv := mkLabelEnv field_call_dangling field_call_funEnv

#eval check_fun field_call_dangling field_call_dangling_lenv

#guard !check_fun field_call_dangling field_call_dangling_lenv

end LeanMove.Tests.Expressivity.SimpleDangling
