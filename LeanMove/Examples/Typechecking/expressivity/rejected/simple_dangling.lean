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
import LeanMove.Typing.Algorithmic.TypeCheckingAlgorithmic
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
module 0x5.field_call {
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

namespace LeanMove.Examples.Expressivity.SimpleDangling

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
  params := [(var_s, .ref (.trecord s_entries) (.varRef var_s) .siteBorrowMut)]
  returnType := .basic .tunit
  locals := [
    { name := var_f, type := .ref .u64 (.refid 0) .siteBorrowImm }
  ]
  blocks := [
    { label := "b0"
      body :=
        -- f = &copy(s).S::f (immutable borrow of field)
        (letsite s0 ← copy var_s) ;;
        Stmt.letBind s1 (Expr.borrowField s0 (.trecord s_entries) field_f) ;;
        (var_f ::= s1) ;;
        -- *move(s) = S { f: 0 } -- ERROR: s is borrowed via f
        (letsite s2 ← move var_s) ;;
        (letsite s3 ← #0) ;;
        Stmt.letBind s4 (Expr.pack "S" [(field_f, s3)]) ;;
        Stmt.writeRef s2 s4 ;;
        Stmt.ret []
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
  params := [(var_p, .ref (.trecord p_entries) (.varRef var_p) .siteBorrowMut)]
  returnType := .basic .tunit
  locals := [
    { name := var_s, type := .ref (.trecord s_entries) (.refid 1) .siteBorrowMut },
    { name := var_f, type := .ref .u64 (.refid 2) .siteBorrowImm }
  ]
  blocks := [
    { label := "b0"
      body :=
        -- s = &mut copy(p).P::s
        (letsite s0 ← copy var_p) ;;
        Stmt.letBind s1 (Expr.borrowMutField s0 (.trecord p_entries) field_s) ;;
        (var_s ::= s1) ;;
        -- f = &copy(s).S::f
        (letsite s2 ← copy var_s) ;;
        Stmt.letBind s3 (Expr.borrowField s2 (.trecord s_entries) field_f) ;;
        (var_f ::= s3) ;;
        -- *move(p) = P { s: S { f: 0 } } -- ERROR: p is borrowed
        (letsite s4 ← move var_p) ;;
        (letsite s5 ← #0) ;;
        Stmt.letBind s6 (Expr.pack "S" [(field_f, s5)]) ;;
        Stmt.letBind s7 (Expr.pack "P" [(field_s, s6)]) ;;
        Stmt.writeRef s4 s7 ;;
        Stmt.ret []
    }
  ]
}

-- Module 3: vector - Skipped (MoveLight doesn't have native vector support)

/-
  Module 4: simple_call
  Creates local, borrows it, passes to function returning immutable ref,
  then tries to write through the mutable ref.

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

  We inline the call to f() as: i = freeze(copy(m))
-/
def simple_call_dangling : FunDef := {
  params := []
  returnType := .basic .tunit
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
        -- i = freeze(copy(m)) (inlined call to f)
        (letsite s2 ← copy var_m) ;;
        Stmt.letBind s3 (Expr.freeze s2) ;;
        (var_i ::= s3) ;;
        -- *copy(m) = 0 -- ERROR: m has immutable alias i
        (letsite s4 ← copy var_m) ;;
        (letsite s5 ← #0) ;;
        Stmt.writeRef s4 s5 ;;
        Stmt.ret []
    }
  ]
}

/-
  Module 5: field_call
  Takes mutable ref to struct, calls function that borrows field immutably,
  then tries to write through the original ref.

  t(s: &mut Self.S) {
      let f: &u64;
  label b0:
      f = Self.f(copy(s));      // f returns &move(r).S::f
      *copy(s) = S { f: 0 };    // ERROR: s borrowed via f
      return;
  }

  We inline the call as: f = &copy(s).S::f
-/
def field_call_dangling : FunDef := {
  params := [(var_s, .ref (.trecord s_entries) (.varRef var_s) .siteBorrowMut)]
  returnType := .basic .tunit
  locals := [
    { name := var_f, type := .ref .u64 (.refid 0) .siteBorrowImm }
  ]
  blocks := [
    { label := "b0"
      body :=
        -- f = &copy(s).S::f (inlined call)
        (letsite s0 ← copy var_s) ;;
        Stmt.letBind s1 (Expr.borrowField s0 (.trecord s_entries) field_f) ;;
        (var_f ::= s1) ;;
        -- *copy(s) = S { f: 0 } -- ERROR: s is borrowed via f
        (letsite s2 ← copy var_s) ;;
        (letsite s3 ← #0) ;;
        Stmt.letBind s4 (Expr.pack "S" [(field_f, s3)]) ;;
        Stmt.writeRef s2 s4 ;;
        Stmt.ret []
    }
  ]
}

/-!
## Why these are rejected

All four functions are rejected at `writeRef` by `check_outbound_bool`, which checks
whether the written-through reference has any outbound edges in the PathEnv. In each case,
a field borrow (or freeze-derived immutable ref) creates a non-empty path from the
write target's reference to another live reference, so the write is rejected:

- **field_dangling:** After `f = &copy(s).S::f`, the PathEnv records that `f`'s reference
  extends `s`'s reference via `[.field "f"]`. The `writeRef` through `move(s)` fails because
  `check_outbound_bool` finds this outbound edge.

- **nested_field_dangling:** After `s = &mut copy(p).P::s` and `f = &copy(s).S::f`, `p`'s
  reference has outbound paths to both `s`'s and (transitively) `f`'s references. The
  `writeRef` through `move(p)` fails.

- **simple_call_dangling:** After `i = freeze(copy(m))`, `consume_ref_transfer` transfers
  `m`'s borrow paths to `i`'s new immutable reference. The PathEnv shows outbound edges
  from `m`'s reference to `i`'s reference, so `writeRef` through `copy(m)` is rejected.

- **field_call_dangling:** Same mechanism as `field_dangling` — borrows field via `s`,
  then tries to write through `s` while the field borrow is live.

## Runtime behavior

All four functions halt successfully. The interpreter performs heap writes without checking
reference aliasing. The "dangling" references still point to valid heap locations (just with
updated values). No runtime error occurs because borrow tracking is purely a static safety
mechanism — the small-step semantics intentionally does not enforce it.
-/

-- -----------------------------------------------------
-- -           Algorithmic Type Checking Tests        --
-- -----------------------------------------------------

-- Initial environment for field_dangling
def field_dangling_initEnv : TypeEnv := {
  siteEnv := AssocMap.empty
  varEnv := init_fun_varEnv field_dangling
  pathEnv := PathEnv.init
  funEnv := AssocMap.empty
}

def field_dangling_lenv : LabelEnv :=
  AssocMap.insert AssocMap.empty "b0" field_dangling_initEnv

#eval check_fun field_dangling field_dangling_lenv

#guard !check_fun field_dangling field_dangling_lenv

-- Initial environment for nested_field_dangling
def nested_field_dangling_initEnv : TypeEnv := {
  siteEnv := AssocMap.empty
  varEnv := init_fun_varEnv nested_field_dangling
  pathEnv := PathEnv.init
  funEnv := AssocMap.empty
}

def nested_field_dangling_lenv : LabelEnv :=
  AssocMap.insert AssocMap.empty "b0" nested_field_dangling_initEnv

#eval check_fun nested_field_dangling nested_field_dangling_lenv

#guard !check_fun nested_field_dangling nested_field_dangling_lenv

-- Initial environment for simple_call_dangling
def simple_call_dangling_initEnv : TypeEnv := {
  siteEnv := AssocMap.empty
  varEnv := init_fun_varEnv simple_call_dangling
  pathEnv := PathEnv.init
  funEnv := AssocMap.empty
}

def simple_call_dangling_lenv : LabelEnv :=
  AssocMap.insert AssocMap.empty "b0" simple_call_dangling_initEnv

#eval check_fun simple_call_dangling simple_call_dangling_lenv

#guard !check_fun simple_call_dangling simple_call_dangling_lenv

-- Initial environment for field_call_dangling
def field_call_dangling_initEnv : TypeEnv := {
  siteEnv := AssocMap.empty
  varEnv := init_fun_varEnv field_call_dangling
  pathEnv := PathEnv.init
  funEnv := AssocMap.empty
}

def field_call_dangling_lenv : LabelEnv :=
  AssocMap.insert AssocMap.empty "b0" field_call_dangling_initEnv

#eval check_fun field_call_dangling field_call_dangling_lenv

#guard !check_fun field_call_dangling field_call_dangling_lenv

end LeanMove.Examples.Expressivity.SimpleDangling
