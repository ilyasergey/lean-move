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
import LeanMove.Lang.MoveIR.PrettyPrint
import LeanMove.Tests.Parsing.TestUtils

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

-- Hand-written FunDefs moved to Tests/Parsing/Test_simple_dangling.lean

-- Function signature for f(r: &mut u64): &u64
def simple_call_funSig : FunSig := ⟨[⟨.u64, some true⟩], [⟨.u64, some false⟩]⟩


-- Function signature for f(r: &mut S): &u64
def field_call_funSig : FunSig := ⟨[⟨.trecord s_entries, some true⟩], [⟨.u64, some false⟩]⟩


-- -----------------------------------------------------
-- -           Parsed MVIR Definitions                 --
-- -----------------------------------------------------

open LeanMove.Tests.Parsing.TestUtils

private def simpleDanglingMvir :=
  include_str "../../../MVIR/simple_dangling.mvir"

#guard (parseAndTranslate simpleDanglingMvir).isOk

private def parsedFuns := (parseAndTranslate simpleDanglingMvir).toOption.get!

-- Module: field (no funEnv needed)
def parsed_field_t := (findFunInModule parsedFuns "field" "t").get!

-- Module: nested_field (no funEnv needed)
def parsed_nested_field_t := (findFunInModule parsedFuns "nested_field" "t").get!

-- Module: simple_call (needs simple_call_funEnv)
def parsed_simple_call_t := (findFunInModule parsedFuns "simple_call" "t").get!

-- Module: field_call (needs field_call_funEnv)
def parsed_field_call_t := (findFunInModule parsedFuns "field_call" "t").get!

-- Uncomment to pretty-print the parsed FunDefs:
-- #eval IO.println (ppFunDef "t" parsed_field_t)
-- #eval IO.println (ppFunDef "t" parsed_nested_field_t)
-- #eval IO.println (ppFunDef "t" parsed_simple_call_t)
-- #eval IO.println (ppFunDef "t" parsed_field_call_t)

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

def field_dangling_lenv := mkLabelEnv parsed_field_t

#eval check_fun parsed_field_t field_dangling_lenv AssocMap.empty

#guard !check_fun parsed_field_t field_dangling_lenv AssocMap.empty

def nested_field_dangling_lenv := mkLabelEnv parsed_nested_field_t

#eval check_fun parsed_nested_field_t nested_field_dangling_lenv AssocMap.empty

#guard !check_fun parsed_nested_field_t nested_field_dangling_lenv AssocMap.empty

-- Function environment for simple_call (contains signature of f)
def simple_call_funEnv : FunEnv :=
  AssocMap.insert AssocMap.empty "f" simple_call_funSig

def simple_call_dangling_lenv := mkLabelEnv parsed_simple_call_t simple_call_funEnv

#eval check_fun parsed_simple_call_t simple_call_dangling_lenv AssocMap.empty

#guard !check_fun parsed_simple_call_t simple_call_dangling_lenv AssocMap.empty

-- Function environment for field_call (contains signature of f)
def field_call_funEnv : FunEnv :=
  AssocMap.insert AssocMap.empty "f" field_call_funSig

def field_call_dangling_lenv := mkLabelEnv parsed_field_call_t field_call_funEnv

#eval check_fun parsed_field_call_t field_call_dangling_lenv AssocMap.empty

#guard !check_fun parsed_field_call_t field_call_dangling_lenv AssocMap.empty

end LeanMove.Tests.Expressivity.SimpleDangling
