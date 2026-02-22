/-
 Copyright Ilya Sergey
 Licensed under the Apache License, Version 2.0
-/

import LeanMove.Examples.Parsing.TestUtils
import LeanMove.Examples.Typechecking.expressivity.rejected.simple_dangling

/-! ## Parse Test: simple_dangling.mvir (REJECTED)

Tests parsing of simple_dangling — the verifier stops creation of dangling references.
Five modules: field, nested_field, vector, simple_call, field_call.
Note: the vector module uses vec_mut_borrow/vec_pack_0 which are not fully supported
in translation, but parsing should succeed.
-/

open LeanMove.Lang.MoveLight
open LeanMove.Lang.MoveIR.Parser
open LeanMove.Lang.MoveIR.Translate
open LeanMove.Examples.Parsing.TestUtils
open LeanMove.Examples.Expressivity.SimpleDangling

def simpleDanglingMvir := "
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
"

-- Parse succeeds
#guard (parseMvir simpleDanglingMvir).isOk

-- 5 modules
#guard (parseMvir simpleDanglingMvir).toOption.get!.modules.length == 5

-- Translation succeeds
#guard (parseAndTranslate simpleDanglingMvir).isOk

-- Alpha-equivalence with hand-written examples
-- (only for the `t` functions that have hand-written counterparts)
#guard
  match parseAndTranslate simpleDanglingMvir with
  | .ok results =>
    match findFunInModule results "field" "t" with
    | some fd => alphaEquivFunDef fd field_dangling
    | none => false
  | .error _ => false

#guard
  match parseAndTranslate simpleDanglingMvir with
  | .ok results =>
    match findFunInModule results "nested_field" "t" with
    | some fd => alphaEquivFunDef fd nested_field_dangling
    | none => false
  | .error _ => false

-- Note: vector module skipped (vec_mut_borrow/vec_pack_0 not supported in translation)

#guard
  match parseAndTranslate simpleDanglingMvir with
  | .ok results =>
    match findFunInModule results "simple_call" "t" with
    | some fd => alphaEquivFunDef fd simple_call_dangling
    | none => false
  | .error _ => false

#guard
  match parseAndTranslate simpleDanglingMvir with
  | .ok results =>
    match findFunInModule results "field_call" "t" with
    | some fd => alphaEquivFunDef fd field_call_dangling
    | none => false
  | .error _ => false
