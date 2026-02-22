/-
 Copyright Ilya Sergey
 Licensed under the Apache License, Version 2.0
-/

import LeanMove.Examples.Parsing.TestUtils
import LeanMove.Examples.Typechecking.expressivity.accepted.extension_writes_after_join

/-! ## Parse Test: extension_writes_after_join.mvir

Tests parsing of extension_writes_after_join — writing to extension after join
with struct S and conditional branching.
-/

open LeanMove.Lang.MoveLight
open LeanMove.Lang.MoveIR.Parser
open LeanMove.Lang.MoveIR.Translate
open LeanMove.Examples.Parsing.TestUtils
open LeanMove.Examples.Expressivity.ExtensionWritesAfterJoin

def extensionWritesAfterJoinMvir := "
// writing to extension after join

//# publish

module 0x2.extension_after_join {

struct S has copy, drop, store { f: u64 }

t(cond: bool, a: &mut Self.S, b: &mut Self.S): &mut Self.S {
    let x: &mut Self.S;
    let y: &mut Self.S;
    let f: &mut u64;
label l0:
    jump_if (move(cond)) l2;
label l1:
    x = move(a);
    y = move(b);
    jump l3;
label l2:
    x = move(b);
    y = move(a);
    jump l3;
label l3:
    f = &mut copy(x).S::f;
    *copy(y) = S { f: *copy(f) };
    *copy(f) = 0;
    return move(y);
}

}
"

-- Parse succeeds
#guard (parseMvir extensionWritesAfterJoinMvir).isOk

-- Translation succeeds
#guard (parseAndTranslate extensionWritesAfterJoinMvir).isOk

-- Alpha-equivalence with hand-written example
#guard
  match parseAndTranslate extensionWritesAfterJoinMvir with
  | .ok results =>
    match findFun results "t" with
    | some fd => alphaEquivFunDef fd t
    | none => false
  | .error _ => false
