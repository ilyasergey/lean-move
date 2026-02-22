/-
 Copyright Ilya Sergey
 Licensed under the Apache License, Version 2.0
-/

import LeanMove.Tests.Parsing.TestUtils
import LeanMove.Tests.Typechecking.expressivity.accepted.alias_write_after_join

/-! ## Parse Test: alias_write_after_join.mvir

Tests parsing of alias_write_after_join — writing to alias after join with branching.
-/

open LeanMove.Lang.MoveLight
open LeanMove.Lang.MoveIR.Parser
open LeanMove.Lang.MoveIR.Translate
open LeanMove.Tests.Parsing.TestUtils
open LeanMove.Tests.Expressivity.AliasWriteAfterJoin

def aliasWriteAfterJoinMvir := "
// writing to alias after join

//# publish

module 0x2.alias_after_join_reborrow {

t(cond: bool) {
    let a: u64;
    let b: u64;
    let x: &mut u64;
    let y: &mut u64;
    let z: &mut u64;
label l0:
    a = 0;
    b = 0;
    jump_if (move(cond)) l2;
label l1:
    x = &mut a;
    y = &mut b;
    jump l3;
label l2:
    x = &mut b;
    y = &mut a;
    jump l3;
label l3:
    z = &mut a;
    *move(z) = 0;
    *move(x) = 0;
    *move(y) = 0;
    return;
}

}
"

-- Parse succeeds
#guard (parseMvir aliasWriteAfterJoinMvir).isOk

-- Translation succeeds
#guard (parseAndTranslate aliasWriteAfterJoinMvir).isOk

-- Alpha-equivalence with hand-written example
#guard
  match parseAndTranslate aliasWriteAfterJoinMvir with
  | .ok results =>
    match findFun results "t" with
    | some fd => alphaEquivFunDef fd t
    | none => false
  | .error _ => false
