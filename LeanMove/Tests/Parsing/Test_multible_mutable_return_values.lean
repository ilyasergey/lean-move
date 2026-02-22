/-
 Copyright Ilya Sergey
 Licensed under the Apache License, Version 2.0
-/

import LeanMove.Tests.Parsing.TestUtils
import LeanMove.Tests.Typechecking.expressivity.accepted.multible_mutable_return_values

/-! ## Parse Test: multible_mutable_return_values.mvir

Tests parsing of multible_mutable_return_values — all mutable return values
of a call should be writable. Uses multi-return (return e1, e2) and
multi-assignment (x, y = call).
-/

open LeanMove.Lang.MoveLight
open LeanMove.Lang.MoveIR.Parser
open LeanMove.Lang.MoveIR.Translate
open LeanMove.Tests.Parsing.TestUtils
open LeanMove.Tests.Expressivity.MultipleMutableReturnValues

def multibleMutableReturnValuesMvir := "
// all mutable return values of a call should writable

//# publish

module 0x2.Tester {

struct Point has copy, drop, store { x: u64, y: u64 }

borrow(p: &mut Self.Point): &mut u64 * &mut u64 {
label b0:
    return &mut copy(p).Point::x, &mut copy(p).Point::y;
}

write(p: &mut Self.Point) {
    let x: &mut u64;
    let y: &mut u64;
label b0:
    x, y = Self.borrow(copy(p));
    *copy(x) = 0;
    *copy(y) = 0;
    *copy(x) = 0;
    *copy(y) = 0;
    return;
}

}
"

-- Parse succeeds
#guard (parseMvir multibleMutableReturnValuesMvir).isOk

-- Translation succeeds
#guard (parseAndTranslate multibleMutableReturnValuesMvir).isOk

-- Alpha-equivalence with hand-written examples
#guard
  match parseAndTranslate multibleMutableReturnValuesMvir with
  | .ok results =>
    match findFunInModule results "Tester" "borrow" with
    | some fd => alphaEquivFunDef fd borrow
    | none => false
  | .error _ => false

#guard
  match parseAndTranslate multibleMutableReturnValuesMvir with
  | .ok results =>
    match findFunInModule results "Tester" "write" with
    | some fd => alphaEquivFunDef fd write
    | none => false
  | .error _ => false

