/-
 Copyright Ilya Sergey
 Licensed under the Apache License, Version 2.0
-/

import LeanMove.Examples.Parsing.TestUtils

/-! ## Parse Test: extension_after_call.mvir

Tests parsing of extension_after_call — writing to extension after a function call,
with struct definitions (Point, Box) and multiple functions.
-/

open LeanMove.Lang.MoveLight
open LeanMove.Lang.MoveIR.Parser
open LeanMove.Lang.MoveIR.Translate
open LeanMove.Examples.Parsing.TestUtils

def extensionAfterCallMvir := "
// can write to an extension after a call

//# publish

module 0x2.Tester {

struct Point has copy, drop, store { x: u64, y: u64 }
struct Box has copy, drop, store { tl: Self.Point, br: Self.Point }

borrow(p: &mut Self.Box): &mut Self.Point {
label b0:
    return &mut copy(p).Box::tl;
}

write(b: &mut Self.Box): &mut Self.Point {
    let p: &mut Self.Point;
    let x: &mut u64;
    let y: &mut u64;
label b0:
    p = Self.borrow(copy(b));
    x = &mut copy(p).Point::x;
    *move(x) = 0;
    y = &mut copy(p).Point::y;
    *move(y) = 0;
    return move(p);
}

}
"

-- Parse succeeds
#guard (parseMvir extensionAfterCallMvir).isOk

-- Translation succeeds
#guard (parseAndTranslate extensionAfterCallMvir).isOk

-- Check borrow function
#guard
  match parseAndTranslate extensionAfterCallMvir with
  | .ok results =>
    match findFun results "borrow" with
    | some fd =>
      fd.params.length == 1 &&
      fd.locals.length == 0 &&
      fd.returnType.length == 1 &&
      fd.blocks.length == 1
    | none => false
  | .error _ => false

-- Check write function
#guard
  match parseAndTranslate extensionAfterCallMvir with
  | .ok results =>
    match findFun results "write" with
    | some fd =>
      fd.params.length == 1 &&
      fd.locals.length == 3 &&
      fd.returnType.length == 1 &&
      fd.blocks.length == 1
    | none => false
  | .error _ => false

-- Note: alpha-equivalence with hand-written example is not tested because
-- the hand-written version uses different variable names (p → tl in fn_write)
-- and different parameter names (p → b in fn_borrow).
