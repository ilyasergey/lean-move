/-
 Copyright Ilya Sergey
 Licensed under the Apache License, Version 2.0
-/

import LeanMove.Tests.Parsing.TestUtils
import LeanMove.Tests.Typechecking.expressivity.accepted.subtree_writes_release

/-! ## Parse Test: subtree_writes_release.mvir

Tests parsing of subtree_writes_release — release is lossy in the graph,
writes are safe after release. Uses nested structs (Tree, Sub1, Sub2) with
deep field borrows and conditional branching.
-/

open LeanMove.Lang.MoveLight
open LeanMove.Lang.MoveIR.Parser
open LeanMove.Lang.MoveIR.Translate
open LeanMove.Tests.Parsing.TestUtils
open LeanMove.Tests.Expressivity.SubtreeWritesRelease

def subtreeWritesReleaseMvir := "
// release is lossy in the graph, these writes are safe

//# publish

module 0x2.extension_after_join {

struct Tree has copy, drop, store { l: Self.Sub1, r: Self.Sub1 }
struct Sub1 has copy, drop, store { l: Self.Sub2, r: Self.Sub2 }
struct Sub2 has copy, drop, store { l: u64, r: u64 }

t(cond: bool, root: &mut Self.Tree) {
    let x: &mut Self.Sub1;
    let y: &mut u64;
label l0:
    jump_if (move(cond)) l2;
label l1:
    x = &mut copy(root).Tree::l;
    y = &mut (&mut copy(x).Sub1::l).Sub2::l;
    jump l3;
label l2:
    x = &mut copy(root).Tree::r;
    y = &mut (&mut copy(x).Sub1::r).Sub2::r;
    jump l3;
label l3:
    _ = move(x);
    *(&mut (&mut copy(root).Tree::l).Sub1::r) = Sub2 { l: 0, r: 0 };
    *move(y) = 0;
    return;
}


}
"

-- Parse succeeds
#guard (parseMvir subtreeWritesReleaseMvir).isOk

-- Translation succeeds
#guard (parseAndTranslate subtreeWritesReleaseMvir).isOk

-- Check structure
#guard
  match parseAndTranslate subtreeWritesReleaseMvir with
  | .ok results =>
    match findFun results "t" with
    | some fd =>
      fd.params.length == 2 &&
      fd.locals.length == 2 &&
      fd.blocks.length == 4 &&
      fd.blocks.map (·.label) == ["l0", "l1", "l2", "l3"]
    | none => false
  | .error _ => false

-- Alpha-equivalence with hand-written example
#guard
  match parseAndTranslate subtreeWritesReleaseMvir with
  | .ok results =>
    match findFun results "t" with
    | some fd => alphaEquivFunDef fd t
    | none => false
  | .error _ => false
