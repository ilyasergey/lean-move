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

def subtreeWritesReleaseMvir :=
  include_str "../Typechecking/expressivity/accepted/subtree_writes_release.mvir"

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
    | some fd => alphaEquivFunDef fd parsed_t
    | none => false
  | .error _ => false
