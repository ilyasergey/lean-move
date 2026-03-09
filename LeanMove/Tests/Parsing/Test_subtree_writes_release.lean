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

Alpha-equivalence tests compare the parser output against hand-written
FunDefs to validate correct translation.
-/

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Lang.MoveIR.Parser
open LeanMove.Lang.MoveIR.Translate
open LeanMove.Tests.Parsing.TestUtils
open LeanMove.Tests.Expressivity.SubtreeWritesRelease

def subtreeWritesReleaseMvir :=
  include_str "../MVIR/subtree_writes_release.mvir"

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

-- ----------------------------------------------------------------
-- Hand-written FunDef for alpha-equivalence testing
-- ----------------------------------------------------------------

-- Sites (distinct per block)
-- l0: branch
private def s0 : Site := .site 0     -- move(cond)
-- l1 (false branch): x = &mut root.l; y = &mut x.l.l
private def s1 : Site := .site 1     -- copy(root)
private def s2 : Site := .site 2     -- borrowMutField(s1, Tree, l) → Sub1
private def s3 : Site := .site 3     -- copy(x)
private def s4 : Site := .site 4     -- borrowMutField(s3, Sub1, l) → Sub2
private def s5 : Site := .site 5     -- borrowMutField(s4, Sub2, l) → u64
-- l2 (true branch): x = &mut root.r; y = &mut x.r.r
private def s6 : Site := .site 6     -- copy(root)
private def s7 : Site := .site 7     -- borrowMutField(s6, Tree, r) → Sub1
private def s8 : Site := .site 8     -- copy(x)
private def s9 : Site := .site 9     -- borrowMutField(s8, Sub1, r) → Sub2
private def s10 : Site := .site 10   -- borrowMutField(s9, Sub2, r) → u64
-- l3: release x; write to root.l.r; write through y; return
private def s11 : Site := .site 11   -- move(x) [release]
private def s12 : Site := .site 12   -- copy(root)
private def s13 : Site := .site 13   -- borrowMutField(s12, Tree, l) → Sub1
private def s14 : Site := .site 14   -- borrowMutField(s13, Sub1, r) → Sub2
private def s15 : Site := .site 15   -- integer literal 0 (for Sub2.l)
private def s16 : Site := .site 16   -- integer literal 0 (for Sub2.r)
private def s17 : Site := .site 17   -- pack("Sub2", [(l, s15), (r, s16)])
private def s18 : Site := .site 18   -- move(y)
private def s19 : Site := .site 19   -- integer literal 0 (for *move(y))

private def hw_t : FunDef := {
  params := [
    (var_cond, .basic .tbool),
    (var_root, .ref (.trecord tree_entries) root_var .siteBorrowMut)
  ]
  returnType := []
  locals := [
    { name := var_x, type := .ref (.trecord sub1_entries) (.refid 1) .siteBorrowMut },
    { name := var_y, type := .ref .u64 (.refid 3) .siteBorrowMut }
  ]
  blocks := [
    -- l0: jump_if (move(cond)) l2;
    { label := "l0"
      body :=
        (letsite s0 ← move var_cond) ;;
        branch s0 "l2" "l1"
    },
    -- l1 (false branch): x = &mut root.l; y = &mut x.l.l; jump l3
    { label := "l1"
      body :=
        (letsite s1 ← copy var_root) ;;
        (letsite s2 ← borrowMutField(s1, .trecord tree_entries, field_l)) ;;
        (var_x ::= s2) ;;
        (letsite s3 ← copy var_x) ;;
        (letsite s4 ← borrowMutField(s3, .trecord sub1_entries, field_l)) ;;
        (letsite s5 ← borrowMutField(s4, .trecord sub2_entries, field_l)) ;;
        (var_y ::= s5) ;;
        jump "l3"
    },
    -- l2 (true branch): x = &mut root.r; y = &mut x.r.r; jump l3
    { label := "l2"
      body :=
        (letsite s6 ← copy var_root) ;;
        (letsite s7 ← borrowMutField(s6, .trecord tree_entries, field_r)) ;;
        (var_x ::= s7) ;;
        (letsite s8 ← copy var_x) ;;
        (letsite s9 ← borrowMutField(s8, .trecord sub1_entries, field_r)) ;;
        (letsite s10 ← borrowMutField(s9, .trecord sub2_entries, field_r)) ;;
        (var_y ::= s10) ;;
        jump "l3"
    },
    -- l3: _ = move(x); write to root.l.r; *move(y) = 0; return
    { label := "l3"
      body :=
        -- _ = move(x) [release]
        (letsite s11 ← move var_x) ;;
        release s11 ;;
        -- *(&mut (&mut copy(root).Tree::l).Sub1::r) = Sub2 { l: 0, r: 0 }
        (letsite s12 ← copy var_root) ;;
        (letsite s13 ← borrowMutField(s12, .trecord tree_entries, field_l)) ;;
        (letsite s14 ← borrowMutField(s13, .trecord sub1_entries, field_r)) ;;
        (letsite s15 ← #0) ;;
        (letsite s16 ← #0) ;;
        (letsite s17 ← pack("Sub2", [(field_l, s15), (field_r, s16)])) ;;
        (*s14 ::= s17) ;;
        -- *move(y) = 0
        (letsite s18 ← move var_y) ;;
        (letsite s19 ← #0) ;;
        (*s18 ::= s19) ;;
        ret []
    }
  ]
}

-- ----------------------------------------------------------------
-- Alpha-equivalence with hand-written example
-- ----------------------------------------------------------------

#guard
  match parseAndTranslate subtreeWritesReleaseMvir with
  | .ok results =>
    match findFun results "t" with
    | some fd => alphaEquivFunDef fd hw_t
    | none => false
  | .error _ => false
