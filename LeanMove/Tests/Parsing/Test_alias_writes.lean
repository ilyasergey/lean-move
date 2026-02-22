/-
 Copyright Ilya Sergey
 Licensed under the Apache License, Version 2.0
-/

import LeanMove.Tests.Parsing.TestUtils
import LeanMove.Tests.Typechecking.expressivity.accepted.alias_writes

/-! ## Parse Test: alias_writes.mvir

Tests parsing and translation of the alias_writes Move IR example.
Four modules: borrow_local_twice, borrow_local_twice_reverse,
borrow_local_and_copy_ref, borrow_local_and_copy_ref_reverse.
-/

open LeanMove.Lang.MoveLight
open LeanMove.Lang.MoveIR.Parser
open LeanMove.Lang.MoveIR.Translate
open LeanMove.Tests.Parsing.TestUtils
open LeanMove.Tests.Expressivity.AliasWrites

def aliasWritesMvir := "
// writing to alias writes should be consistent

//# publish

module 0x2.borrow_local_twice {

t() {
    let a: u64;
    let x: &mut u64;
    let y: &mut u64;
label b0:
    a = 0;
    x = &mut a;
    y = &mut a;
    *move(x) = 0;
    *move(y) = 0;
    return;
}

}

//# publish

module 0x3.borrow_local_twice_reverse {

t() {
    let a: u64;
    let x: &mut u64;
    let y: &mut u64;
label b0:
    a = 0;
    x = &mut a;
    y = &mut a;
    *move(y) = 0;
    *move(x) = 0;
    return;
}

}

//# publish

module 0x4.borrow_local_and_copy_ref {

t() {
    let a: u64;
    let x: &mut u64;
    let y: &mut u64;
label b0:
    a = 0;
    x = &mut a;
    y = copy(x);
    *move(x) = 0;
    *move(y) = 0;
    return;
}

}

//# publish

module 0x5.borrow_local_and_copy_ref_reverse {

t() {
    let a: u64;
    let x: &mut u64;
    let y: &mut u64;
label b0:
    a = 0;
    x = &mut a;
    y = copy(x);
    *move(y) = 0;
    *move(x) = 0;
    return;
}

}
"

-- Parse succeeds
#guard (parseMvir aliasWritesMvir).isOk

-- Correct number of modules
#guard (parseMvir aliasWritesMvir).toOption.get!.modules.length == 4

-- Translation succeeds
#guard (parseAndTranslate aliasWritesMvir).isOk

-- Alpha-equivalence with hand-written examples
#guard
  match parseAndTranslate aliasWritesMvir with
  | .ok results =>
    match findFunInModule results "borrow_local_twice" "t" with
    | some fd => alphaEquivFunDef fd parsed_borrow_local_twice
    | none => false
  | .error _ => false

#guard
  match parseAndTranslate aliasWritesMvir with
  | .ok results =>
    match findFunInModule results "borrow_local_twice_reverse" "t" with
    | some fd => alphaEquivFunDef fd parsed_borrow_local_twice_reverse
    | none => false
  | .error _ => false

#guard
  match parseAndTranslate aliasWritesMvir with
  | .ok results =>
    match findFunInModule results "borrow_local_and_copy_ref" "t" with
    | some fd => alphaEquivFunDef fd parsed_borrow_local_and_copy_ref
    | none => false
  | .error _ => false

#guard
  match parseAndTranslate aliasWritesMvir with
  | .ok results =>
    match findFunInModule results "borrow_local_and_copy_ref_reverse" "t" with
    | some fd => alphaEquivFunDef fd parsed_borrow_local_and_copy_ref_reverse
    | none => false
  | .error _ => false
