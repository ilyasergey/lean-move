/-
 Copyright Ilya Sergey
 Licensed under the Apache License, Version 2.0
-/

import LeanMove.Tests.Parsing.TestUtils
import LeanMove.Tests.Typechecking.expressivity.rejected.imm_borrow_after_mut_call_invalid

/-! ## Parse Test: imm_borrow_after_mut_call.mvir (REJECTED)

Tests parsing of imm_borrow_after_mut_call — can create an immutable extension
via a call after a mut borrow, but if the mut is a parent, it won't be writable.
Two modules: valid and invalid.
-/

open LeanMove.Lang.MoveLight
open LeanMove.Lang.MoveIR.Parser
open LeanMove.Lang.MoveIR.Translate
open LeanMove.Tests.Parsing.TestUtils
open LeanMove.Tests.Expressivity.ImmBorrowAfterMutCallInvalid

def immBorrowAfterMutCallMvir := "
// can create an immutabe extension via a call after a mut borrow,
// but if the mut is a parent, it won't be writable

//# publish
module 0x2.valid {

    id_mut(r: &mut u64): &mut u64 {
    label b0:
        return move(r);
    }

    id(r: &u64): &u64 {
    label b0:
        return move(r);
    }

    t() {
        let a: u64;
        let r: &mut u64;
        let mut1: &mut u64;
        let imm1: &u64;
        let imm2: &u64;
        let imm3: &u64;
    label b0:
        a = 0;
        r = &mut a;
        mut1 = Self.id_mut(copy(r));
        imm1 = Self.id(&a);
        imm2 = Self.id(freeze(copy(r)));
        imm3 = Self.id(freeze(copy(mut1)));
        _ = *copy(imm1);
        _ = *copy(imm2);
        _ = *copy(imm3);
        return;
    }
}

//# publish
module 0x2.invalid {

    id_mut(r: &mut u64): &mut u64 {
    label b0:
        return move(r);
    }

    id(r: &u64): &u64 {
    label b0:
        return move(r);
    }

    t() {
        let a: u64;
        let r: &mut u64;
        let mut1: &mut u64;
        let imm1: &u64;
    label b0:
        a = 0;
        r = &mut a;
        mut1 = Self.id_mut(copy(r));
        imm1 = Self.id(&a);
        *copy(mut1) = 0;
        return;
    }
}
"

-- Parse succeeds
#guard (parseMvir immBorrowAfterMutCallMvir).isOk

-- 2 modules
#guard (parseMvir immBorrowAfterMutCallMvir).toOption.get!.modules.length == 2

-- Translation succeeds
#guard (parseAndTranslate immBorrowAfterMutCallMvir).isOk

-- Alpha-equivalence: invalid module t function
#guard
  match parseAndTranslate immBorrowAfterMutCallMvir with
  | .ok results =>
    match findFunInModule results "invalid" "t" with
    | some fd => alphaEquivFunDef fd parsed_invalid
    | none => false
  | .error _ => false
