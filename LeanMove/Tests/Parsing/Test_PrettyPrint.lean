/-
 Copyright Ilya Sergey
 Licensed under the Apache License, Version 2.0
-/

import LeanMove.Tests.Parsing.TestUtils
import LeanMove.Lang.MoveIR.PrettyPrint

/-! ## Pretty-Printer Tests

Tests for the MoveLight pretty-printer, which converts translated `FunDef`
values back into readable Lean code using the macro syntax from `Macros.lean`.

### Usage

The pretty-printer converts MVIR → MoveLight translation results into readable
Lean code. Typical workflow:

```
-- 1. Parse and translate MVIR text
let results ← parseAndTranslate mvirSource

-- 2. Pretty-print all translated functions
IO.println (ppTranslateResults results)

-- 3. Or pretty-print a single function by name
let fd := findFunInModule results "ModuleName" "functionName"
IO.println (ppFunDef "functionName" fd)
```
-/

open LeanMove.Lang.MoveLight
open LeanMove.Lang.MoveIR.Parser
open LeanMove.Lang.MoveIR.Translate
open LeanMove.Lang.MoveIR.PrettyPrint
open LeanMove.Tests.Parsing.TestUtils

/-- Check if `sub` appears as a substring in `s` -/
def hasSubstr (s sub : String) : Bool :=
  (s.splitOn sub).length > 1

/- ====================================================== -/
/-       Usage Example                                     -/
/- ====================================================== -/

-- End-to-end example: parse MVIR text, translate to MoveLight, and pretty-print.
-- The output uses the macro syntax from Macros.lean (letsite, ;;, copy, etc.)
/-
#eval do
  let mvir := "
//# publish
module 0x1.Example {
  struct Pair has copy, drop { x: u64, y: u64 }
  swap(p: &mut Self.Pair) {
    let tmp: u64;
  label b0:
    tmp = *&mut copy(p).Pair::x;
    *&mut copy(p).Pair::x = *&mut copy(p).Pair::y;
    *&mut copy(p).Pair::y = copy(tmp);
    return;
  }
}
"
  match parseAndTranslate mvir with
  | .ok results =>
    IO.println "=== All functions in module ==="
    IO.println (ppTranslateResults results)
    IO.println ""
    IO.println "=== Single function extraction ==="
    match findFunInModule results "Example" "swap" with
    | some fd => IO.println (ppFunDef "swap" fd)
    | none => IO.println "Function not found"
  | .error e => IO.println s!"Parse/translate error: {e}"
-/

/- ====================================================== -/
/-       Test MVIR Source                                  -/
/- ====================================================== -/

def ppTestMvir := "
//# publish
module 0x1.Simple {

struct S has copy, drop { f: u64 }

borrow_f(s: &mut Self.S): &mut u64 {
label b0:
    return &mut copy(s).S::f;
}

write(s: &mut Self.S) {
    let x: &mut u64;
label b0:
    x = Self.borrow_f(copy(s));
    *copy(x) = 0;
    return;
}

}
"

/- ====================================================== -/
/-       Pretty-Print Output                              -/
/- ====================================================== -/

-- Parse and translate
#guard (parseAndTranslate ppTestMvir).isOk

-- Pretty-print the translated result
def ppTestOutput : String :=
  match parseAndTranslate ppTestMvir with
  | .ok results => ppTranslateResults results
  | .error e => s!"Error: {e}"

-- Display the output
-- #eval IO.println ppTestOutput

/- ====================================================== -/
/-       Output Verification                              -/
/- ====================================================== -/

-- Function names
#guard hasSubstr ppTestOutput "def borrow_f : FunDef"
#guard hasSubstr ppTestOutput "def write : FunDef"

-- Module annotation
#guard hasSubstr ppTestOutput "-- Module: Simple"

-- Parameters with types
#guard hasSubstr ppTestOutput ".siteBorrowMut"
#guard hasSubstr ppTestOutput ".paramRef"

-- Return types
#guard hasSubstr ppTestOutput "some true"

-- Block labels
#guard hasSubstr ppTestOutput "label := \"b0\""

-- Macro syntax: letsite with copy
#guard hasSubstr ppTestOutput "letsite"
#guard hasSubstr ppTestOutput "copy"

-- Macro syntax: borrowMutField
#guard hasSubstr ppTestOutput "borrowMutField("

-- Macro syntax: statement sequencing
#guard hasSubstr ppTestOutput ";;"

-- Macro syntax: call
#guard hasSubstr ppTestOutput "call("
#guard hasSubstr ppTestOutput "\"Simple.borrow_f\""

-- Macro syntax: assign
#guard hasSubstr ppTestOutput "::="

-- Macro syntax: integer literal
#guard hasSubstr ppTestOutput "#0"

-- Macro syntax: ret
#guard hasSubstr ppTestOutput "ret ["

-- Local variable declarations
#guard hasSubstr ppTestOutput ".ref .u64"

/- ====================================================== -/
/-       Pretty-Print Individual Functions                -/
/- ====================================================== -/

-- Pretty-print a single function
def ppBorrowF : String :=
  match parseAndTranslate ppTestMvir with
  | .ok results =>
    match findFunInModule results "Simple" "borrow_f" with
    | some fd => ppFunDef "borrow_f" fd
    | none => "not found"
  | .error e => s!"Error: {e}"

-- #eval IO.println ppBorrowF

-- Verify single-function output
#guard hasSubstr ppBorrowF "def borrow_f : FunDef"
#guard hasSubstr ppBorrowF "ret ["
#guard hasSubstr ppBorrowF "borrowMutField("

/- ====================================================== -/
/-       Pretty-Print with Multiple Blocks                -/
/- ====================================================== -/

def ppMultiBlockMvir := "
//# publish
module 0x1.Branch {

struct S has copy, drop { f: u64 }

branch_test(s: &mut Self.S, b: bool) {
    let x: &mut u64;
label entry:
    jump_if (copy(b)) then;
label else:
    return;
label then:
    x = &mut copy(s).S::f;
    *move(x) = 0;
    return;
}

}
"

#guard (parseAndTranslate ppMultiBlockMvir).isOk

def ppMultiBlockOutput : String :=
  match parseAndTranslate ppMultiBlockMvir with
  | .ok results => ppTranslateResults results
  | .error e => s!"Error: {e}"

-- #eval IO.println ppMultiBlockOutput

-- Multi-block: should have branch and jump syntax
#guard hasSubstr ppMultiBlockOutput "branch"
#guard hasSubstr ppMultiBlockOutput "ret []"
-- Should have multiple labels
#guard hasSubstr ppMultiBlockOutput "label := \"entry\""
#guard hasSubstr ppMultiBlockOutput "label := \"then\""
#guard hasSubstr ppMultiBlockOutput "label := \"else\""
