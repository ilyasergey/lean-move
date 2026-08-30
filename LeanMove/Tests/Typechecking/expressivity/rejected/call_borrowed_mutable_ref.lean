/-
 Copyright Ilya Sergey
 Licensed under the Apache License, Version 2.0
-/

import LeanMove.Lang.MoveLight
import LeanMove.Typing.TypeChecking
import LeanMove.Typing.Algorithmic.DecidableTypeEnv
import LeanMove.Lang.Macros
import LeanMove.Tests.Parsing.TestUtils

/-!
# Call with a borrowed mutable reference

Source: `Tests/MVIR/call_borrowed_mutable_ref.mvir`.
Upstream error: `CALL_BORROWED_MUTABLE_REFERENCE_ERROR`.

A mutable reference passed to a function must have no outstanding extensions at the
point of the call. `check_mutable_inputs_isolated` ranges both of its site variables
over the argument list, so it only rules out arguments that reach *each other*; the
`call` rule's `check_mutable_inputs_no_extensions` premise supplies the other half,
reusing the `check_outbound` obligation that `write_ref` discharges for a direct write.

Three rejected programs, one per kind of clobber, each paired with an accepted control
that performs the same operations with no live borrow across the call:

| | rejected | accepted control |
|---|---|---|
| struct | `clobber_via_call`, `create_swapped` | `create`, `clobber_after_read` |
| vector | `clear_via_call` | `clear_after_read` |
| enum | `overwrite_via_call` | `overwrite_after_read` |

The controls are load-bearing. Without them, a rule that rejected every call taking a
`&mut` argument would satisfy the rejection tests just as well. `create` in particular is
accepted by the Move bytecode verifier and is copied verbatim from
`Tests/MVIR/mutable_borrows_are_not_unique_calls.mvir`, whose comment at line 21 is what
predicts `create_swapped` must fail.

Unlike `rejected/enum_invalid_ref_unpack.lean`, every check here runs against a `funEnv`
carrying the callee's real signature, derived from its parsed `FunDef`. Checking a call
against an empty `funEnv` rejects it at `lookup env.funEnv fnName` before the borrow rules
are reached, which is a vacuous pass.
-/

namespace LeanMove.Tests.Expressivity.CallBorrowedMutableRef

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Typing
open LeanMove.Tests.Parsing.TestUtils

private def src := include_str "../../../MVIR/call_borrowed_mutable_ref.mvir"

#guard (parseAndTranslate src).isOk

private def parsedFuns := (parseAndTranslate src).toOption.get!

def enumEnv : EnumEnv :=
  match (parseAndTranslateWithEnums src : Except String _) with
  | Except.ok (_, ee) => ee
  | Except.error _ => AssocMap.empty

private def fn (modName fname : String) : FunDef :=
  (findFunInModule parsedFuns modName fname).get!

/-- The signature a callee actually has, read off its parsed definition. -/
private def sigOf (f : FunDef) : FunSig :=
  ⟨f.params.map (fun p => p.2.toParamType), f.returnType⟩

private def funEnv : FunEnv :=
  AssocMap.insert
    (AssocMap.insert
      (AssocMap.insert
        (AssocMap.insert AssocMap.empty
          "struct_clobber.clobberS" (sigOf (fn "struct_clobber" "clobberS")))
        "struct_clobber.borrow_f" (sigOf (fn "struct_clobber" "borrow_f")))
      "vector_clear.clearV" (sigOf (fn "vector_clear" "clearV")))
    "enum_overwrite.overwrite" (sigOf (fn "enum_overwrite" "overwrite"))

private def checks (modName fname : String) : Bool :=
  let f := fn modName fname
  check_fun_dec f (mkLabelEnvDec f funEnv enumEnv) enumEnv

/- ====================================================== -/
/-  Callees check out on their own                        -/
/- ====================================================== -/

#guard checks "struct_clobber" "clobberS"
#guard checks "struct_clobber" "borrow_f"
#guard checks "vector_clear" "clearV"
#guard checks "enum_overwrite" "overwrite"

/- ====================================================== -/
/-  Struct                                                -/
/- ====================================================== -/

/-- Overwriting the whole struct through a callee, while a field of it is borrowed. -/
theorem struct_clobber_via_call_rejected :
    checks "struct_clobber" "clobber_via_call" = false := by native_decide

/-- `mutable_borrows_are_not_unique_calls.mvir:21`: "if we swap the call with the field
    borrow, this will error". -/
theorem struct_create_swapped_rejected :
    checks "struct_clobber" "create_swapped" = false := by native_decide

/-- Control: accepted upstream, and the borrow is created after the call. -/
theorem struct_create_accepted :
    checks "struct_clobber" "create" = true := by native_decide

/-- Control: the borrow is consumed before the call. -/
theorem struct_clobber_after_read_accepted :
    checks "struct_clobber" "clobber_after_read" = true := by native_decide

/- ====================================================== -/
/-  Vector                                                -/
/- ====================================================== -/

/-- Clearing the vector through a callee, while one of its elements is borrowed. -/
theorem vector_clear_via_call_rejected :
    checks "vector_clear" "clear_via_call" = false := by native_decide

/-- Control: the element borrow is consumed before the call. -/
theorem vector_clear_after_read_accepted :
    checks "vector_clear" "clear_after_read" = true := by native_decide

/- ====================================================== -/
/-  Enum                                                  -/
/- ====================================================== -/

/-- Changing the variant through a callee, while a field of the old variant is borrowed. -/
theorem enum_overwrite_via_call_rejected :
    checks "enum_overwrite" "overwrite_via_call" = false := by native_decide

/-- Control: the unpacked field borrows are consumed before the call. -/
theorem enum_overwrite_after_read_accepted :
    checks "enum_overwrite" "overwrite_after_read" = true := by native_decide

end LeanMove.Tests.Expressivity.CallBorrowedMutableRef
