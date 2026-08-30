/-
 Copyright Ilya Sergey
 Licensed under the Apache License, Version 2.0
-/

import LeanMove.Lang.MoveLight
import LeanMove.Typing.TypeChecking
import LeanMove.Typing.Algorithmic.AlgorithmicTypeChecking
import LeanMove.Lang.Macros
import LeanMove.Semantics.Smallstep
import LeanMove.Tests.Parsing.TestUtils

/-!
# Known gaps

Unlike every other file under `Tests/`, the `#guard`s here pin down behaviour that is
**wrong**. Each one records a divergence from the Move bytecode verifier that the rest of
the suite does not currently detect. When a gap is fixed the corresponding `#guard` will
fail; that is the point. The fix is to flip the expectation, move the case into
`expressivity/rejected/`, and delete it from here.

## G1. The call rule ignores outstanding extensions of its mutable arguments

`check_mutable_inputs_isolated` (`Typing/TypeChecking.lean`) is

```
∀ mi_site ∈ bs, ∀ other_site ∈ bs, … → ∀ p, interpret_regex (paths (mi_ref, other_ref)) p → p = []
```

Both quantifiers range over `bs`, the call's own argument sites. So the premise rules out
arguments that reach *each other*, and says nothing about references borrowed out of an
argument earlier in the block and still live across the call. `check_mutable_inputs_isolated_bool`
(`Typing/Algorithmic/AlgorithmicTypeChecking.lean`) mirrors it faithfully, so this is not a
spec/algorithm disagreement that `check_stmt_sound` could catch — the relational
specification has the same hole, and the `call` constructor of `typecheck_stmt` carries no
other premise that would cover it.

The intended rule is recorded in the imported corpus at
`Tests/MVIR/mutable_borrows_are_not_unique_calls.mvir:18`: *"as long as the argument to the
call does not have any extensions at the time of the call (and as long as it does not
overlap with any other arguments)"*. Only the parenthetical half is implemented.

Consequence: every write the checker rejects inline is accepted when a callee performs it.
The four modules of `call_rule_extension_gap.mvir` pair each call-routed form with its
inline analogue, over a struct, a vector, and an enum variant change.

Note that `rejected/enum_invalid_ref_unpack.lean` does cover the enum case (its modules 2, 4
and 7 are the `Self.overwrite(...)` variants, upstream error
`CALL_BORROWED_MUTABLE_REFERENCE_ERROR`), but checks them with an empty `funEnv`, so
`lookup env.funEnv fnName` returns `none` and they are rejected before the borrow rules are
consulted. Supplying the callee's signature, as this file does, flips them to accepted.

## G2. A bare `Self.f(args);` statement can never be checked

`Lang/MoveIR/Parser.lean:540` desugars a call used as a statement into
`.assign ["_"] (.call …)`, and `Lang/MoveIR/Translate.lean:444` then allocates one result
site per variable in that list. A function with no return values therefore acquires a
phantom output site, `populate_call_outputs` fails against `rets = []`, and the call is
rejected whatever it does. No test in the suite calls a void function, which is why this
went unnoticed. The helpers in `call_rule_extension_gap.mvir` all return a dummy `u64` to
work around it; `void_call_is_rejected` below pins the underlying behaviour.

## Runtime note: none of these produce a `danglingRef`

The accepted programs are executed at the bottom of this file. All of them halt. A clobber
cannot dangle a reference in this heap model, for three separate reasons:

* **structs** — a runtime reference is `Loc × List Field` and `writeRef` cannot change the
  shape at a location, since the type system forces the replacement to have the same
  record type. `readPath` still finds the field, and the borrow reads the clobbered value.
* **vectors** — `vecMutBorrow` (`Semantics/Smallstep.lean:838`) `alloc`s a *copy* of the
  element and returns a reference to that fresh location. A vector element borrow is
  therefore not an alias at all: mutating, clearing or popping the vector cannot be
  observed through it, and it reads the value captured at borrow time.
* **enums** — `buildFlatVariantFields` (`Semantics/Smallstep.lean:141`) gives every variant
  value the fields of *all* variants, with the inactive ones defaulted. Changing the variant
  does not remove `Two::y` from the heap value; it resets it to `0`. So the path still
  resolves.

So the mechanised soundness theorem is not threatened by G1: the accepted programs read a
stale or defaulted value rather than dangling. What that costs is conformance with the
production verifier, and it means the runtime certificates cannot witness this class of bug.
-/

namespace LeanMove.Tests.KnownGaps

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Typing
open LeanMove.Semantics
open AssocMap
open LeanMove.Tests.Parsing.TestUtils

private def src := include_str "../MVIR/call_rule_extension_gap.mvir"

#guard (parseAndTranslate src).isOk

private def parsedFuns := (parseAndTranslate src).toOption.get!

def enumEnv : EnumEnv :=
  match (parseAndTranslateWithEnums src : Except String _) with
  | Except.ok (_, ee) => ee
  | Except.error _ => AssocMap.empty

private def fn (modName fname : String) : FunDef :=
  (findFunInModule parsedFuns modName fname).get!

/-- The signature a callee actually has, read off its parsed definition. Building the
    `funEnv` this way is what distinguishes these tests from the existing enum ones,
    which check calls against an empty `funEnv` and so reject them vacuously. -/
private def sigOf (f : FunDef) : FunSig :=
  ⟨f.params.map (fun p => p.2.toParamType), f.returnType⟩

private def funEnv : FunEnv :=
  AssocMap.insert
    (AssocMap.insert
      (AssocMap.insert
        (AssocMap.insert AssocMap.empty "swap.borrow_f" (sigOf (fn "swap" "borrow_f")))
        "clobber.clobberS" (sigOf (fn "clobber" "clobberS")))
      "vecprobe.clearV" (sigOf (fn "vecprobe" "clearV")))
    "enumprobe.overwrite" (sigOf (fn "enumprobe" "overwrite"))

private def accepts (modName fname : String) : Bool :=
  let f := fn modName fname
  check_fun f (mkLabelEnv f funEnv enumEnv) enumEnv

/- ====================================================== -/
/-  G1. Call-routed clobbers, paired with inline analogues -/
/- ====================================================== -/

-- Baseline: the callee definitions themselves check out, so a `false` below is about the
-- caller and not about a malformed helper.
#guard accepts "swap" "borrow_f"
#guard accepts "clobber" "clobberS"
#guard accepts "vecprobe" "clearV"
#guard accepts "enumprobe" "overwrite"

-- Control: accepted upstream *and* here, because `s` has no extensions at the call.
#guard accepts "swap" "create"

-- GAP: `mutable_borrows_are_not_unique_calls.mvir:21` says this "will error".
#guard accepts "swap" "create_swapped"          -- expected: !accepts

-- GAP: struct clobber. The inline form is rejected.
#guard accepts "clobber" "clobber_via_call"     -- expected: !accepts
#guard !accepts "clobber" "clobber_inline"

-- GAP: vector clobber. The inline form is module 0x22 of vec_dangling_borrow.mvir.
#guard accepts "vecprobe" "clear_via_call"      -- expected: !accepts
#guard !accepts "vecprobe" "clear_inline"

-- GAP: enum variant change. Upstream: CALL_BORROWED_MUTABLE_REFERENCE_ERROR.
#guard accepts "enumprobe" "overwrite_via_call" -- expected: !accepts
#guard !accepts "enumprobe" "overwrite_inline"

/- ====================================================== -/
/-  G2. Void calls                                        -/
/- ====================================================== -/

/-- `clobberS` with its return value stripped, i.e. what the natural spelling of these
    tests would be. Rejected purely because of the parser/translator desugaring, so this
    `#guard` says nothing about borrow checking. -/
private def voidClobber : FunDef :=
  { fn "clobber" "clobberS" with returnType := [] }

#guard !check_fun voidClobber (mkLabelEnv voidClobber funEnv enumEnv) enumEnv

/- ====================================================== -/
/-  Runtime behaviour of the accepted programs            -/
/- ====================================================== -/

private def rtFunEnv : AssocMap Id FunDef :=
  AssocMap.insert
    (AssocMap.insert
      (AssocMap.insert AssocMap.empty "clobber.clobberS" (fn "clobber" "clobberS"))
      "vecprobe.clearV" (fn "vecprobe" "clearV"))
    "enumprobe.overwrite" (fn "enumprobe" "overwrite")

private def sHeap : Heap × Loc :=
  Heap.empty.alloc (.record [(⟨"f"⟩, .int 42 .u64)])

private def vHeap : Heap × Loc :=
  Heap.empty.alloc (.vec .u64 [.int 42 .u64, .int 43 .u64])

private def xHeap : Heap × Loc :=
  Heap.empty.alloc (.variant "Two" "enumprobe.X"
    [(MoveLight.qualifyField "One" ⟨"x"⟩, .int 7 .u64),
     (MoveLight.qualifyField "Two" ⟨"x"⟩, .int 1 .u64),
     (MoveLight.qualifyField "Two" ⟨"y"⟩, .int 2 .u64)])

private def runClobber :=
  run 200 (initState (fn "clobber" "clobber_via_call") rtFunEnv [.ref sHeap.2 []] sHeap.1)

private def runVec :=
  run 200 (initState (fn "vecprobe" "clear_via_call") rtFunEnv [.ref vHeap.2 []] vHeap.1)

private def runEnum :=
  run 200 (initState (fn "enumprobe" "overwrite_via_call") rtFunEnv [.ref xHeap.2 []] xHeap.1
            (enumEnv := enumEnv))

-- Struct: `*e` reads the clobbered field, 0 rather than the original 42. No dangling ref,
-- because the replacement value is another `S` and so still has field `f`.
#guard runClobber.getHaltedValues == some [.int 0 .u64]

-- Vector: `*r` reads 42, the value the element had when it was borrowed, even though the
-- vector is now empty. `vecMutBorrow` copied the element to a fresh location, so the
-- borrow never observed the clear at all — it is not an alias.
#guard runVec.getHaltedValues == some [.int 42 .u64]

-- Enum: `*y` reads 0. `Two::y` survives the change to variant `One` under the flat
-- encoding and is reset to its default, rather than disappearing.
#guard runEnum.getHaltedValues == some [.int 0 .u64]

-- Stated separately, since it is the load-bearing claim: none of the three dangle.
#guard !(runClobber matches .error (.danglingRef _))
#guard !(runVec matches .error (.danglingRef _))
#guard !(runEnum matches .error (.danglingRef _))

end LeanMove.Tests.KnownGaps
