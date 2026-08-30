/-
 Copyright Ilya Sergey
 Licensed under the Apache License, Version 2.0
-/

import LeanMove.Lang.MoveLight
import LeanMove.Typing.TypeChecking
import LeanMove.Typing.Algorithmic.AlgorithmicTypeChecking
import LeanMove.Lang.Macros
import LeanMove.Tests.Parsing.TestUtils

/-!
# Known gaps

Unlike every other file under `Tests/`, the `#guard`s here pin down behaviour that is
**wrong**. Each records a divergence from the Move bytecode verifier that the rest of the
suite does not detect. When a gap is fixed the corresponding `#guard` fails; that is the
point. The fix is then to flip the expectation, move the case into the appropriate
`accepted/` or `rejected/` directory, and delete it from here.

## G1. A bare `Self.f(args);` statement can never be checked

`Lang/MoveIR/Parser.lean:540` desugars a call used as a statement into
`.assign ["_"] (.call …)`, and `Lang/MoveIR/Translate.lean:444` then allocates one result
site per variable in that list. A function with no return values therefore acquires a
phantom output site, `populate_call_outputs` fails against `rets = []`, and the call is
rejected whatever it does — the borrow rules are never consulted.

No test in the suite calls a void function, which is why this went unnoticed. Every helper
in `call_borrowed_mutable_ref.mvir` returns a dummy `u64` to work around it.

The minimal fix is in the parser: emit an empty variable list for a bare call rather than
`["_"]`, so `for _ in vars` allocates no result sites and `buildAssigns [] [] cont` reduces
to `cont`. The explicit-discard form `_ = Self.f(x);` keeps its current behaviour. Landing
that needs a void-call test in both directions — one that should check and one that should
not — or the fix goes back to being unexercised.

## Previously listed here

**The call rule ignoring outstanding extensions of its mutable arguments** was G1 until it
was fixed by the `check_mutable_inputs_no_extensions` premise on `typecheck_stmt.call`. Its
cases now live in `expressivity/rejected/call_borrowed_mutable_ref.lean`, covering a struct,
a vector and an enum clobber, each with an accepted control.
-/

namespace LeanMove.Tests.KnownGaps

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Typing
open AssocMap
open LeanMove.Tests.Parsing.TestUtils

private def src := include_str "../MVIR/call_borrowed_mutable_ref.mvir"

#guard (parseAndTranslate src).isOk

private def parsedFuns := (parseAndTranslate src).toOption.get!

private def fn (modName fname : String) : FunDef :=
  (findFunInModule parsedFuns modName fname).get!

private def sigOf (f : FunDef) : FunSig :=
  ⟨f.params.map (fun p => p.2.toParamType), f.returnType⟩

private def funEnv : FunEnv :=
  AssocMap.insert AssocMap.empty
    "struct_clobber.clobberS" (sigOf (fn "struct_clobber" "clobberS"))

/- ====================================================== -/
/-  G1. Void calls                                        -/
/- ====================================================== -/

/-- `clobberS` with its return value stripped — the natural spelling of a clobber helper,
    and what `*move(s) = S { f: 0 }; return;` would translate to. Rejected purely because
    of the parser/translator desugaring, so this says nothing about borrow checking. -/
private def voidClobber : FunDef :=
  { fn "struct_clobber" "clobberS" with returnType := [] }

#guard !check_fun voidClobber (mkLabelEnv voidClobber funEnv) AssocMap.empty  -- expected: checks

end LeanMove.Tests.KnownGaps
