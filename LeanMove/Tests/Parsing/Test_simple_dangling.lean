/-
 Copyright Ilya Sergey
 Licensed under the Apache License, Version 2.0
-/

import LeanMove.Tests.Parsing.TestUtils
import LeanMove.Tests.Typechecking.expressivity.rejected.simple_dangling

/-! ## Parse Test: simple_dangling.mvir (REJECTED)

Tests parsing of simple_dangling — the verifier stops creation of dangling references.
Five modules: field, nested_field, vector, simple_call, field_call.
Note: the vector module uses vec_mut_borrow/vec_pack_0 which are not fully supported
in translation, but parsing should succeed.
-/

open LeanMove.Lang.MoveLight
open LeanMove.Lang.MoveIR.Parser
open LeanMove.Lang.MoveIR.Translate
open LeanMove.Tests.Parsing.TestUtils
open LeanMove.Tests.Expressivity.SimpleDangling

def simpleDanglingMvir :=
  include_str "../Typechecking/expressivity/rejected/simple_dangling.mvir"

-- Parse succeeds
#guard (parseMvir simpleDanglingMvir).isOk

-- 5 modules
#guard (parseMvir simpleDanglingMvir).toOption.get!.modules.length == 5

-- Translation succeeds
#guard (parseAndTranslate simpleDanglingMvir).isOk

-- Alpha-equivalence with hand-written examples
-- (only for the `t` functions that have hand-written counterparts)
#guard
  match parseAndTranslate simpleDanglingMvir with
  | .ok results =>
    match findFunInModule results "field" "t" with
    | some fd => alphaEquivFunDef fd parsed_field_t
    | none => false
  | .error _ => false

#guard
  match parseAndTranslate simpleDanglingMvir with
  | .ok results =>
    match findFunInModule results "nested_field" "t" with
    | some fd => alphaEquivFunDef fd parsed_nested_field_t
    | none => false
  | .error _ => false

-- Note: vector module skipped (vec_mut_borrow/vec_pack_0 not supported in translation)

#guard
  match parseAndTranslate simpleDanglingMvir with
  | .ok results =>
    match findFunInModule results "simple_call" "t" with
    | some fd => alphaEquivFunDef fd parsed_simple_call_t
    | none => false
  | .error _ => false

#guard
  match parseAndTranslate simpleDanglingMvir with
  | .ok results =>
    match findFunInModule results "field_call" "t" with
    | some fd => alphaEquivFunDef fd parsed_field_call_t
    | none => false
  | .error _ => false
