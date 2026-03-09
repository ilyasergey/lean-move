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
# Enum Match

Tests basic variant_switch dispatch with packVariant and unpackVariant.
One module: m.t0 (5 blocks: l0 + variant_switch targets l1, l2, l3 + l4)

Source: enum_match.mvir
-/

namespace LeanMove.Tests.Expressivity.EnumMatch

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Typing
open LeanMove.Tests.Parsing.TestUtils
open AssocMap

private def enumMatchMvir :=
  include_str "enum_match.mvir"

#guard (parseAndTranslateWithEnums enumMatchMvir).isOk

private def parsedFuns :=
  match (parseAndTranslateWithEnums enumMatchMvir : Except String _) with
  | Except.ok (funs, _) => funs
  | Except.error _ => []

private def enumEnv : EnumEnv :=
  match (parseAndTranslateWithEnums enumMatchMvir : Except String _) with
  | Except.ok (_, ee) => ee
  | Except.error _ => AssocMap.empty

def parsed_t0 := (findFunInModule parsedFuns "m" "t0").get!

-- Verify parsing succeeds
#guard parsedFuns.length == 1
#guard parsed_t0.blocks.length == 5

-- Variable names (from parsed locals)
private def var_loc1 : Var := ⟨"loc1"⟩
private def var_loc3 : Var := ⟨"loc3"⟩

-- VarEnv at variant_switch targets (l1, l2, l3):
-- loc1 was assigned before the switch, others still invalid
private def switch_target_varEnv : VarEnv :=
  let ve := init_fun_varEnv parsed_t0
  match lookup ve var_loc1 with
  | some (_, τ, ms) => update ve var_loc1 (.validVar, τ, ms)
  | none => ve

-- VarEnv at join point l4:
-- loc3 was assigned in all branches, loc1 was consumed (moved)
-- copier/inner: invalidVar in label env (some branches have them valid,
-- but the relaxed varenv check allows invalidVar to match validVar)
private def join_varEnv : VarEnv :=
  let ve := init_fun_varEnv parsed_t0
  match lookup ve var_loc3 with
  | some (_, τ, ms) => update ve var_loc3 (.validVar, τ, ms)
  | none => ve

-- Manual label env with precise varEnvs for each block
def t0_lenvDec : LabelEnvDec :=
  let f := freshenBlockEnv parsed_t0
  let initEnv := mkInitEnvDec parsed_t0 (enumEnv := enumEnv)
  let switchEnv : TypeEnvDec :=
    { siteEnv := AssocMap.empty, varEnv := switch_target_varEnv,
      pathEnv := init_fun_pathEnvDec parsed_t0.params, funEnv := AssocMap.empty,
      enumEnv := enumEnv }
  let joinEnv : TypeEnvDec :=
    { siteEnv := AssocMap.empty, varEnv := join_varEnv,
      pathEnv := init_fun_pathEnvDec parsed_t0.params, funEnv := AssocMap.empty,
      enumEnv := enumEnv }
  insert (insert (insert (insert (insert AssocMap.empty
    "l0" (f initEnv))
    "l1" (f switchEnv))
    "l2" (f switchEnv))
    "l3" (f switchEnv))
    "l4" (f joinEnv)

-- Check all blocks pass
private def t0_lenv := t0_lenvDec.toLabelEnv

private def checkBlockAt (i : Nat) : Bool :=
  match parsed_t0.blocks[i]? with
  | none => false
  | some block =>
    match lookup t0_lenv block.label with
    | none => false
    | some blockEnv => check_block t0_lenv block blockEnv parsed_t0.returnType

#guard checkBlockAt 0   -- l0
#guard checkBlockAt 1   -- l1
#guard checkBlockAt 2   -- l2
#guard checkBlockAt 3   -- l3
#guard checkBlockAt 4   -- l4

-- Full function type check
theorem enum_match_typechecks : check_fun_dec parsed_t0 t0_lenvDec enumEnv = true := by native_decide

end LeanMove.Tests.Expressivity.EnumMatch
