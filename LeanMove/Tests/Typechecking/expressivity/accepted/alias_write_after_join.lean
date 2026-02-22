/-
 Copyright Ilya Sergey

 Licensed under the Apache License, Version 2.0 (the "License");
 you may not use this file except in compliance with the License.
 You may obtain a copy of the License at

      https://www.apache.org/licenses/LICENSE-2.0

 Unless required by applicable law or agreed to in writing, software
 distributed under the License is distributed on an "AS IS" BASIS,
 WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 See the License for the specific language governing permissions and
 limitations under the License.
-/


import LeanMove.Lang.MoveLight
import LeanMove.Typing.TypeChecking
import LeanMove.Typing.Algorithmic.DecidableTypeEnv
import LeanMove.Lang.Macros
import LeanMove.Lang.MoveIR.PrettyPrint
import LeanMove.Tests.Parsing.TestUtils

/-!
# Alias Write After Join

Source: https://github.com/tnowacki/sui/blob/example-tests/external-crates/move/crates/bytecode-verifier-transactional-tests/tests/reference_safety/expressivity/alias_write_after_join.mvir

Original Move IR:
```
module 0x2.alias_after_join_reborrow {
  t(cond: bool) {
    let a: u64;
    let b: u64;
    let x: &mut u64;
    let y: &mut u64;
    let z: &mut u64;
  label l0:
    a = 0;
    b = 0;
    jump_if (move(cond)) l2;
  label l1:
    x = &mut a;
    y = &mut b;
    jump l3;
  label l2:
    x = &mut b;
    y = &mut a;
    jump l3;
  label l3:
    z = &mut a;
    *move(z) = 0;
    *move(x) = 0;
    *move(y) = 0;
    return;
  }
}
```

This test demonstrates that writing through aliased mutable references is safe
after control flow joins, because all writes release the reference.
-/

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Typing
open AssocMap
open Regex

namespace LeanMove.Tests.Expressivity.AliasWriteAfterJoin

-- Variables
def var_a : Var := ⟨"a"⟩
def var_b : Var := ⟨"b"⟩
def var_x : Var := ⟨"x"⟩
def var_y : Var := ⟨"y"⟩
def var_z : Var := ⟨"z"⟩
def var_cond : Var := ⟨"cond"⟩

-- Hand-written FunDef moved to Tests/Parsing/Test_alias_write_after_join.lean

-- -----------------------------------------------------
-- -           Parsed MVIR                             --
-- -----------------------------------------------------

open LeanMove.Tests.Parsing.TestUtils

private def aliasWriteAfterJoinMvir :=
  include_str "alias_write_after_join.mvir"

-- Verify that parsing the MVIR succeeds
#guard (parseAndTranslate aliasWriteAfterJoinMvir).isOk

private def parsedFuns := (parseAndTranslate aliasWriteAfterJoinMvir).toOption.get!

def parsed_t := (findFun parsedFuns "t").get!

-- Uncomment to pretty-print the parsed FunDef:
-- #eval IO.println (ppFunDef "t" parsed_t)

-- Abbreviations for path elements and refs
def rta : PathElement := .root_to_var var_a
def rtb : PathElement := .root_to_var var_b
def r1 : Aref := .refid 1
def r2 : Aref := .refid 2

-- -----------------------------------------------------
-- -           Algorithmic Type Checking Tests        --
-- -----------------------------------------------------

-- VarEnv at l1/l2 entry (after l0: a,b assigned, cond consumed)
def t_branch_varEnv : VarEnv :=
  let ve := init_fun_varEnv parsed_t
  let ve := update ve var_a (.validVar, .basic .u64, .mutable)
  let ve := update ve var_b (.validVar, .basic .u64, .mutable)
  update ve var_cond (.invalidVar, .basic .tbool, .mutable)

-- VarEnv at l3 entry (x and y now valid refs)
def t_l3_varEnv : VarEnv :=
  let ve := t_branch_varEnv
  let ve := update ve var_x (.validVar, .ref .u64 r1 .siteBorrowMut, .mutable)
  update ve var_y (.validVar, .ref .u64 r2 .siteBorrowMut, .mutable)

-- PathEnvDec at l3 entry (join of l1 and l2 with union paths)
def t_l3_pathEnvDec : PathEnvDec := {
  refs := [r2, r1, .root]
  paths :=
    insert (insert (insert (insert (insert (insert AssocMap.empty
      (.root, r1) ((.ε ⬝ ⌜rta⌝) ∣ (.ε ⬝ ⌜rtb⌝)))
      (.root, r2) ((.ε ⬝ ⌜rtb⌝) ∣ (.ε ⬝ ⌜rta⌝)))
      (r1, .root) ((∂[rta] .ε) ∣ (∂[rtb] .ε)))
      (r2, .root) ((∂[rtb] .ε) ∣ (∂[rta] .ε)))
      (r1, r2) (((∂[rta] .ε) ⬝ ⌜rtb⌝) ∣ ((∂[rtb] .ε) ⬝ ⌜rta⌝)))
      (r2, r1) ((∂[rtb] (.ε ⬝ ⌜rta⌝)) ∣ (∂[rta] (.ε ⬝ ⌜rtb⌝)))
}

-- Template for l3 environment (uses simple refids that get freshened)
private def t_l3_env_template : TypeEnvDec :=
  { siteEnv := AssocMap.empty, varEnv := t_l3_varEnv,
    pathEnv := t_l3_pathEnvDec, funEnv := AssocMap.empty }

-- Label environment (decidable)
-- freshenBlockEnv is applied uniformly; it is a no-op for l0/l1/l2 (no valid-var refids).
def t_lenvDec : LabelEnvDec :=
  let f := freshenBlockEnv parsed_t
  insert (insert (insert (insert AssocMap.empty
    "l0" (f (mkInitEnvDec parsed_t)))
    "l1" (f { siteEnv := AssocMap.empty, varEnv := t_branch_varEnv,
              pathEnv := .init, funEnv := AssocMap.empty }))
    "l2" (f { siteEnv := AssocMap.empty, varEnv := t_branch_varEnv,
              pathEnv := .init, funEnv := AssocMap.empty }))
    "l3" (f t_l3_env_template)

-- Theorem: t is well-typed (algorithmic)
theorem t_check : check_fun_dec parsed_t t_lenvDec = true := by native_decide

-- -----------------------------------------------------
-- -           Relational Type Checking Theorems      --
-- -----------------------------------------------------

-- Main theorem: t is well-typed (relational)
theorem t_welltyped : ∃ lenv, typecheck_fun parsed_t lenv :=
  ⟨_, check_fun_dec_sound _ _ t_check⟩

end LeanMove.Tests.Expressivity.AliasWriteAfterJoin
