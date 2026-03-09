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
import LeanMove.Typing.Algorithmic.DecidableTypeEnv
import LeanMove.Lang.Macros
import LeanMove.Lang.MoveIR.PrettyPrint
import LeanMove.Tests.Parsing.TestUtils

/-!
# Extension Writes After Join

Source: https://github.com/tnowacki/sui/blob/example-tests/external-crates/move/crates/bytecode-verifier-transactional-tests/tests/reference_safety/expressivity/extension_writes_after_join.mvir

This module demonstrates writing to extensions after a control flow join.

Original Move IR:
```
module 0x2.extension_after_join {

struct S has copy, drop, store { f: u64 }

t(cond: bool, a: &mut Self.S, b: &mut Self.S): &mut Self.S {
    let x: &mut Self.S;
    let y: &mut Self.S;
    let f: &mut u64;
label l0:
    jump_if (move(cond)) l2;
label l1:
    x = move(a);
    y = move(b);
    jump l3;
label l2:
    x = move(b);
    y = move(a);
    jump l3;
label l3:
    f = &mut copy(x).S::f;
    *copy(y) = S { f: *copy(f) };
    *copy(f) = 0;
    return move(y);
}

}
```

The algorithmic checker uses lookup-based (order-independent) AssocMap equivalence
to compare VarEnvs at jump targets. This allows l1 and l2 to perform moves in
different orders while still passing the subsumption check at `jump l3`.
-/

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Typing
open AssocMap
open Regex

namespace LeanMove.Tests.Expressivity.ExtensionWritesAfterJoin

-- Field for S struct
def field_f : Field := ⟨"f"⟩

-- S { f: u64 }
def s_entries : AssocMap Field BasicMoveType := insert empty field_f .u64

-- Variables
def var_cond : Var := ⟨"cond"⟩
def var_a : Var := ⟨"a"⟩
def var_b : Var := ⟨"b"⟩
def var_x : Var := ⟨"x"⟩
def var_y : Var := ⟨"y"⟩
def var_f : Var := ⟨"f"⟩

-- Hand-written FunDef moved to Tests/Parsing/Test_extension_writes_after_join.lean

-- -----------------------------------------------------
-- -           Parsed MVIR                             --
-- -----------------------------------------------------

open LeanMove.Tests.Parsing.TestUtils

private def extensionWritesAfterJoinMvir :=
  include_str "extension_writes_after_join.mvir"

-- Verify that parsing the MVIR succeeds
#guard (parseAndTranslate extensionWritesAfterJoinMvir).isOk

private def parsedFuns := (parseAndTranslate extensionWritesAfterJoinMvir).toOption.get!

def parsed_t := (findFun parsedFuns "t").get!

-- Uncomment to pretty-print the parsed FunDef:
-- #eval IO.println (ppFunDef "t" parsed_t)

-- -----------------------------------------------------
-- -           Decidable Type Checking                --
-- -----------------------------------------------------

-- VarEnv at l1/l2 entry (after l0: cond consumed)
def t_branch_varEnv : VarEnv :=
  let ve := init_fun_varEnv parsed_t
  update ve var_cond (.invalidVar, .basic .tbool, .mutable)

-- VarEnv at l3 entry (a,b moved/invalid, x,y valid)
-- Template refids: simple sequential values, freshened by freshenBlockEnv
def t_l3_varEnv : VarEnv :=
  let ve := t_branch_varEnv
  let ve := update ve var_a (.invalidVar, .ref (.trecord s_entries) (.refid 60) .siteBorrowMut, .mutable)
  let ve := update ve var_x (.validVar, .ref (.trecord s_entries) (.refid 1) .siteBorrowMut, .mutable)
  let ve := update ve var_b (.invalidVar, .ref (.trecord s_entries) (.refid 50) .siteBorrowMut, .mutable)
  update ve var_y (.validVar, .ref (.trecord s_entries) (.refid 2) .siteBorrowMut, .mutable)

-- PathEnvDec at l3: tracks refs for valid vars x and y
def t_l3_pathEnvDec : PathEnvDec := {
  refs := [.root, .refid 1, .refid 2]
  paths := .empty
}

-- Template for l3 environment (uses simple refids that get freshened)
private def t_l3_env_template : TypeEnvDec :=
  { siteEnv := AssocMap.empty, varEnv := t_l3_varEnv,
    pathEnv := t_l3_pathEnvDec, funEnv := AssocMap.empty }

-- Label environment (decidable)
--
-- `freshenBlockEnv` is applied uniformly to all block entries. It is a no-op for
-- environments derived from the function signature (l0, l1, l2), where all
-- refid-bearing vars are still uninitialized. It only freshens template placeholder
-- refids in hand-crafted join-point environments (l3), shifting them above
-- `maxFunDefRefId` so the subsumption σ-matching works.
--
-- l0: Entry block — initial TypeEnv from params and locals.
-- l1, l2: Branch targets — cond consumed, a/b/x/y/f unchanged, param refs only.
-- l3: Join point — template refids 1, 2 for valid vars x, y get freshened.
def t_lenvDec : LabelEnvDec :=
  let f := freshenBlockEnv parsed_t
  insert (insert (insert (insert AssocMap.empty
    "l0" (f (mkInitEnvDec parsed_t)))
    "l1" (f { siteEnv := AssocMap.empty, varEnv := t_branch_varEnv,
              pathEnv := init_fun_pathEnvDec parsed_t.params, funEnv := AssocMap.empty }))
    "l2" (f { siteEnv := AssocMap.empty, varEnv := t_branch_varEnv,
              pathEnv := init_fun_pathEnvDec parsed_t.params, funEnv := AssocMap.empty }))
    "l3" (f t_l3_env_template)

-- Theorem: t is well-typed (algorithmic, decidable)
theorem t_check : check_fun_dec parsed_t t_lenvDec = true := by native_decide

-- Main theorem: t is well-typed (relational)
theorem t_welltyped : ∃ lenv, typecheck_fun parsed_t lenv AssocMap.empty :=
  ⟨_, check_fun_dec_sound _ _ _ t_check⟩

end LeanMove.Tests.Expressivity.ExtensionWritesAfterJoin
