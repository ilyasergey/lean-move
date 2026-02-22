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

-- Sites
def s0 : Site := .site 0
def s1 : Site := .site 1
def s2 : Site := .site 2
def s3 : Site := .site 3
def s4 : Site := .site 4
def s5 : Site := .site 5
def s6 : Site := .site 6
def s7 : Site := .site 7
def s8 : Site := .site 8
def s9 : Site := .site 9
def s10 : Site := .site 10
def s11 : Site := .site 11
def s12 : Site := .site 12 -- move(y) for return
def s13 : Site := .site 13 -- integer literal 0 for write

def t : FunDef := {
  params := [
    (var_cond, .basic .tbool),
    (var_a, .ref (.trecord s_entries) (.varRef (Var.mk "a")) .siteBorrowMut),
    (var_b, .ref (.trecord s_entries) (.varRef (Var.mk "b")) .siteBorrowMut)
  ]
  returnType := [⟨.trecord s_entries, some true⟩]
  locals := [
    { name := var_x, type := .ref (.trecord s_entries) (.refid 1) .siteBorrowMut },
    { name := var_y, type := .ref (.trecord s_entries) (.refid 2) .siteBorrowMut },
    { name := var_f, type := .ref .u64 (.refid 3) .siteBorrowMut }
  ]
  blocks := [
    -- l0: jump_if (move(cond)) l2;
    { label := "l0"
      body :=
        (letsite s0 ← move var_cond) ;;  -- s0 = move(cond)
        branch s0 "l2" "l1"              -- if s0 then l2 else l1
    },
    -- l1 (false branch): x = move(a); y = move(b); jump l3;
    { label := "l1"
      body :=
        (letsite s1 ← move var_a) ;;     -- s1 = move(a)
        (var_x ::= s1) ;;                -- x = s1
        (letsite s2 ← move var_b) ;;     -- s2 = move(b)
        (var_y ::= s2) ;;                -- y = s2
        jump "l3"
    },
    -- l2 (true branch): x = move(b); y = move(a); jump l3;
    { label := "l2"
      body :=
        (letsite s3 ← move var_b) ;;     -- s3 = move(b)
        (var_x ::= s3) ;;                -- x = s3
        (letsite s4 ← move var_a) ;;     -- s4 = move(a)
        (var_y ::= s4) ;;                -- y = s4
        jump "l3"
    },
    -- l3: f = &mut copy(x).S::f; *copy(y) = S { f: *copy(f) }; *copy(f) = 0; return move(y);
    { label := "l3"
      body :=
        -- f = &mut copy(x).S::f
        (letsite s5 ← copy var_x) ;;
        (letsite s6 ← borrowMutField(s5, .trecord s_entries, field_f)) ;;
        (var_f ::= s6) ;;
        -- *copy(y) = S { f: *copy(f) }
        -- First read *copy(f), then pack into S, then write to *copy(y)
        (letsite s7 ← copy var_f) ;;
        (letsite s8 ← *s7) ;;                             -- s8 = *s7 (the value in f)
        (letsite s9 ← pack("S", [(field_f, s8)])) ;;     -- s9 = S { f: s8 }
        (letsite s10 ← copy var_y) ;;
        (*s10 ::= s9) ;;                                  -- *s10 = s9 (write struct to y)
        -- *copy(f) = 0
        (letsite s11 ← copy var_f) ;;
        (letsite s13 ← #0) ;;                             -- s13 = 0 (integer literal)
        (*s11 ::= s13) ;;                                 -- *s11 = s13
        -- return move(y)
        (letsite s12 ← move var_y) ;;
        ret [s12]
    }
  ]
}

-- -----------------------------------------------------
-- -           Decidable Type Checking                --
-- -----------------------------------------------------

-- VarEnv at l1/l2 entry (after l0: cond consumed)
def t_branch_varEnv : VarEnv :=
  let ve := init_fun_varEnv t
  update ve var_cond (.invalidVar, .basic .tbool, .mutable)

-- VarEnv at l3 entry (a,b moved/invalid, x,y valid)
-- Order of updates must match checker's execution in l1: move a, assign x, move b, assign y
def t_l3_varEnv : VarEnv :=
  let ve := t_branch_varEnv
  let ve := update ve var_a (.invalidVar, .ref (.trecord s_entries) ((.refid 4)) .siteBorrowMut, .mutable)
  let ve := update ve var_x (.validVar, .ref (.trecord s_entries) (.refid 1) .siteBorrowMut, .mutable)
  let ve := update ve var_b (.invalidVar, .ref (.trecord s_entries) (.refid 5) .siteBorrowMut, .mutable)
  update ve var_y (.validVar, .ref (.trecord s_entries) (.refid 305) .siteBorrowMut, .mutable)

-- PathEnvDec at l3: must track .refid refs from both branches
def t_l3_pathEnvDec : PathEnvDec := {
  refs := [.root, .refid 1, .refid 305]
  paths := .empty
}

-- Label environment (decidable)
def t_lenvDec : LabelEnvDec :=
  insert (insert (insert (insert AssocMap.empty
    "l0" { siteEnv := AssocMap.empty, varEnv := init_fun_varEnv t,
           pathEnv := init_fun_pathEnvDec t.params, funEnv := AssocMap.empty })
    "l1" { siteEnv := AssocMap.empty, varEnv := t_branch_varEnv,
           pathEnv := init_fun_pathEnvDec t.params, funEnv := AssocMap.empty })
    "l2" { siteEnv := AssocMap.empty, varEnv := t_branch_varEnv,
           pathEnv := init_fun_pathEnvDec t.params, funEnv := AssocMap.empty })
    "l3" { siteEnv := AssocMap.empty, varEnv := t_l3_varEnv,
           pathEnv := t_l3_pathEnvDec, funEnv := AssocMap.empty }

-- Theorem: t is well-typed (algorithmic, decidable)
theorem t_check : check_fun_dec t t_lenvDec = true := by rfl

-- Main theorem: t is well-typed (relational)
theorem t_welltyped : ∃ lenv, typecheck_fun t lenv :=
  ⟨_, check_fun_dec_sound _ _ t_check⟩

end LeanMove.Tests.Expressivity.ExtensionWritesAfterJoin
