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

import Ssreflect.Lang

import LeanMove.Lang.MoveLight
import LeanMove.Checker.TypeChecking
import LeanMove.Lang.Macros

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
open LeanMove.Checker
open AssocMap
open Regex

namespace LeanMove.Examples.Expressivity.AliasWriteAfterJoin

-- Variables
def var_a : Var := ⟨"a"⟩
def var_b : Var := ⟨"b"⟩
def var_x : Var := ⟨"x"⟩
def var_y : Var := ⟨"y"⟩
def var_z : Var := ⟨"z"⟩
def var_cond : Var := ⟨"cond"⟩

-- Sites (temporaries in A-normal form)
def s0 : Site := .site 0   -- integer literal 0 for a
def s1 : Site := .site 1   -- integer literal 0 for b
def s2 : Site := .site 2   -- move(cond)
def s3 : Site := .site 3   -- &mut a or &mut b (for x)
def s4 : Site := .site 4   -- &mut b or &mut a (for y)
def s5 : Site := .site 5   -- &mut a (for z)
def s6 : Site := .site 6   -- move(z)
def s7 : Site := .site 7   -- integer literal 0 for first write
def s8 : Site := .site 8   -- move(x)
def s9 : Site := .site 9   -- integer literal 0 for second write
def s10 : Site := .site 10 -- move(y)
def s11 : Site := .site 11 -- integer literal 0 for third write

/-
  Function t(cond: bool) translated to MoveLight AST
-/
def t : FunDef := {
  params := [(var_cond, .basic .tbool)]
  returnType := .basic .tunit
  locals := [
    { name := var_a, type := .basic .u64 },
    { name := var_b, type := .basic .u64 },
    { name := var_x, type := .ref .u64 (.varRef var_a) .siteBorrowMut },
    { name := var_y, type := .ref .u64 (.varRef var_b) .siteBorrowMut },
    { name := var_z, type := .ref .u64 (.varRef var_a) .siteBorrowMut }
  ]
  blocks := [
    -- label l0: a = 0; b = 0; branch on cond
    { label := "l0"
      body :=
        (letsite s0 ← #0) ;;            -- s0 = 0 (integer literal)
        (var_a ::= s0) ;;               -- a = s0
        (letsite s1 ← #0) ;;            -- s1 = 0 (integer literal)
        (var_b ::= s1) ;;               -- b = s1
        (letsite s2 ← move var_cond)    -- s2 = move(cond)
      terminator := Terminator.branch s2 "l2" "l1"
    },
    -- label l1 (false branch): x = &mut a; y = &mut b; jump l3
    { label := "l1"
      body :=
        (letsite s3 ← &mut var_a) ;;    -- s3 = &mut a
        (var_x ::= s3) ;;               -- x = s3
        (letsite s4 ← &mut var_b) ;;    -- s4 = &mut b
        (var_y ::= s4)                  -- y = s4
      terminator := Terminator.jump "l3"
    },
    -- label l2 (true branch): x = &mut b; y = &mut a; jump l3
    { label := "l2"
      body :=
        (letsite s3 ← &mut var_b) ;;    -- s3 = &mut b
        (var_x ::= s3) ;;               -- x = s3
        (letsite s4 ← &mut var_a) ;;    -- s4 = &mut a
        (var_y ::= s4)                  -- y = s4
      terminator := Terminator.jump "l3"
    },
    -- label l3: z = &mut a; writes; return
    { label := "l3"
      body :=
        (letsite s5 ← &mut var_a) ;;    -- s5 = &mut a
        (var_z ::= s5) ;;               -- z = s5
        (letsite s6 ← move var_z) ;;    -- s6 = move(z)
        (letsite s7 ← #0) ;;            -- s7 = 0 (integer literal)
        Stmt.writeRef s6 s7 ;;          -- *s6 = s7
        (letsite s8 ← move var_x) ;;    -- s8 = move(x)
        (letsite s9 ← #0) ;;            -- s9 = 0 (integer literal)
        Stmt.writeRef s8 s9 ;;          -- *s8 = s9
        (letsite s10 ← move var_y) ;;   -- s10 = move(y)
        (letsite s11 ← #0) ;;           -- s11 = 0 (integer literal)
        Stmt.writeRef s10 s11           -- *s10 = s11
      terminator := Terminator.ret []   -- return
    }
  ]
}

-- Theorem: t is well-typed
theorem t_welltyped : ∃ lenv, typecheck_fun t lenv := by
  sorry

end LeanMove.Examples.Expressivity.AliasWriteAfterJoin
