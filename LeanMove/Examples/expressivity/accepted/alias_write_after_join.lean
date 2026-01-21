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
import LeanMove.Examples.Macros

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
    jump_if (copy(cond)) l2;
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
    *copy(z) = 0;
    *copy(x) = 0;
    *copy(y) = 0;
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
def s0 : Site := .site 0   -- constant 0
def s1 : Site := .site 1   -- copy(cond)
def s2 : Site := .site 2   -- &mut a or &mut b
def s3 : Site := .site 3   -- &mut b or &mut a
def s4 : Site := .site 4   -- &mut a (for z)
def s5 : Site := .site 5   -- copy(z)
def s6 : Site := .site 6   -- constant 0 for write
def s7 : Site := .site 7   -- copy(x)
def s8 : Site := .site 8   -- constant 0 for write
def s9 : Site := .site 9   -- copy(y)
def s10 : Site := .site 10 -- constant 0 for write

/-
  Function t(cond: bool) translated to MoveLight AST
-/
def t : FunDef := {
  params := [(var_cond, .basic .tbool)]
  returnType := .basic .tunit
  locals := [
    { name := var_a, type := .basic .tint },
    { name := var_b, type := .basic .tint },
    { name := var_x, type := .ref .tint (.varRef var_a) .siteBorrowMut },
    { name := var_y, type := .ref .tint (.varRef var_b) .siteBorrowMut },
    { name := var_z, type := .ref .tint (.varRef var_a) .siteBorrowMut }
  ]
  blocks := [
    -- label l0: a = 0; b = 0; branch on cond
    { label := "l0"
      body :=
        (var_a ::= s0) ;;               -- a = 0
        (var_b ::= s0) ;;               -- b = 0
        (letsite s1 ← copy var_cond) ;; -- s1 = copy(cond)
        Stmt.branch s1 "l2" "l1"        -- if s1 then l2 else l1
    },
    -- label l1 (false branch): x = &mut a; y = &mut b; jump l3
    { label := "l1"
      body :=
        (letsite s2 ← &mut var_a) ;;    -- s2 = &mut a
        (var_x ::= s2) ;;               -- x = s2
        (letsite s3 ← &mut var_b) ;;    -- s3 = &mut b
        (var_y ::= s3) ;;               -- y = s3
        jump "l3"
    },
    -- label l2 (true branch): x = &mut b; y = &mut a; jump l3
    { label := "l2"
      body :=
        (letsite s2 ← &mut var_b) ;;    -- s2 = &mut b
        (var_x ::= s2) ;;               -- x = s2
        (letsite s3 ← &mut var_a) ;;    -- s3 = &mut a
        (var_y ::= s3) ;;               -- y = s3
        jump "l3"
    },
    -- label l3: z = &mut a; writes; return
    { label := "l3"
      body :=
        (letsite s4 ← &mut var_a) ;;    -- s4 = &mut a
        (var_z ::= s4) ;;               -- z = s4
        (letsite s5 ← copy var_z) ;;    -- s5 = copy(z)
        Stmt.writeRef s5 s6 ;;          -- *s5 = 0
        (letsite s7 ← copy var_x) ;;    -- s7 = copy(x)
        Stmt.writeRef s7 s8 ;;          -- *s7 = 0
        (letsite s9 ← copy var_y) ;;    -- s9 = copy(y)
        Stmt.writeRef s9 s10 ;;         -- *s9 = 0
        Stmt.ret []                     -- return
    }
  ]
}

-- Theorem: t is well-typed
theorem t_welltyped : ∃ lenv, typecheck_fun t lenv := by
  sorry

end LeanMove.Examples.Expressivity.AliasWriteAfterJoin
