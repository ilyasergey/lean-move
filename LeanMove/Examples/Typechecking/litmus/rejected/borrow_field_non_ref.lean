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
import LeanMove.Typing.Algorithmic.TypeCheckingAlgorithmic
import LeanMove.Typing.Algorithmic.AlgorithmicTypingSoundness
import LeanMove.Lang.Macros

/-!
# BorrowField on Non-Reference — Runtime Litmus Test

Demonstrates that the type checker prevents borrowing a field from a non-reference.
Applying `borrowField` to a record value (instead of a reference to a record) is
rejected by the type checker and produces `typeMismatch` at runtime.

Original Move-like pseudocode:
```
foo() {
    let x: S;          // S = { f: u64 }
    let f_ref: &u64;
label b0:
    x = S { f: 42 };
    f_ref = &copy(x).S::f;   // ERROR: copy(x) is a record, not a ref
    return;
}
```
-/

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Typing
open AssocMap
open Regex

namespace LeanMove.Examples.BorrowFieldNonRef

-- Fields
def field_f : Field := ⟨"f"⟩

-- S { f: u64 }
def s_entries : AssocMap Field BasicMoveType := insert empty field_f .u64

-- Variables
def var_x : Var := ⟨"x"⟩
def var_f_ref : Var := ⟨"f_ref"⟩

-- Sites
def s0 : Site := .site 0   -- integer literal 42
def s1 : Site := .site 1   -- pack S { f: s0 }
def s2 : Site := .site 2   -- copy(x) — a record value, not a ref
def s3 : Site := .site 3   -- borrowField s2 — ERROR

def foo : FunDef := {
  params := []
  returnType := .basic .tunit
  locals := [
    { name := var_x, type := .basic (.trecord s_entries) },
    { name := var_f_ref, type := .ref .u64 (.varRef var_x) .siteBorrowImm }
  ]
  blocks := [
    { label := "b0"
      body :=
        -- x = S { f: 42 }
        (letsite s0 ← #42) ;;
        Stmt.letBind s1 (Expr.pack "S" [(field_f, s0)]) ;;
        (var_x ::= s1) ;;
        -- f_ref = &copy(x).S::f — ERROR: copy(x) is a record, not a reference
        (letsite s2 ← copy var_x) ;;
        Stmt.letBind s3 (Expr.borrowField s2 (.trecord s_entries) field_f) ;;
        (var_f_ref ::= s3) ;;
        Stmt.ret []
    }
  ]
}

/-!
## Why this is rejected by the type checker

The `borrowField` expression requires its source site to have a reference type (`.ref ...`).
Since `copy(x)` produces a site with type `.basic (.trecord s_entries)` (a record *value*,
not a reference *to* a record), the checker rejects the borrow.

To correctly borrow a field, one must first create a reference: `&mut x` or `&x`,
then borrow the field from that reference.

## Why this fails at runtime

At runtime, `s2` holds `Value.record [("f", int 42)]`. The `borrowField` case in the
step function pattern-matches for `Value.ref loc path` and falls through to the catch-all,
producing `typeMismatch "borrowField on non-ref"`.
-/

-- -----------------------------------------------------
-- -           Algorithmic Type Checking Tests        --
-- -----------------------------------------------------

def foo_initEnv : TypeEnv := {
  siteEnv := AssocMap.empty
  varEnv := init_fun_varEnv foo
  pathEnv := PathEnv.init
  funEnv := AssocMap.empty
}

def foo_lenv : LabelEnv :=
  AssocMap.insert AssocMap.empty "b0" foo_initEnv

#eval check_fun foo foo_lenv

#guard !check_fun foo foo_lenv

end LeanMove.Examples.BorrowFieldNonRef
