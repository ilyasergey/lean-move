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
import LeanMove.Lang.Macros

/-!
# Return Local Borrow — Rejected

This function borrows a local variable and attempts to return the borrow.
It should be rejected by condition 2 of the `ret` rule: "no local borrowing".

```
fn_return_local_borrow(): &mut u64 {
    let a: u64;
    let r: &mut u64;
label b0:
    a = 42;
    r = &mut a;
    return move(r);   // REJECTED: r borrows local a, so G(root, varRef(r)) ≠ ∅
}
```

After `r = &mut a`, the pathEnv has:
- G(root, varRef(a)) = root_to_var "a"
- G(varRef(a), varRef(r)) = ε  (or similar extension)
- So G(root, varRef(r)) contains paths via root → a → r

The return of `move(r)` is rejected because the returned ref's aref
has a non-empty path from `.root`, violating "no local borrowing".
-/

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Typing
open AssocMap

namespace LeanMove.Examples.Litmus.ReturnLocalBorrow

-- Variables
def var_a : Var := ⟨"a"⟩
def var_r : Var := ⟨"r"⟩

-- Sites
def s0 : Site := .site 0
def s1 : Site := .site 1
def s2 : Site := .site 2

/-
  fn_return_local_borrow(): &mut u64
  Borrows local and returns the borrow — should be rejected.
-/
def fn_return_local_borrow : FunDef := {
  params := []
  returnType := [⟨.u64, some true⟩]
  locals := [
    { name := var_a, type := .basic .u64 },
    { name := var_r, type := .ref .u64 (.refid 0) .siteBorrowMut }
  ]
  blocks := [
    { label := "b0"
      body :=
        (letsite s0 ← #42) ;;
        (var_a ::= s0) ;;
        (letsite s1 ← &mut var_a) ;;
        (var_r ::= s1) ;;
        (letsite s2 ← move var_r) ;;
        ret [s2]
    }
  ]
}

def fn_return_local_borrow_initEnv : TypeEnv := {
  siteEnv := empty
  varEnv := init_fun_varEnv fn_return_local_borrow
  pathEnv := PathEnv.init
  funEnv := empty
}

def fn_return_local_borrow_lenv : LabelEnv :=
  insert empty "b0" fn_return_local_borrow_initEnv

-- The algorithmic checker rejects this
#guard !check_fun fn_return_local_borrow fn_return_local_borrow_lenv

end LeanMove.Examples.Litmus.ReturnLocalBorrow
