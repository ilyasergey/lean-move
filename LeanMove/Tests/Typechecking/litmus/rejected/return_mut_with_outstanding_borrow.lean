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
import LeanMove.Typing.Algorithmic.AlgorithmicTypeChecking
import LeanMove.Typing.Algorithmic.DecidableTypeEnv
import LeanMove.Lang.Macros

/-!
# Return Mutable Ref with Outstanding Field Borrow — Rejected

This function takes a mutable reference to a record, borrows a field
(creating an immutable reference), and then tries to return the original
mutable reference while the field borrow is still alive.

Rejected by condition 3 of the `ret` rule (writability): the returned
mutable ref must have only trivial outbound paths to locally-created refs (.refid).
After `borrowField`, the pathEnv records `G(paramRef(p), r') = [.field x]`
where `r'` is the field borrow's aref (a .refid). This is a non-trivial outbound
path to a .refid ref, so the return is rejected.

This demonstrates **no flow from mutable to immutable reference upon return**:
a function cannot return a mutable ref while an outstanding immutable borrow
(derived from it) exists — doing so would allow the caller to mutate through
the returned ref while the immutable borrow is still conceptually alive.

```
fn_return_mut_with_field_borrow(p: &mut Point): &mut Point {
label b0:
    s0 = copy(p);              // s0: &mut Point (same aref as p)
    s1 = &s0.Point::x;         // s1: &u64, immutable field borrow
    s2 = move(p);              // s2: &mut Point (move p out)
    return s2;                  // REJECTED: G(paramRef(p), aref(s1)) = [.field x] ≠ {ε}
}
```
-/

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Typing
open AssocMap

namespace LeanMove.Tests.Litmus.ReturnMutWithOutstandingBorrow

-- Record type: Point { x: u64, y: u64 }
def field_x : Field := ⟨"x"⟩
def field_y : Field := ⟨"y"⟩
def point_entries : AssocMap Field BasicMoveType :=
  insert (insert empty field_x .u64) field_y .u64

-- Variables
def var_p : Var := ⟨"p"⟩

-- Sites
def s0 : Site := .site 0
def s1 : Site := .site 1
def s2 : Site := .site 2

/-
  fn_return_mut_with_field_borrow(p: &mut Point): &mut Point
  Borrows a field of p, then tries to return p — should be rejected.
-/
def fn_return_mut_with_field_borrow : FunDef := {
  params := [(var_p, .ref (.trecord point_entries) (.paramRef var_p) .siteBorrowMut)]
  returnType := [⟨.trecord point_entries, some true⟩]
  locals := []
  blocks := [
    { label := "b0"
      body :=
        (letsite s0 ← copy var_p) ;;                                          -- s0 = copy(p)
        Stmt.letBind s1 (Expr.borrowField s0 (.trecord point_entries) field_x) ;; -- s1 = &s0.x
        (letsite s2 ← move var_p) ;;                                          -- s2 = move(p)
        Stmt.ret [s2]                                                           -- REJECTED
    }
  ]
}

def fn_lenv := mkLabelEnv fn_return_mut_with_field_borrow

-- The algorithmic checker rejects this
#guard !check_fun fn_return_mut_with_field_borrow fn_lenv

end LeanMove.Tests.Litmus.ReturnMutWithOutstandingBorrow
