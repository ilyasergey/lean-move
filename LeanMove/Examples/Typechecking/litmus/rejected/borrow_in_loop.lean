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

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Typing
open AssocMap

/-
https://github.com/MystenLabs/sui/blob/main/external-crates/move/crates/move-vm-transactional-tests/tests/references/borrow_in_loop.mvir

Original Move IR Program:

foo() {
    let x: u64;
    let r: &u64;
    label l0:
    x = 0;
    r = &x;
    jump l0;
}
-/

namespace LeanMove.Examples.BorrowInLoop

-- Variables
def var_x : Var := ⟨"x"⟩
def var_r : Var := ⟨"r"⟩

-- Sites (temporaries in A-normal form)
def s0 : Site := .site 0  -- constant 0
def s1 : Site := .site 1  -- &x

/-
  Function foo() translated to MoveLight AST:

  foo() {
      let x: u64;
      let r: &u64;
  label l0:
      x = 0;       // let s0 = 0; x = s0
      r = &x;      // let s1 = &x; r = s1
      jump l0;
  }
-/
def foo : FunDef := {
  params := []
  returnType := .basic .tunit
  locals := [
    { name := var_x, type := .basic .u64 },
    { name := var_r, type := .ref .u64 (.varRef var_x) .siteBorrowImm }
  ]
  blocks := [
    { label := "l0"
      body :=
        (letsite s0 ← #0) ;;       -- s0 = 0 (integer literal)
        (var_x ::= s0) ;;          -- x = s0
        (letsite s1 ← &var_x) ;;   -- s1 = &x
        (var_r ::= s1) ;;          -- r = s1
        jump "l0"                  -- jump l0 (terminal)
    }
  ]
}

/-!
## Why this is rejected

The loop back-edge (`jump l0`) requires the environment at `l0` to be subsumed by the
initial label environment. After executing the body, `r` holds a borrow of `x` — the
PathEnv has a non-empty path from `.root` through `x` to `r`'s reference. But the initial
environment at `l0` has `PathEnv.init` (no borrows). The post-body environment is **not**
subsumed by the initial one because of the extra borrow, so the `jump` check fails.

## Runtime behavior

The interpreter loops forever (exhausts fuel). There is no runtime safety violation —
the borrow is re-created each iteration and the old one is overwritten. The type checker
rejects it because it cannot prove the loop invariant is maintained.
-/

/- -----------------------------------------------------/
/- -           Type Checking Verification             --/
/- -----------------------------------------------------/

-- Initial environment for foo: no params, locals x and r are invalid
def foo_initEnv : TypeEnv := {
  siteEnv := AssocMap.empty
  varEnv := init_fun_varEnv foo
  pathEnv := PathEnv.init
  funEnv := AssocMap.empty
}

-- LabelEnv for foo: maps "l0" to the initial environment
def foo_lenv : LabelEnv :=
  AssocMap.insert AssocMap.empty "l0" foo_initEnv

-- Debug
#eval check_fun foo foo_lenv

-- Test: algorithmic checker rejects foo
#guard !check_fun foo foo_lenv

open Stmt

/-!
## Analysis: Why foo_welltyped Cannot Be Proven

This program fails type-checking due to a **borrow-checking violation** at the loop back-edge.

Trace through loop iterations:

**First iteration (entry with foo_initEnv):**
- `x` is invalid, `r` is invalid
- `pathEnv` has only root with ε self-edge

After `x = 0`:
- `x` becomes valid with type `.basic .u64`

After `let s1 = &x` (borrowImm):
- Creates immutable borrow, `s1 : &u64`
- **PathEnv updated**: adds edge from `root` to new ref `r1` via `[.root_to_var var_x]`
- This means `x` is now **borrowed** (reachable from root via var_x path)

After `r = s1`:
- `r` becomes valid, holding the reference
- The borrow edge remains in PathEnv

After `jump "l0"`:
- Must satisfy `TypeEnv.equiv env foo_initEnv`
- This requires the pathEnv to match `PathEnv.init`
- But our pathEnv has the borrow edge! **TypeEnv.equiv fails.**

**Second iteration attempt (hypothetically):**
Even if we tried a different `lenv` where the loop invariant includes the borrow:

After `x = 0` (second time):
- Rule `var_assign_valid` takes a **mutable** borrow via `borrowMut x`
- `t_uborrowMut_val` requires `not_borrowed x env` (TypeChecking.lean:303)
- But `r` still holds an immutable reference to `x`!
- `not_borrowed x env` checks that no path from root starts with `root_to_var x`
- The borrow edge violates this. **Mutable borrow fails.**

### Conclusion

The typing rules correctly reject this program. In Move/Rust semantics, you cannot:
1. Create a reference `r = &x`
2. Loop back and reassign `x = 0` while `r` is still live

The reference `r` must be released before `x` can be written again.

A corrected version would need to either:
- Release `r` before the jump: `release(s1); jump l0`
- Or not store the borrow across the back-edge

-/

-- Theorem: foo is ill-typed
-- Note: proving this formally requires the completeness theorem (check_fun_complete),
-- which is not yet fully proven. The algorithmic rejection above demonstrates the result.

-- theorem foo_illtyped : ¬ (∃ lenv, typecheck_fun foo lenv) := by
--   sorry


end LeanMove.Examples.BorrowInLoop
