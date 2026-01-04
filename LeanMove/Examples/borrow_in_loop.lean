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

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Checker
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
    { name := var_x, type := .basic .tint },
    { name := var_r, type := .ref .tint (.varRef var_x) .siteBorrowImm }
  ]
  blocks := [
    { label := "l0"
      body :=
        -- x = 0 (in A-normal form: assign from a site holding constant)
        .seq (.assign var_x s0)
        -- r = &x
        (.seq (.letBind s1 (.usage (.borrowImm var_x)))
        (.seq (.assign var_r s1)
        -- jump l0
        (.jump "l0")))
    }
  ]
}

/- -----------------------------------------------------/
/- -           Type Checking Verification             --/
/- -----------------------------------------------------/

-- Initial environment for foo: no params, locals x and r are invalid
def foo_initEnv : TypeEnv := {
  siteEnv := AssocMap.empty
  varEnv := add_locals_to_varEnv AssocMap.empty foo.locals
  pathEnv := PathEnv.init
  funEnv := AssocMap.empty
}

-- LabelEnv for foo: maps "l0" to the initial environment
def foo_lenv : LabelEnv :=
  AssocMap.insert AssocMap.empty "l0" foo_initEnv

open Stmt

/-!
## Analysis: Why foo_welltyped Cannot Be Proven

This program has **two fundamental issues** that prevent it from type-checking:

### Issue 1: Missing Site Initialization

The program uses `assign var_x s0` but `s0` is never introduced into the `siteEnv`.
In A-normal form, the assignment `x = 0` should be translated as:
```
let s0 = <constant 0>   -- introduces s0 into siteEnv
x = s0                   -- consumes s0
```
However, the current AST only has the second statement. The typing rule
`var_assign_invalid` (TypeChecking.lean:659-664) requires:
```
AssocMap.lookup env.siteEnv a = some τ
```
Since `s0` is never bound, this lookup fails.

### Issue 2: Borrow-Checking Violation in Loop

Even if Issue 1 were fixed (e.g., by adding a constant expression form), the program
would still fail to type-check due to a **borrow-checking violation**.

Trace through loop iterations:

**First iteration (entry with foo_initEnv):**
- `x` is invalid, `r` is invalid
- `pathEnv` has only root with ε self-edge

After `x = 0`:
- `x` becomes valid with type `.basic .tint`

After `let s1 = &x` (borrowImm):
- Creates immutable borrow, `s1 : &tint`
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

-- Theorem: foo is well-typed
-- NOTE: This theorem is FALSE - the program has borrow-checking violations.
-- We document exactly where the proof gets stuck.
theorem foo_welltyped : ∃ lenv, typecheck_fun foo lenv := by
  exists foo_lenv
  apply typecheck_fun.fun_ok (initEnv := foo_initEnv)
  all_goals try aesop
  { unfold foo at a; aesop }
  {
    move: a=>//=
    scase: (foo.blocks.head?) =>//=[] l b
    scase
    srw foo_lenv at a_1
    move: (lookup_some _ _ _ a_1)=>//=
    srw foo_initEnv=>//=
    simp [AssocMap.insert]; scase=>//
    scase
    sby simp [empty]
  }
  {
    -- The actual type-checking of the block body
    scase: idx a a_1=>//=
    dsimp [foo] at * =>//==<- {block}=>//=
    srw foo_lenv foo_initEnv=>//= /lookup_some=>//=
    simp [AssocMap.insert]=>->

    /-
    Goal state at this point:
    We need to find an `outEnv` such that:
      typecheck_block foo_lenv block foo_initEnv outEnv

    The block body is:
      seq (assign var_x s0)
          (seq (letBind s1 (usage (borrowImm var_x)))
               (seq (assign var_r s1)
                    (jump "l0")))

    To prove this, we would apply `typecheck_stmt.seq` repeatedly.

    STUCK POINT 1: First statement `assign var_x s0`
    ------------------------------------------------
    For `var_assign_invalid` (since x starts invalid):
      - Need: lookup foo_initEnv.siteEnv s0 = some (.basic .tint)
      - But: foo_initEnv.siteEnv = empty
      - Therefore: lookup returns none
      - PROOF FAILS HERE

    Even if we had s0 in siteEnv, we would eventually hit:

    STUCK POINT 2: The `jump "l0"` statement
    ----------------------------------------
    For `typecheck_stmt.jump`:
      - Need: TypeEnv.equiv currentEnv foo_initEnv
      - But after borrowImm, pathEnv has edge: root --[var_x]--> r
      - foo_initEnv.pathEnv = PathEnv.init (no such edge)
      - pathEnv.paths don't match
      - TypeEnv.equiv fails
      - PROOF WOULD FAIL HERE

    No choice of outEnv can satisfy both the typing rules and
    the jump's environment equivalence requirement.
    -/

    sorry
  }
  { sdone }

/-!
## Alternative: What Would Make This Program Type-Check?

For this loop pattern to work, we would need one of:

1. **Release the borrow before jumping:**
   ```
   label l0:
     x = 0;
     let s1 = &x;
     r = s1;
     release(r);  -- or use r before loop back
     jump l0;
   ```

2. **Different loop invariant:**
   Use a `lenv` where the entry environment already accounts for the borrow.
   But then the first iteration (with x invalid) wouldn't match.

3. **Weaker typing rules:**
   Allow environments to be "compatible" rather than "equivalent" at jumps.
   This would require subtyping/weakening on PathEnv.
   Current rules are intentionally strict for soundness.

The current typing rules are designed to be **sound**: they never accept
programs with use-after-free or dangling reference errors. This program
genuinely has such an error (writing to x while r references it), so
rejection is correct behavior.
-/

end LeanMove.Examples.BorrowInLoop
