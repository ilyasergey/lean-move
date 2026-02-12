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
import LeanMove.Typing.TypeChecking
import LeanMove.Typing.Algorithmic.TypeCheckingAlgorithmic
import LeanMove.Lang.Macros

/-!
# Fixed Version of borrow_in_loop

See: `borrow_in_loop.lean` for the broken version and detailed analysis of why it fails.

This file demonstrates the corrected version of the program. The original program
failed to type-check because it kept a borrow alive across a loop back-edge while
trying to reassign the borrowed variable.

The fix: **release the borrow before jumping back**.

## Original (broken) program from borrow_in_loop.lean:
```
foo() {
    let x: u64;
    let r: &u64;
    label l0:
    x = 0;
    r = &x;      // borrow created
    jump l0;     // borrow still live! Cannot reassign x on next iteration
}
```

## Fixed program (this file):
```
foo(x: u64) {
label l0:
    let s0 = &x;   // borrow x
    release(s0);   // release borrow immediately
    jump l0;       // x is no longer borrowed, loop can continue
}
```

Key differences:
1. We use `x` as a parameter (starting valid) since MoveLight lacks constant expressions
2. We release the borrow before jumping back, restoring the PathEnv to its initial state
3. The simplified version doesn't assign to a local variable `r` to avoid Aref mismatch issues

The proof demonstrates that `release` removes the reference from PathEnv via
`delete_ref_node`, which allows `TypeEnv.subsumes` to succeed at the back-edge.
-/

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Typing
open AssocMap
open Regex

namespace LeanMove.Examples.BorrowInLoopFixed

-- Variables
def var_x : Var := ⟨"x"⟩
def var_r : Var := ⟨"r"⟩

-- Sites (temporaries in A-normal form)
def s0 : Site := .site 0  -- &x
def s1 : Site := .site 1  -- move(r) for release

/-
  Function foo(x: u64) translated to MoveLight AST:

  Simplified version: borrow x, immediately release, then loop.
  We don't assign to r to avoid the Aref mismatch issue.

  foo(x: u64) {
  label l0:
      let s0 = &x;     // borrow x
      release(s0);     // immediately release
      jump l0;
  }
-/
def foo : FunDef := {
  params := [(var_x, .basic .u64)]  -- x is a parameter, starts valid
  returnType := .basic .tunit
  locals := []  -- no locals needed for this simplified version
  blocks := [
    { label := "l0"
      body :=
        (letsite s0 ← &var_x) ;;  -- let s0 = &x
        (release s0) ;;           -- release(s0)
        jump "l0"                 -- jump l0 (terminal)
    }
  ]
}

/- -----------------------------------------------------/
/- -           Type Checking Verification             --/
/- -----------------------------------------------------/

-- Initial environment for foo: parameter x is valid, no locals
def foo_initEnv : TypeEnv := {
  siteEnv := AssocMap.empty
  varEnv := init_varEnv_from_params [(var_x, .basic .u64)]
  pathEnv := PathEnv.init
  funEnv := AssocMap.empty
}

-- LabelEnv for foo: maps "l0" to the initial environment
def foo_lenv : LabelEnv :=
  AssocMap.insert AssocMap.empty "l0" foo_initEnv

open Stmt

/-!
## Intermediate Environments

To prove the block type-checks, we need to trace through each statement
and construct the intermediate type environments.

For the simplified program:
  let s0 = &x;
  release(s0);
  jump l0;
-/

-- Fresh abstract reference for the borrow
def r0 : Aref := .refid 0

-- Environment after `let s0 = &x`
-- s0 holds an immutable reference to x
-- PathEnv has edge: root --[var_x]--> r0
def env_after_borrow : TypeEnv := {
  siteEnv := AssocMap.insert AssocMap.empty s0 (.ref .u64 r0 .siteBorrowImm)
  varEnv := foo_initEnv.varEnv  -- unchanged
  pathEnv := {
    refs := [r0, .root]
    paths := fun (u, v) =>
      if u = .root ∧ v = r0 then Regex.char (PathElement.root_to_var var_x)
      else if u = r0 ∧ v = r0 then Regex.ε
      else if u = .root ∧ v = .root then Regex.ε
      else Regex.empty
  }
  funEnv := AssocMap.empty
}

-- Environment after `release(s0)`
-- s0 consumed, r0 deleted from PathEnv
-- This should be equivalent to foo_initEnv!
def env_after_release : TypeEnv := {
  siteEnv := AssocMap.empty
  varEnv := foo_initEnv.varEnv  -- unchanged (no variable assignments)
  pathEnv := delete_ref_node env_after_borrow.pathEnv r0
  funEnv := AssocMap.empty
}

/-!
## Type Checking Trace

Let's trace through the type checking to understand why this version works:

**Entry environment (foo_initEnv):**
- `siteEnv`: empty
- `varEnv`: `{x -> (valid, .basic .u64, mutable)}`
- `pathEnv`: `PathEnv.init` (only root with ε self-edge)

**After `let s0 = &x` (borrowImm):**
- `siteEnv`: `{s0 -> .ref .u64 r0 .siteBorrowImm}`
- `pathEnv`: adds edge `root --[var_x]--> r0`
- x is now borrowed

**After `release(s0)`:**
- `siteEnv`: s0 consumed (empty again)
- `pathEnv`: reference r0 deleted via `delete_ref_node`
- **The borrow edge is removed!**

**After `jump "l0"`:**
- Current env: siteEnv empty, varEnv unchanged, pathEnv should equal PathEnv.init
- This should match foo_initEnv!
- `TypeEnv.equiv` should succeed!

The key insight is that `release` removes the reference from PathEnv via
`delete_ref_node`, which sets all paths involving r0 to `empty` and removes
r0 from the refs list. This restores the PathEnv to its initial state.
-/

-- Test theorem
theorem foo_check: check_fun foo foo_lenv := by rfl

-- Theorem: foo is well-typed
theorem foo_welltyped : ∃ lenv, typecheck_fun foo lenv := by
  exists foo_lenv
  apply typecheck_fun.fun_ok (initEnv := foo_initEnv)
  · -- initEnv.varEnv = init_fun_varEnv foo
    rfl
  · -- initEnv.siteEnv = empty
    rfl
  · -- initEnv.pathEnv = PathEnv.init
    rfl
  · -- foo.blocks ≠ []
    simp only [foo]; intro h; exact List.noConfusion h
  · -- Entry block environment equivalence (now 2-tuple Block)
    intro entryLabel entryBody entryEnv hhead hlookup
    simp only [foo, List.head?] at hhead
    injection hhead with hblock
    have h1 : entryLabel = "l0" := (congrArg Block.label hblock).symm
    subst h1
    simp only [foo_lenv, AssocMap.insert, AssocMap.lookup] at hlookup
    injection hlookup with heq
    rw [← heq]
    -- Prove reflexivity of equiv
    unfold TypeEnv.equiv
    refine ⟨LookupEquiv.refl _, VarEnvLookupCompatible.refl _, rfl, ?_⟩
    intros; rfl
  · -- Every block must type check
    intro block hmem blockEnv hlookup
    simp only [foo, List.mem_singleton] at hmem
    subst hmem
    simp only [foo_lenv, AssocMap.insert, AssocMap.lookup] at hlookup
    injection hlookup with heq
    subst heq

    -- Define intermediate environments
    let pe1 : PathEnv := update_with_extension r0 .root [.root_to_var var_x]
                           (update_with_epsilon r0 r0 PathEnv.init)

    let env1 : TypeEnv := {
      siteEnv := AssocMap.insert AssocMap.empty s0 (.ref .u64 r0 .siteBorrowImm)
      varEnv := init_varEnv_from_params [(var_x, .basic .u64)]
      pathEnv := pe1
      funEnv := AssocMap.empty
    }

    let env2 : TypeEnv := {
      siteEnv := AssocMap.empty
      varEnv := init_varEnv_from_params [(var_x, .basic .u64)]
      pathEnv := delete_ref_node pe1 r0
      funEnv := AssocMap.empty
    }

    -- Key fact: r0 is not root
    have hr0_not_root : r0 ≠ Aref.root := by
      simp only [r0]; intro h; injection h

    -- After delete_ref_node, only .root is in refs
    have hrefs : (delete_ref_node pe1 r0).refs = [.root] := rfl

    -- The refs match PathEnv.init.refs
    have hrefs_eq : (delete_ref_node pe1 r0).refs = PathEnv.init.refs := by
      simp only [hrefs, PathEnv.init]

    -- Paths between .root and .root are preserved
    have hpaths_root : (delete_ref_node pe1 r0).paths (.root, .root) =
                       PathEnv.init.paths (.root, .root) := by
      simp only [delete_ref_node]
      have hne : ¬(Aref.root = r0 ∨ Aref.root = r0) := by
        intro h
        cases h with
        | inl h => exact hr0_not_root h.symm
        | inr h => exact hr0_not_root h.symm
      simp only [hne, ite_false]
      rfl

    -- TypeEnv.subsumes foo_initEnv env2
    have hsubsumes : TypeEnv.subsumes foo_initEnv env2 := by
      unfold TypeEnv.subsumes
      refine ⟨LookupEquiv.refl _, VarEnvLookupCompatible.refl _, hrefs_eq, ?_⟩
      intro u v hu hv path hinterp
      rw [hrefs] at hu hv
      simp only [List.mem_singleton] at hu hv
      subst hu hv
      simp only [foo_initEnv]
      rwa [← hpaths_root]

    -- typecheck_block is now just typecheck_stmt (body includes terminal)
    unfold typecheck_block
    -- Body: letBind s0 (&x) (release s0 (jump "l0"))
    -- Type check: let_bind_borrowImm -> release -> jump
    apply typecheck_stmt.let_bind_borrowImm (r := r0)
    · rfl  -- lookup varEnv var_x
    · rfl  -- notIn siteEnv s0
    · rfl  -- freshRefBool r0
    · -- continuation: release s0 (jump "l0")
      apply typecheck_stmt.release (τ := .u64) (r := r0) (isBor := .siteBorrowImm)
      · rfl  -- lookup siteEnv s0
      · -- continuation: jump "l0"
        apply typecheck_stmt.jump (envL := foo_initEnv)
        · rfl  -- lookup lenv "l0" = some foo_initEnv
        · exact hsubsumes  -- TypeEnv.subsumes foo_initEnv env2

end LeanMove.Examples.BorrowInLoopFixed
