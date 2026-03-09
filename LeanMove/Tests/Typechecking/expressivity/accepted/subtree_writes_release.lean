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
# Subtree Writes Release

Source: https://github.com/tnowacki/sui/blob/example-tests/external-crates/move/crates/bytecode-verifier-transactional-tests/tests/reference_safety/expressivity/subtree_writes_release.mvir

This module demonstrates that "release is lossy in the graph" - writes to
references are safe even when there's complex aliasing, as long as references
are properly released.

Nested struct hierarchy:
- Tree { l: Sub1, r: Sub1 }
- Sub1 { l: Sub2, r: Sub2 }
- Sub2 { l: u64, r: u64 }

Original MVIR:
```
t(cond: bool, root: &mut Self.Tree) {
    let x: &mut Self.Sub1;
    let y: &mut u64;
label l0:
    jump_if (move(cond)) l2;
label l1:
    x = &mut copy(root).Tree::l;
    y = &mut (&mut copy(x).Sub1::l).Sub2::l;
    jump l3;
label l2:
    x = &mut copy(root).Tree::r;
    y = &mut (&mut copy(x).Sub1::r).Sub2::r;
    jump l3;
label l3:
    _ = move(x);
    // should be safe root.l.r is not borrowed
    *(&mut (&mut copy(root).Tree::l).Sub1::r) = Sub2 { l: 0, r: 0 };
    *move(y) = 0;
    return;
}
```
-/

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Typing
open AssocMap
open Regex

namespace LeanMove.Tests.Expressivity.SubtreeWritesRelease

-- Fields for nested structs
def field_l : Field := ⟨"l"⟩
def field_r : Field := ⟨"r"⟩

-- Sub2 { l: u64, r: u64 }
def sub2_entries : AssocMap Field BasicMoveType :=
  insert (insert empty field_l .u64) field_r .u64

-- Sub1 { l: Sub2, r: Sub2 }
def sub1_entries : AssocMap Field BasicMoveType :=
  insert (insert empty field_l (.trecord sub2_entries)) field_r (.trecord sub2_entries)

-- Tree { l: Sub1, r: Sub1 }
def tree_entries : AssocMap Field BasicMoveType :=
  insert (insert empty field_l (.trecord sub1_entries)) field_r (.trecord sub1_entries)

-- Abstract reference for the parameter
def root_var : Aref := .paramRef ⟨"root"⟩

-- Variables
def var_cond : Var := ⟨"cond"⟩
def var_root : Var := ⟨"root"⟩
def var_x : Var := ⟨"x"⟩
def var_y : Var := ⟨"y"⟩

-- Hand-written FunDef moved to Tests/Parsing/Test_subtree_writes_release.lean

-- -----------------------------------------------------
-- -           Parsed MVIR                             --
-- -----------------------------------------------------

open LeanMove.Tests.Parsing.TestUtils

private def subtreeWritesReleaseMvir :=
  include_str "../../../MVIR/subtree_writes_release.mvir"

-- Verify that parsing the MVIR succeeds
#guard (parseAndTranslate subtreeWritesReleaseMvir).isOk

private def parsedFuns := (parseAndTranslate subtreeWritesReleaseMvir).toOption.get!

def parsed_t := (findFun parsedFuns "t").get!

-- Uncomment to pretty-print the parsed FunDef:
-- #eval IO.println (ppFunDef "t" parsed_t)

-- -----------------------------------------------------
-- -           Algorithmic Type Checking Tests        --
-- -----------------------------------------------------

-- VarEnv at l1/l2 entry (after l0: cond consumed by move)
def t_branch_varEnv : VarEnv :=
  let ve := init_fun_varEnv parsed_t
  update ve var_cond (.invalidVar, .basic .tbool, .mutable)

-- VarEnv at l3 entry (x,y assigned/valid; cond still invalid)
-- Template refids: arbitrary fresh values, freshened by freshenBlockEnv
def t_l3_varEnv : VarEnv :=
  let ve := t_branch_varEnv
  let ve := update ve var_x (.validVar, .ref (.trecord sub1_entries) (.refid 2) .siteBorrowMut, .mutable)
  update ve var_y (.validVar, .ref .u64 (.refid 5) .siteBorrowMut, .mutable)

-- Regex helpers matching the structural forms of field paths.
-- Forward paths: extend ε by field chars
private def fl := Regex.concat Regex.ε (Regex.char (PathElement.field field_l))
private def fr := Regex.concat Regex.ε (Regex.char (PathElement.field field_r))
private def fl2 := Regex.concat fl (Regex.char (PathElement.field field_l))
private def fr2 := Regex.concat fr (Regex.char (PathElement.field field_r))
private def fl3 := Regex.concat fl2 (Regex.char (PathElement.field field_l))
private def fr3 := Regex.concat fr2 (Regex.char (PathElement.field field_r))

-- Reverse paths: Brzozowski derivatives of ε
private def dfl := Regex.deriv Regex.ε (PathElement.field field_l)
private def dfr := Regex.deriv Regex.ε (PathElement.field field_r)
private def dfl2 := Regex.deriv dfl (PathElement.field field_l)
private def dfr2 := Regex.deriv dfr (PathElement.field field_r)
private def dfl3 := Regex.deriv dfl2 (PathElement.field field_l)
private def dfr3 := Regex.deriv dfr2 (PathElement.field field_r)

-- Template refs: arbitrary fresh values (not tied to checker's numbering)
-- r1: copy alias of root, r2: x (var), r3: copy alias of x
-- r4: borrowMutField intermediate, r5: y (var)
private def r1 : Aref := .refid 1
private def r2 : Aref := .refid 2
private def r3 : Aref := .refid 3
private def r4 : Aref := .refid 4
private def r5 : Aref := .refid 5

-- l3 PathEnvDec: paths from both branches (l1 uses field_l, l2 uses field_r).
-- Uses arbitrary template refids; freshenBlockEnv + extendRefSubst handle the mapping.
def t_l3_pathEnvDec : PathEnvDec :=
  { refs := [r5, r4, r3, r2, r1, .root, root_var]
    paths :=
      (AssocMap.empty
      -- root_var ↔ r1: ε (copy alias, same in both branches)
      |>.insert (root_var, r1) Regex.ε
      |>.insert (r1, root_var) Regex.ε
      -- root_var ↔ r2: union fl fr / union dfl dfr
      |>.insert (root_var, r2) (.union fl fr)
      |>.insert (r2, root_var) (.union dfl dfr)
      -- root_var ↔ r3: union fl fr / union dfl dfr (r3 is alias of r2)
      |>.insert (root_var, r3) (.union fl fr)
      |>.insert (r3, root_var) (.union dfl dfr)
      -- root_var ↔ r4: union fl2 fr2 / union dfl2 dfr2
      |>.insert (root_var, r4) (.union fl2 fr2)
      |>.insert (r4, root_var) (.union dfl2 dfr2)
      -- root_var ↔ r5: union fl3 fr3 / union dfl3 dfr3
      |>.insert (root_var, r5) (.union fl3 fr3)
      |>.insert (r5, root_var) (.union dfl3 dfr3)
      -- r1 ↔ r2: union fl fr / union dfl dfr
      |>.insert (r1, r2) (.union fl fr)
      |>.insert (r2, r1) (.union dfl dfr)
      -- r1 ↔ r3: union fl fr / union dfl dfr
      |>.insert (r1, r3) (.union fl fr)
      |>.insert (r3, r1) (.union dfl dfr)
      -- r2 ↔ r3: ε (alias, same in both branches)
      |>.insert (r2, r3) Regex.ε
      |>.insert (r3, r2) Regex.ε
      -- r2 ↔ r4: union fl fr / union dfl dfr
      |>.insert (r2, r4) (.union fl fr)
      |>.insert (r4, r2) (.union dfl dfr)
      -- r2 ↔ r5: union fl2 fr2 / union dfl2 dfr2
      |>.insert (r2, r5) (.union fl2 fr2)
      |>.insert (r5, r2) (.union dfl2 dfr2)
      -- r3 ↔ r4: union fl fr / union dfl dfr
      |>.insert (r3, r4) (.union fl fr)
      |>.insert (r4, r3) (.union dfl dfr)
      -- r3 ↔ r5: union fl2 fr2 / union dfl2 dfr2
      |>.insert (r3, r5) (.union fl2 fr2)
      |>.insert (r5, r3) (.union dfl2 dfr2)
      -- r4 ↔ r5: union fl fr / union dfl dfr
      |>.insert (r4, r5) (.union fl fr)
      |>.insert (r5, r4) (.union dfl dfr)
      -- r1 ↔ r4: union fl2 fr2 / union dfl2 dfr2
      |>.insert (r1, r4) (.union fl2 fr2)
      |>.insert (r4, r1) (.union dfl2 dfr2)
      -- r1 ↔ r5: union fl3 fr3 / union dfl3 dfr3
      |>.insert (r1, r5) (.union fl3 fr3)
      |>.insert (r5, r1) (.union dfl3 dfr3))
  }

-- Template for l3 environment (uses simple refids that get freshened)
private def t_l3_env_template : TypeEnvDec :=
  { siteEnv := AssocMap.empty, varEnv := t_l3_varEnv,
    pathEnv := t_l3_pathEnvDec, funEnv := AssocMap.empty }

-- Decidable label environment
-- freshenBlockEnv is applied uniformly; it is a no-op for l0/l1/l2 (no valid-var refids).
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

end LeanMove.Tests.Expressivity.SubtreeWritesRelease
