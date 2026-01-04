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
import Batteries.Data.HashMap
import Ssreflect.Lang

import LeanMove.Structures.AssocMap
import LeanMove.Structures.Regex
import LeanMove.Lang

/-!
# Type Environment Definitions

This file contains the definitions of type environments and their components
used by the MoveLight type checker. The typing rules themselves are in
`TypeChecking.lean`.

## Contents
- Mutability and validity types
- Environment types (SiteEnv, VarEnv, PathEnv, FunEnv, TypeEnv, LabelEnv)
- PathEnv operations (init, update, delete, etc.)
- TypeEnv equivalence
- Lemmas about PathEnv operations
-/

namespace LeanMove.Checker

open Lang
open Lang.MoveLight
open AssocMap
open Regex

/- ---------------------------------------------------- -/
/-       Basic Types for Type Checking                  -/
/- ---------------------------------------------------- -/

-- Whether the variable is mutable or immutable
inductive Mut where
  | immut
  | mutable
deriving Repr, DecidableEq, Inhabited, Hashable

-- Instace of order on borrow kinds
instance : Ord Mut where
  compare a b := match a, b with
    | .immut, .mutable => .lt
    | .mutable, .immut => .gt
    | .immut, .immut => .eq
    | .mutable, .mutable => .eq

instance : LE Mut where
  le a b := match a, b with
    | _, .mutable => true
    | .mutable, .immut => false
    | .immut, .immut => true

-- Whether the variable is borrowed or not
inductive VarBorrowStatus where
  | varBorrowedImm
  | varBorrowedMut
  | varNotBorrowed
deriving Repr, DecidableEq, Inhabited, Hashable

instance : LE VarBorrowStatus where
  le a b := match a, b with
    | .varNotBorrowed, _ => true
    | _, .varNotBorrowed => false
    | .varBorrowedImm, .varBorrowedMut => true
    | .varBorrowedMut, .varBorrowedImm => false
    | .varBorrowedImm, .varBorrowedImm => true
    | .varBorrowedMut, .varBorrowedMut => true

-- Whether the variable is valid to move/copy from
-- Better than Boolean
inductive IsValid where
  | validVar
  | invalidVar
deriving Repr, DecidableEq, Inhabited, Hashable

/- ---------------------------------------------------- -/
/-       Environment Types                              -/
/- ---------------------------------------------------- -/

-- Environment mapping abstract locations to their types, abstract references, and borrow marker
abbrev SiteEnv := AssocMap Site MoveType

-- Environment mapping variables to their site, types, mutability, abstract references, and borrow status
abbrev VarEnv := AssocMap Var (IsValid × MoveType × Mut)

-- Either a root or a field access
inductive PathElement where
  | field : Field → PathElement
  | root_to_var : Var → PathElement
deriving Repr, DecidableEq, Inhabited, Hashable

abbrev Path := List PathElement

-- Environment mapping pairs of sites to sets regular expressions
structure PathEnv where
  refs : List Aref
  -- Initially empty for each pair
  paths: (Aref × Aref) → Regex PathElement

/- ---------------------------------------------------- -/
/-       PathEnv Operations                             -/
/- ---------------------------------------------------- -/

/-- Initialize an empty PathEnv with root already present -/
def PathEnv.init : PathEnv :=
  { refs := [.root],
    paths := fun (u, v) => if u = v then Regex.ε else Regex.empty }

-- Check that the property p holds for all paths from s in penv
def check_outbound (penv: PathEnv) (s: Aref) (p: Regex PathElement → Prop) :=
  forall s', p (penv.paths  (s, s'))

-- Garbage collect the reference from penv
def garbage_collect (penv: PathEnv) (r: Aref) : PathEnv :=
  let G := penv.paths
  let paths' := fun (u, v) => if u = r ∨ v = r then Regex.empty else G (u, v)
  let refs' := List.filter (fun r' => r' ≠ r) penv.refs
  { penv with paths := paths', refs := refs' }

-- z = &x.p
def update_with_extension (z x : Aref) (p: Path) (pe: PathEnv) : PathEnv :=
  let G := pe.paths
  let paths' := fun (u, v) =>
    if u = z ∧ v = z then Regex.ε  else
    if v = z then G (u, x) ∘ p else
    if u = z then der (G (x, v)) p
    else G (u, v)
  let refs' := if z ∉ pe.refs then z :: pe.refs else pe.refs
  { pe with paths := paths', refs := refs' }

def extend_with_star (target source : Aref) (pe: PathEnv) : PathEnv :=
  let G := pe.paths
  let paths' := fun (u, v) =>
    if u = target ∧ v = target then Regex.ε  else
    if v = target then Regex.concat (G (u, source)) (Regex.star (Regex.dot)) else
    -- [TODO] [Q2] Discuss what is going on here compared ot the previous case.
    -- if u = target then der (G (source, v)) p else
    G (u, v)
  let refs' := if target ∉ pe.refs then target :: pe.refs else pe.refs
  { pe with paths := paths', refs := refs' }

-- z = &x
def update_with_epsilon (z x : Aref) (pe: PathEnv)  : PathEnv :=
  update_with_extension z x [] pe


def delete_ref_node (pe: PathEnv) (r : Aref) : PathEnv :=
  let G := pe.paths
  let paths' := fun (u, v) => if u = r ∨ v = r then Regex.empty else G (u, v)
  { pe with refs  := List.filter (fun r' => r' ≠ r) pe.refs,
            paths := paths' }

-- Consume reference r and transfer its reachability to r'
-- Used by freeze: old mutable reference is consumed, new immutable reference inherits paths
-- Semantics: all edges pointing TO r now point to r' instead, r is removed
def consume_ref_transfer (pe: PathEnv) (r r' : Aref) : PathEnv :=
  let G := pe.paths
  -- For each edge (u, r) with label L, create edge (u, r') with label L
  -- Remove all edges involving r
  let paths' := fun (u, v) =>
    if u = r ∨ v = r then
      Regex.empty
    else if v = r' then
      -- r' gets edges from: original edges to r' + edges that were to r
      Regex.union (G (u, r')) (G (u, r))
    else
      G (u, v)
  let refs' := if r' ∉ pe.refs then r' :: pe.refs else pe.refs
  { pe with refs  := List.filter (fun x => x ≠ r) refs',
            paths := paths' }

def freshRef (r: Aref) (pe: PathEnv) := r ∉ pe.refs

/- ---------------------------------------------------- -/
/-       Function Signatures                            -/
/- ---------------------------------------------------- -/

structure ParamType where
  -- inner type
  basicType : BasicMoveType
  -- mutable    = some true
  -- immmutable = some false
  -- not a reference = none
  isRefMut : Option Bool
deriving Repr, Inhabited, Hashable

-- Function table
structure FunSig where
  params : List ParamType
  returnType : List ParamType
deriving Repr, Inhabited, Hashable

abbrev FunEnv := AssocMap Id FunSig

/- ---------------------------------------------------- -/
/-       Type Environment                               -/
/- ---------------------------------------------------- -/

-- New structure packaging all environments
structure TypeEnv where
  siteEnv : SiteEnv
  varEnv  : VarEnv
  pathEnv : PathEnv
  funEnv  : FunEnv

-- Label environment: maps labels to their expected entry type environments
-- Used for type checking control flow (jumps must target labels with compatible environments)
abbrev LabelEnv := AssocMap Label TypeEnv

/--
  Check that two type environments are equivalent.

  For PathEnv, we only compare paths between references that are in the refs list.
  This is semantically correct because:
  1. The `refs` list tracks which abstract references are "live" in the current scope
  2. Paths involving non-live references are irrelevant for borrow checking
  3. Operations like `delete_ref_node` set paths involving deleted refs to `empty`,
     but the deleted ref is removed from `refs`, so we don't compare those paths

  This weaker equivalence allows loops to type-check correctly: after releasing
  a borrow, the deleted reference's paths become `empty`, but since it's no longer
  in `refs`, the environment is still equivalent to the loop entry environment.
-/
def TypeEnv.equiv (env1 env2 : TypeEnv) : Prop :=
  env1.siteEnv = env2.siteEnv ∧
  env1.varEnv = env2.varEnv ∧
  env1.pathEnv.refs = env2.pathEnv.refs ∧
  (∀ u v, u ∈ env1.pathEnv.refs → v ∈ env1.pathEnv.refs →
    env1.pathEnv.paths (u, v) = env2.pathEnv.paths (u, v))

/- ---------------------------------------------------- -/
/-       Well-formedness of the environments            -/
/- ---------------------------------------------------- -/

structure WellFormedEnv (typeEnv : TypeEnv) where
  -- All abstract locations have unique keys
  uniqueSites : uniqueKeys typeEnv.siteEnv
  -- The root is always present in the path environment
  rootPresent : Aref.root ∈ typeEnv.pathEnv.refs
  -- TODO: say that for all pairs in pathEnv there is either
  -- a variable in varEnv or a site in siteEnv

/- ---------------------------------------------------- -/
/-       Lemmas for PathEnv operations                   -/
/- ---------------------------------------------------- -/

/--
  When we delete a reference `r` from a PathEnv,
  the resulting refs list filters out `r`.
-/
lemma delete_ref_node_refs (pe : PathEnv) (r : Aref) :
    (delete_ref_node pe r).refs = List.filter (fun r' => r' ≠ r) pe.refs := by
  rfl

/--
  When we delete a reference `r`, all paths involving `r` become empty.
-/
lemma delete_ref_node_paths_involving_r (pe : PathEnv) (r : Aref) (u v : Aref) :
    u = r ∨ v = r → (delete_ref_node pe r).paths (u, v) = Regex.empty := by
  move=> h
  simp only [delete_ref_node]
  scase: h => hr
  · simp [hr]
  · simp [hr]

/--
  When we delete a reference `r`, paths not involving `r` are unchanged.
-/
lemma delete_ref_node_paths_not_involving_r (pe : PathEnv) (r : Aref) (u v : Aref) :
    u ≠ r → v ≠ r → (delete_ref_node pe r).paths (u, v) = pe.paths (u, v) := by
  move=> hu hv
  simp only [delete_ref_node]
  simp [hu, hv]

/--
  Deleting a reference `r ≠ .root` from a PathEnv with refs = [r, .root]
  gives refs = [.root].
-/
lemma delete_ref_node_restores_init_refs (pe : PathEnv) (r : Aref) (hr : r ≠ .root)
    (hrefs : pe.refs = [r, .root]) :
    (delete_ref_node pe r).refs = [.root] := by
  simp only [delete_ref_node, hrefs, List.filter]
  have h : Aref.root ≠ r := fun h => hr h.symm
  simp [h]

/-!
### PathEnv Equivalence After delete_ref_node

The lemma `delete_ref_node PathEnv.init r = PathEnv.init` is **NOT provable**
for syntactic equality because:

- `PathEnv.init.paths (r, r) = Regex.ε` for ANY `r` (the function returns ε when u = v)
- `(delete_ref_node PathEnv.init r).paths (r, r) = Regex.empty` (paths involving r are emptied)

These differ syntactically even though `r ∉ PathEnv.init.refs`.

**Solution implemented:** We weakened `TypeEnv.equiv` to only compare paths between
references that are in the refs list. This is semantically correct because paths
involving non-live references are irrelevant for borrow checking.

With this weaker equivalence, `delete_ref_node` on a PathEnv that was extended
from `PathEnv.init` correctly produces an equivalent PathEnv.
-/

/--
  For references u, v that are both in PathEnv.init.refs (i.e., both equal .root),
  delete_ref_node preserves the path value when r ≠ .root.
-/
lemma delete_ref_node_init_paths_between_roots (r : Aref) (hr : r ≠ .root) :
    (delete_ref_node PathEnv.init r).paths (.root, .root) = PathEnv.init.paths (.root, .root) := by
  simp only [delete_ref_node, PathEnv.init]
  have h1 : ¬(Aref.root = r) := fun h => hr h.symm
  simp [h1]

/--
  After deleting a fresh reference r ≠ .root from PathEnv.init,
  the refs list is [.root] (same as PathEnv.init.refs).
-/
lemma delete_ref_node_init_refs (r : Aref) (hr : r ≠ .root) :
    (delete_ref_node PathEnv.init r).refs = PathEnv.init.refs := by
  simp only [delete_ref_node, PathEnv.init, List.filter]
  have h : Aref.root ≠ r := fun h => hr h.symm
  simp [h]

/--
  Key lemma: For any PathEnv `pe`, after deleting `r`, the paths between
  remaining refs match the original paths. This is because `delete_ref_node`
  only modifies paths involving `r`, and refs remaining in the list are
  guaranteed to be different from `r`.
-/
lemma delete_ref_node_paths_between_remaining (pe : PathEnv) (r : Aref)
    (u v : Aref) (hu : u ∈ (delete_ref_node pe r).refs) (hv : v ∈ (delete_ref_node pe r).refs) :
    (delete_ref_node pe r).paths (u, v) = pe.paths (u, v) := by
  -- u and v are in the filtered refs, so u ≠ r and v ≠ r
  simp only [delete_ref_node_refs] at hu hv
  simp only [List.mem_filter, decide_eq_true_eq] at hu hv
  have hur : u ≠ r := hu.2
  have hvr : v ≠ r := hv.2
  exact delete_ref_node_paths_not_involving_r pe r u v hur hvr

end LeanMove.Checker
