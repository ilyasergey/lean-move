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

namespace LeanMove.Typing

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

def Mut.le (a b : Mut) : Prop :=
  match a, b with
  | _, .mutable => True
  | .mutable, .immut => False
  | .immut, .immut => True

instance : LE Mut where
  le := Mut.le

instance : (a b : Mut) → Decidable (a ≤ b)
  | _, .mutable => isTrue (by simp only [LE.le, Mut.le])
  | .mutable, .immut => isFalse (by simp only [LE.le, Mut.le]; exact id)
  | .immut, .immut => isTrue (by simp only [LE.le, Mut.le])

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

/-- Two VarEnv entries are compatible if IsValid and Mut match exactly,
    and MoveType is compatible (ignoring Aref values for `.refid`). -/
def VarEntryCompatible : (IsValid × MoveType × Mut) → (IsValid × MoveType × Mut) → Prop
  | (v1, t1, m1), (v2, t2, m2) => v1 = v2 ∧ MoveType.compatible t1 t2 ∧ m1 = m2

/-- Two VarEnvs are lookup-compatible if for every key, the looked-up entries are compatible.
    This is like LookupEquiv but uses MoveType.compatible instead of exact equality for types. -/
def VarEnvLookupCompatible (m1 m2 : VarEnv) : Prop :=
  ∀ k, match AssocMap.lookup m1 k, AssocMap.lookup m2 k with
    | some e1, some e2 => VarEntryCompatible e1 e2
    | none, none => True
    | _, _ => False

theorem VarEnvLookupCompatible.refl (m : VarEnv) : VarEnvLookupCompatible m m := by
  intro k
  cases AssocMap.lookup m k with
  | none => trivial
  | some e =>
    obtain ⟨v, t, mu⟩ := e
    exact ⟨rfl, MoveType.compatible_of_beq t t (MoveType.beq_of_eq t t rfl), rfl⟩

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

/-- Initial PathEnv for a function: includes .root and all abstract refs from ref-typed params.
    For functions with only basic-typed params, this equals `PathEnv.init` definitionally. -/
def init_fun_pathEnv (f : FunDef) : PathEnv :=
  let paramRefs := f.params.filterMap (fun (_, τ) => match τ with
    | .ref _ r _ => some r
    | _ => none)
  { refs := .root :: paramRefs,
    paths := fun (u, v) =>
      if u = v then Regex.ε
      else .empty }

/-- When all parameters have basic types, `init_fun_pathEnv f = PathEnv.init`. -/
lemma init_fun_pathEnv_basic (f : FunDef)
    (hbasic : ∀ x τ, (x, τ) ∈ f.params → ∃ bt, τ = .basic bt) :
    init_fun_pathEnv f = PathEnv.init := by
  simp only [init_fun_pathEnv, PathEnv.init]
  have hnil : f.params.filterMap (fun (_, τ) => match τ with
    | .ref _ r _ => some r | _ => none) = [] := by
    rw [List.filterMap_eq_nil_iff]
    intro ⟨x, τ⟩ hmem
    obtain ⟨bt, hbt⟩ := hbasic x τ hmem
    simp [hbt]
  simp only [hnil]

-- Check that the property p holds for all paths from s to tracked refs in penv
def check_outbound (penv: PathEnv) (s: Aref) (p: Regex PathElement → Prop) :=
  forall s', s' ∈ penv.refs → p (penv.paths  (s, s'))

-- Garbage collect the reference from penv
def garbage_collect (penv: PathEnv) (r: Aref) : PathEnv :=
  let G := penv.paths
  let paths' := fun (u, v) =>
    if u = r ∧ v = r then Regex.ε         -- preserve ε self-loop for non-member invariant
    else if u = r ∨ v = r then Regex.empty -- clear all other edges involving r
    else G (u, v)
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
    if u = target then Regex.concat (Regex.star (Regex.dot)) (G (source, v)) else
    G (u, v)
  let refs' := if target ∉ pe.refs then target :: pe.refs else pe.refs
  { pe with paths := paths', refs := refs' }

-- z = &x
def update_with_epsilon (z x : Aref) (pe: PathEnv)  : PathEnv :=
  update_with_extension z x [] pe


def delete_ref_node (pe: PathEnv) (r : Aref) : PathEnv :=
  let G := pe.paths
  let paths' := fun (u, v) =>
    if u = r ∧ v = r then Regex.ε         -- preserve ε self-loop for non-member invariant
    else if u = r ∨ v = r then Regex.empty -- clear all other edges involving r
    else G (u, v)
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
    if u = r ∧ v = r then
      Regex.ε  -- preserve ε self-loop for non-member invariant
    else if u = r ∨ v = r then
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

/-- Boolean version of freshRef for use in algorithmic type checking -/
def freshRefBool (r: Aref) (pe: PathEnv) : Bool := !(pe.refs.contains r)

/-- Extract the refid from an Aref, returning 0 for non-refid Arefs -/
def getRefId (r : Aref) : Nat :=
  match r with
  | .refid n => n
  | _ => 0

/-- Compute a fresh Aref by finding the maximum refid in the PathEnv and adding 1 -/
def nextFreshRef (pe : PathEnv) : Aref :=
  let maxId := pe.refs.foldl (fun acc r => max acc (getRefId r)) 0
  .refid (maxId + 1)

/-- Extract the Aref from a MoveType, if present -/
def getTypeRef : MoveType → Option Aref
  | .ref _ r _ => some r
  | .basic _ => none

/-- Collect all Arefs appearing in VarEnv types -/
def collectVarEnvRefs (ve : VarEnv) : List Aref :=
  ve.entries.filterMap fun (_, (_, τ, _)) => getTypeRef τ

/-- Collect all Arefs appearing in SiteEnv types -/
def collectSiteEnvRefs (se : SiteEnv) : List Aref :=
  se.entries.filterMap fun (_, τ) => getTypeRef τ

/- ---------------------------------------------------- -/
/-       Function Signatures                            -/
/- ---------------------------------------------------- -/

-- ParamType is defined in LeanMove/Lang/MoveLight.lean (imported transitively)

-- Function table
structure FunSig where
  params : List ParamType
  returnType : List ParamType
deriving Repr, Inhabited, Hashable, DecidableEq

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

/-- Propositional version: r doesn't appear as a ref in any VarEnv or SiteEnv entry,
    is fresh in PathEnv, and is not a variable reference. -/
def freshRefInEnv (r : Aref) (env : TypeEnv) : Prop :=
  freshRef r env.pathEnv ∧
  r ∉ collectVarEnvRefs env.varEnv ∧
  r ∉ collectSiteEnvRefs env.siteEnv ∧
  (∀ v, r ≠ .varRef v)

/-- Boolean version of freshRefInEnv for use in algorithmic type checking -/
def freshRefInEnvBool (r : Aref) (env : TypeEnv) : Bool :=
  freshRefBool r env.pathEnv &&
  !(collectVarEnvRefs env.varEnv).contains r &&
  !(collectSiteEnvRefs env.siteEnv).contains r &&
  match r with | .varRef _ => false | _ => true

/-- Compute a fresh Aref by finding the maximum refid across all TypeEnv components -/
def nextFreshRefInEnv (env : TypeEnv) : Aref :=
  let allRefs := env.pathEnv.refs ++ collectVarEnvRefs env.varEnv ++ collectSiteEnvRefs env.siteEnv
  let maxId := allRefs.foldl (fun acc r => max acc (getRefId r)) 0
  .refid (maxId + 1)

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
  LookupEquiv env1.siteEnv env2.siteEnv ∧
  VarEnvLookupCompatible env1.varEnv env2.varEnv ∧
  env1.pathEnv.refs = env2.pathEnv.refs ∧
  (∀ u v, u ∈ env1.pathEnv.refs → v ∈ env1.pathEnv.refs →
    env1.pathEnv.paths (u, v) = env2.pathEnv.paths (u, v))

/- ---------------------------------------------------- -/
/-       Aref Substitution (for refid unification)     -/
/- ---------------------------------------------------- -/

/-- Apply a substitution to a MoveType's Aref.
    Only ref types are affected; basic types are unchanged. -/
def applySubstMoveType (σ : Aref → Aref) : MoveType → MoveType
  | .basic bt => .basic bt
  | .ref bt r bk => .ref bt (σ r) bk

/-- Base type compatibility for MoveType: checks base type and borrow kind match,
    ignoring the Aref. Used for invalid (consumed) entries where arefs are irrelevant. -/
def MoveType.baseCompatible : MoveType → MoveType → Prop
  | .basic bt1, .basic bt2 => bt1 = bt2
  | .ref bt1 _ bk1, .ref bt2 _ bk2 => bt1 = bt2 ∧ bk1 = bk2
  | _, _ => False

/-- VarEnv entries match after applying substitution σ to the first VarEnv's types.
    For valid entries: exact match after applying σ (refids are unified).
    For invalid entries: base type compatibility suffices (arefs don't matter). -/
def VarEnvSubstEquiv (σ : Aref → Aref) (ve1 ve2 : VarEnv) : Prop :=
  ∀ k, match AssocMap.lookup ve1 k, AssocMap.lookup ve2 k with
    | some (.validVar, τ1, ms1), some (.validVar, τ2, ms2) =>
      applySubstMoveType σ τ1 = τ2 ∧ ms1 = ms2
    | some (.invalidVar, τ1, ms1), some (.invalidVar, τ2, ms2) =>
      MoveType.baseCompatible τ1 τ2 ∧ ms1 = ms2
    | none, none => True
    | _, _ => False

/-- SiteEnv entries match after applying substitution σ to the first SiteEnv's types. -/
def SiteEnvSubstEquiv (σ : Aref → Aref) (se1 se2 : SiteEnv) : Prop :=
  ∀ k, match AssocMap.lookup se1 k, AssocMap.lookup se2 k with
    | some τ1, some τ2 => applySubstMoveType σ τ1 = τ2
    | none, none => True
    | _, _ => False

/-- `envL.subsumes env` means there exists a refid substitution σ such that
    after renaming envL's refid placeholders via σ, the VarEnvs and SiteEnvs
    match env's, the PathEnv refs match env's, and env's paths are included
    in envL's paths.
    σ maps envL's .refid arefs → env's actual arefs (which may include .varRef).
    Used at jump/branch targets where envL is a label environment. -/
def TypeEnv.subsumes (envL env : TypeEnv) : Prop :=
  ∃ σ : Aref → Aref,
    -- σ is identity on non-refid arefs (only .refid placeholders are renamed)
    (∀ r, (∀ n, r ≠ .refid n) → σ r = r) ∧
    -- After σ on envL, VarEnv entries match env's
    VarEnvSubstEquiv σ envL.varEnv env.varEnv ∧
    -- After σ on envL, SiteEnv entries match env's
    SiteEnvSubstEquiv σ envL.siteEnv env.siteEnv ∧
    -- After σ on envL, PathEnv refs match env's (up to permutation)
    (envL.pathEnv.refs.map σ).Perm env.pathEnv.refs ∧
    -- σ is injective on envL.pathEnv.refs (needed for path deletion cases)
    (∀ u v, u ∈ envL.pathEnv.refs → v ∈ envL.pathEnv.refs → σ u = σ v → u = v) ∧
    -- σ doesn't create roots: non-root arefs never map to root
    -- (follows from the algorithmic construction; needed for MoveType.compatible preservation)
    (∀ r, r ≠ .root → σ r ≠ .root) ∧
    -- Paths in env are included in envL (env ⊆ envL, after σ renaming)
    (∀ u v, u ∈ envL.pathEnv.refs → v ∈ envL.pathEnv.refs →
      ∀ path, interpret_regex (env.pathEnv.paths (σ u, σ v)) path →
              interpret_regex (envL.pathEnv.paths (u, v)) path)

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

end LeanMove.Typing
