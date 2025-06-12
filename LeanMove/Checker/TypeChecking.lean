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
import Aesop

import LeanMove.Structures.AssocMap
import LeanMove.Structures.Regex

import LeanMove.Lang

namespace LeanMove.Checker

open Lang
open Lang.MoveLight
open AssocMap
open Regex


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

inductive SiteIsBorrowing where
  | siteBorrowImm : Var -> SiteIsBorrowing
  | siteBorrowMut : Var -> SiteIsBorrowing
  | siteNotBorrowed : SiteIsBorrowing
deriving Repr, DecidableEq, Inhabited, Hashable

-- Whether the variable is valid to move/copy from
-- Better than Boolean
inductive IsValid where
  | validVar
  | invalidVar
deriving Repr, DecidableEq, Inhabited, Hashable


-- Environment mapping abstract locations to their types, abstract references, and borrow marker
abbrev AlocEnv := AssocMap Aloc (MoveType × SiteIsBorrowing)

-- Environment mapping variables to their site, types, mutability, abstract references, and borrow status
abbrev VarEnv := AssocMap Var (IsValid × MoveType × Mut)

-- Either a root or a field access
inductive PathElement where
  | field : Field → PathElement
deriving Repr, DecidableEq, Inhabited, Hashable

-- Environment mapping pairs of sites to sets regular expressions
structure PathEnv where
  refs : List Aref
  -- Initially empty for each pair
  paths: (Aref × Aref) → Regex PathElement

-- z = &x.p
def update_with_extension (pe: PathEnv) (z x : Aref) (p: PathElement) : PathEnv :=
  let G := pe.paths
  let paths' := fun (u, v) =>
    if u = z ∧ v = z then Regex.ε  else
    if v = z then G (u, x) ∘ p else
    if u = z then der (G (x, v)) p
    else G (u, v)
  let refs' := if z ∉ pe.refs then z :: pe.refs else pe.refs
  { pe with paths := paths', refs := refs' }

-- z = &x
def update_with_epsilon (pe: PathEnv) (z x : Aref) : PathEnv :=
  let G := pe.paths
  let paths' := fun (u, v) =>
    if u = z ∧ v = z then Regex.ε  else
    if v = z then G (u, x) else
    if u = z then G (x, v)
    else G (u, v)
  let refs' := if z ∉ pe.refs then z :: pe.refs else pe.refs
  { pe with paths := paths', refs := refs' }


def freshRef (r: Aref) (pe: PathEnv) := r ∉ pe.refs

-- New structure packaging all environments
structure TypeEnv where
  alocEnv : AlocEnv
  varEnv  : VarEnv
  pathEnv : PathEnv

/- ---------------------------------------------------- -/
/-       Well-formedness of the environments            -/
/- ---------------------------------------------------- -/

structure WellFormedEnv (typeEnv : TypeEnv) where
  -- All abstract locations
  uniqueAlocs : uniqueKeys typeEnv.alocEnv
  -- TODO: say that for all pairs in pathEnv there is either
  -- a variable in varEnv or a site in siteEnv

/- ---------------------------------------------------- -/
/- Typing relations for usages, expressions, statements -/
/- ---------------------------------------------------- -/

-- TODO: track borrowed status of the variables in varEnv

open AssocMap

-- Only adopt a reference in the graph if the type is a reference
def with_new_ref (τ : MoveType) (r : Aref) := match τ with
  | MoveType.ref τ' _ => MoveType.ref τ' r
  | MoveType.basic _ => τ

-- relation ⟨L; E; G⟩ ⊢ u ⤳ ⟨L'; E'; G'; Aloc; τ⟩ for the type Usage

/-
[Notes on typecheck_usage]

* Most of the constructors require fresh reference and fresh abstract location
  and  fresh reference. To simplify things those are provided externally and
  checked for being fresh within the respective rule.

  TODO: Check the freshness of references

* The association between a variable/aloc and the respective abstract reference
  is now packaged into the type to avoid clutter. This might bite us in the butt
  later. In any event, one needs to be careful when comparing MoveType instances
  for equality, as they might be the same "type-wise", but differ in the
  abstract references they carry. There is no such problem for basic types,
  which can be compared for equality freely.

* The logic for updating the graph are still missing, and need to be clarified
  with Todd before incorporated into the type checking rules.

 -/

inductive typecheck_usage : TypeEnv → Usage → TypeEnv → Aloc -> MoveType → Prop where
  | t_umove : ∀ env env' x τ ms a,
     -- Can only move from non-borrowed variables
     AssocMap.lookup env.varEnv x = some (.validVar, τ, ms) →
     notIn env.alocEnv a →
     -- No need to handle PathEnv here
     env' = { env with varEnv  := update env.varEnv x (.invalidVar, τ, ms)
                       alocEnv := insert env.alocEnv a (τ, .siteNotBorrowed) } →
     typecheck_usage env (.move x) env' a τ

  -- Copying a variable value, not a reference
  | t_ucopy_val : ∀ env env' x bt ms a,
     AssocMap.lookup env.varEnv x = some (.validVar, MoveType.basic bt, ms) →
     notIn env.alocEnv a →
     env' = { env with alocEnv := insert env.alocEnv a (.basic bt, .siteNotBorrowed)} →
     typecheck_usage env (.copy x) env' a (.basic bt)

  -- Copying a reference value
  | t_ucopy_ref : ∀ env env' x τ ms a (s t: Aref),
     AssocMap.lookup env.varEnv x = some (.validVar, .ref τ s, ms) →
     notIn env.alocEnv a →
     freshRef t env.pathEnv →
     env' = { env with alocEnv := insert env.alocEnv a (MoveType.ref τ t, .siteNotBorrowed)
                       pathEnv := update_with_epsilon env.pathEnv s t } →
     -- TODO: update G with s and r
     typecheck_usage env (.copy x) env' a (.ref τ t)

  -- Borrowing the reference to a variable's content, makes a new reference r
  | t_uborrowImm_val : ∀ env env' x τ ms a (r: Aref),
     AssocMap.lookup env.varEnv x = some (.validVar, .basic τ, ms) →
     AssocMap.notIn env.alocEnv a →
     -- r is a fresh reference to the value, only trivial paths
     env' = { env with alocEnv := insert env.alocEnv a (.ref (.basic τ) r, .siteBorrowImm x)
     -- [Q] Checking: only allocating an epsilon transition from r to r
                       pathEnv := update_with_epsilon env.pathEnv r r } →
     typecheck_usage env (.borrowImm x) env' a (.ref (.basic τ) r)

  -- Borrowing the reference to a variable reference
  | t_uborrowImm_ref : ∀ env env' x τ ms a (s t: Aref),
     AssocMap.lookup env.varEnv x = some (.validVar, .ref τ s, ms) →
     AssocMap.notIn env.alocEnv a →
     -- [Q] Is this really correct? The languages of s and r are the same?
     env' = { env with alocEnv := insert env.alocEnv a (.ref (.ref τ s) t, .siteBorrowImm x)
                       pathEnv := update_with_epsilon env.pathEnv s t } →
     typecheck_usage env (.borrowImm x) env' a (.ref (.ref τ s) t)

  -- Mutable borrow to a value
  | t_uborrowMut_val : ∀ env env' x τ ms a (r: Aref),
     LE.le .mutable ms  →
     AssocMap.lookup env.varEnv x = some (.validVar, .basic τ, ms) →
     AssocMap.notIn env.alocEnv a →
     -- TODO: update G for the new reference r
     env' = { env with alocEnv := insert env.alocEnv a (.ref (.basic τ) r, .siteBorrowMut x)
                       pathEnv := update_with_epsilon env.pathEnv r r } →
     typecheck_usage env (.borrowMut x) env' a (.ref (.basic τ) r)

  -- Borrowing the reference to a variable reference
  | t_uborrowMut_ref : ∀ env env' x τ ms a (s t: Aref),
     LE.le .mutable ms  →
     AssocMap.lookup env.varEnv x = some (.validVar, .ref τ s, ms) →
     AssocMap.notIn env.alocEnv a →
     -- TODO: update G with s and r
     env' = { env with alocEnv := insert env.alocEnv a (.ref (.ref τ s) t, .siteBorrowMut x)
                       pathEnv := update_with_epsilon env.pathEnv s t } →
     typecheck_usage env (.borrowMut x) env' a (.ref (.ref τ s) t)


/- ---------------------------------------------------- -/
/- Typing relations for expressions -/
/- ---------------------------------------------------- -/

-- ⟨L; E; G⟩ ⊢ (e : expr) ⤳ ⟨L'; E'; G'⟩
inductive typecheck_expr : TypeEnv → Expr → TypeEnv → Aloc → MoveType → Prop where
  -- Expression is a usage
  | usage : ∀ env env' u s τ,
     typecheck_usage env u env' s τ ->
     typecheck_expr env (Expr.usage u) env s τ

  ----------------------------------------------------
  -- Done above this line
  ----------------------------------------------------
  | borrowField : ∀ env env' a f af bt bt' isBor fentries r rf,
     -- Site type is τ basic type
     AssocMap.lookup env.alocEnv a = some (.ref (.basic bt) r, isBor) →
     -- This is a record type, here are its entries
     bt = .trecord fentries →
     -- Get the field type via the name f
     lookup fentries f = some bt' →

     -- TODO: add path tracking: what exactly is updated if we delete the old site?


     -- Update site environment with the new reference
     env' = {env with alocEnv := insert (delete env.alocEnv a) af (.ref (.basic bt') rf, isBor)} →
     typecheck_expr env (Expr.borrowField a bt f) env' af (.ref (.basic bt') rf)

  ----------------------------------------------------
  -- Not touched recently below this line
  ----------------------------------------------------
  | borrowMutField : ∀ env s a f s',
     typecheck_expr env (Expr.borrowMutField s a f) env s' TInt
  | binop : ∀ env s1 s2 s',
     typecheck_expr env (Expr.binop s1 s2) env s' TInt
  | readRef : ∀ env s s',
     typecheck_expr env (Expr.readRef s) env s' TInt
  | pack : ∀ env t fs s,
     typecheck_expr env (Expr.pack t fs) env s TInt

inductive typecheck_stmt : TypeEnv → Stmt → TypeEnv → Prop where
  -- Add your constructors here, for example:
  | skip : ∀ env, typecheck_stmt env Stmt.skip env
  -- | assign : ∀ env x e, typecheck_expr env e τ → typecheck_stmt env (MoveLight.Stmt.assign x e) env
  -- ... other constructors ...

-- Macro to mimic the notation ⟨L; E; G⟩  ⊢ s ⤳ ⟨L'; E'; G'⟩
macro "typecheck_stmt_macro" env:term "⊢" s:term "⤳" env':term : term =>
  `(typecheck_stmt $env $s $env')

/- ---------------------------------------------------- -/
/-    Simple theorems about the typing relations        -/
/- ---------------------------------------------------- -/

/-
A well-typed statement in an empty site and path environments,
   produces a path environment that only has sites for variables, but not temporaries
-/

-- TODO: theorem stating that typecheck_usage does no introduce duplicate sites
-- and that it only increases the domain of the path environment


/- typecheck_usage preserves  the uniqueness of
   sites in the site environment -/

/- theorem typecheck_usage_unique_sites : ∀ env env' u s τ,
  typecheck_usage env u env' s τ →
  uniqueKeys env.alocEnv →
  uniqueKeys env'.alocEnv := by
  move=> env env' u s τ; scase
  { -- case t_umove
    move=>env x r H1 -> H3 //==
    sby apply notIn_uniqueKeys_insert
  }
  { -- case t_ucopy
    move=>x ms r H1 H2 -> H3 //==
    sby apply notIn_uniqueKeys_insert
  }
  { -- case t_uborrowImm
    move=>s x τ r  H1 H2 -> H3 /=
    sby apply notIn_uniqueKeys_insert
  }
  { --case t_uborrowMut
    move=>s x τ r  H1 H2 -> H4 /=
    sby apply notIn_uniqueKeys_insert
  }
 -/


end LeanMove.Checker
