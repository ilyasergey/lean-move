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

import LeanMove.Structures.PathMap
import LeanMove.Structures.AssocMap
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


-- Environment mapping pairs of sites to sets regular expressions
abbrev PathSet := Regex Field → Prop
structure GraphEnv where
  refs : List Aref
  paths: (Aref × Aref) → PathSet

-- Update an instance of PathEnv with a new pair of sites and a regex
-- def update_path_env (env : GraphEnv) (s1 s2 : Aref) (re : Regex Field) : GraphEnv :=
--   fun (s1', s2') re' => if s1' = s1 && s2' = s2
--       -- TODO: revise this to use transitive closure of the regex
--       then re' = re ∨ env (s1, s2) re'
--       else env (s1', s2') re'

-- New structure packaging all environments
structure TypeEnv where
  alocEnv : AlocEnv
  varEnv  : VarEnv
  graphEnv : GraphEnv

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
     env' = { env with varEnv  := update varEnv x (.invalidVar, τ, ms)
                       alocEnv := insert env.alocEnv a (τ, .siteNotBorrowed) } →
     -- TODO: handle G
     typecheck_usage env (.move x) env' a τ

  -- Copying a variable value, r is an abstract reference, optional
  -- TODO: Handle r for the case when τ is a reference type
  | t_ucopy : ∀ env env' x τ ms a (r: Aref),
     AssocMap.lookup env.varEnv x = some (.validVar, τ, ms) →
     -- newSite is fresh
     notIn env.alocEnv a →
     -- VarEnv is not affected by this
     env' = { env with alocEnv := insert env.alocEnv a (with_new_ref τ r, .siteNotBorrowed)} →
     -- TODO: handle G
     typecheck_usage env (.copy x) env' a τ

  -- Borrowing the reference to a variable's content, makes a new reference r
  | t_uborrowImm : ∀ env x τ ms a (r : Aref),
     AssocMap.lookup env.varEnv x = some (.validVar, τ, ms) →
     -- newSite is fresh
     AssocMap.notIn env.alocEnv a →
     -- The variable site s is now reachable from newSite via epsilon-transition
     -- TODO: handle G
     env' = { env with alocEnv := insert env.alocEnv a (.ref τ r, .siteBorrowImm x) } →
     typecheck_usage env (.borrowImm x) env' a (.ref τ r)

  /- Mutably borrowing the reference to a variable's payload -/
  | t_uborrowMut : ∀ env x τ ms a r,
     AssocMap.lookup env.varEnv x = some (.validVar, τ, ms) →
     LE.le .mutable ms  →     -- Can only mutably borrow if the variable is mutable
     -- newSite is fresh
     AssocMap.notIn env.alocEnv a →
     -- Change the status of the variable and add new reachability
     -- The variable site s is now reachable from newSite via epsilon-transition
     -- TODO: handle G
     env' = { env with alocEnv := AssocMap.insert env.alocEnv a (.ref τ r, .siteBorrowMut x) } →
     typecheck_usage env (.borrowMut x) env' a τ

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
theorem typecheck_usage_unique_sites : ∀ env env' u s τ,
  typecheck_usage env u env' s τ →
  uniqueKeys env.alocEnv →
  uniqueKeys env'.alocEnv := by
  move=> env env' u s τ; scase
  { -- case t_umove
    move=>env x ms r H1 -> H3 //==
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



end LeanMove.Checker
