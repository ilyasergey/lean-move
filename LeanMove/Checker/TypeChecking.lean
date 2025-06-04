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

import LeanMove.Lang
import LeanMove.Structures.PathMap
import LeanMove.Structures.AssocMap

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

-- Environment mapping variables to their site, types, mutability, and borrow status
abbrev VarEnv := AssocMap Var (Site × MoveType × Mut × VarBorrowStatus)

-- Environment mapping sites to their types and borrow marker
abbrev SiteEnv := AssocMap Site (MoveType × SiteIsBorrowing)

-- Environment mapping pairs of sites to sets regular expressions
abbrev PathSet := Regex Field → Prop
abbrev PathEnv := (Site × Site) → PathSet

-- Update an instance of PathEnv with a new pair of sites and a regex
def update_path_env (env : PathEnv) (s1 s2 : Site) (re : Regex Field) : PathEnv :=
  fun (s1', s2') re' => if s1' = s1 && s2' = s2
      -- TODO: revise this to use transitive closure of the regex
      then re' = re ∨ env (s1, s2) re'
      else env (s1', s2') re'

-- New structure packaging all environments
structure TypeEnv where
  siteEnv : SiteEnv
  varEnv  : VarEnv
  pathEnv : PathEnv

/- ---------------------------------------------------- -/
/-       Well-formedness of the environments            -/
/- ---------------------------------------------------- -/

structure WellFormedEnv (typeEnv : TypeEnv) where
  -- All variable names are unique
  uniqueVarSite : uniqueKeys typeEnv.varEnv
  -- All entries in varEnv have consistent entries in siteEnv
  -- TODO
  -- All keys in sitesEnv are unique
  uniqueSites : uniqueKeys typeEnv.siteEnv
  -- TODO: say that for all pairs in pathEnv there is either
  -- a variable in varEnv or a site in siteEnv

/- ---------------------------------------------------- -/
/- Typing relations for usages, expressions, statements -/
/- ---------------------------------------------------- -/

-- TODO: track borrowed status of the variables in varEnv

open AssocMap

-- relation L; E; R ⊢ u ⤳ L'; E'; R'; Site; τ for the type Usage
inductive typecheck_usage : TypeEnv → Usage → TypeEnv → Site -> MoveType → Prop where

  /- Moving the contents of the variable to a new site, purge it from varEnv -/
  | t_umove : ∀ env env' x s τ ms,
     -- Can only move from non-borrowed variables
     AssocMap.lookup env.varEnv x = some (s, τ, ms, varNotBorrowed) →
     env' = { env with varEnv  := delete env.varEnv x
                       siteEnv := insert env.siteEnv s (τ, .siteNotBorrowed) } →
     -- Note: R is not affected by this, as no new sites created
     typecheck_usage env (.copy x) env' s τ

  /- Copying: make a new site for the copied variable, no not delete the old one -/
  | t_ucopy : ∀ env env' x s τ ms newSite,
     AssocMap.lookup env.varEnv x = some (s, τ, ms, bs) →
     -- newSite is fresh
     AssocMap.notIn env.siteEnv newSite →
     -- VarEnv is not affected by this
     env' = { env with siteEnv := insert env.siteEnv newSite (τ, .siteNotBorrowed)} →
     -- Note: R is not affected by this, as no new sharing introduced
     typecheck_usage env (.copy x) env' newSite τ

  /- Borrowing the reference to a variable's payload -/
  | t_uborrowImm : ∀ env x τ ms bs newSite,
     AssocMap.lookup env.varEnv x = some (s, τ, ms, bs) →
     LE.le bs .varBorrowedImm → -- Borrow status: either unborrowed or immutable borrowed
     -- newSite is fresh
     AssocMap.notIn env.siteEnv newSite →
     -- The variable site s is now reachable from newSite via epsilon-transition
     env' = { env with varEnv :=  update env.varEnv x (s, τ, ms, .varBorrowedImm),
                       siteEnv := AssocMap.insert env.siteEnv newSite (.ref τ, .siteBorrowImm x),
                       pathEnv := update_path_env env.pathEnv newSite s Regex.epsilon } → -- TODO: is this correct?
     typecheck_usage env (.borrowImm x) env newSite (.ref τ)

  /- Mutably borrowing the reference to a variable's payload -/
  | t_uborrowMut : ∀ env x s τ ms bs newSite,
     AssocMap.lookup env.varEnv x = some (s, τ, ms, bs) →
     LE.le bs .varNotBorrowed   → -- Borrow status: must be unborrowed
     LE.le .mutable ms  →     -- Can only mutably borrow if the variable is mutable
     -- newSite is fresh
     AssocMap.notIn env.siteEnv newSite →
     -- Change the status of the variable and add new reachability
     -- The variable site s is now reachable from newSite via epsilon-transition
     env' = { env with varEnv :=  update env.varEnv x (s, τ, ms, .varBorrowedMut)
                       siteEnv := AssocMap.insert env.siteEnv newSite (.ref τ, .siteBorrowMut x)
                       pathEnv := update_path_env env.pathEnv newSite s Regex.epsilon } → -- TODO: is this correct?
     typecheck_usage env (.borrowMut x) env newSite τ

/-
Questions (29 May 2025):
* [Q] Should we update the R as a result of the last two clauses (borrowImm and borrowMut)?
* [Q] What is the difference between two sites beling aliases and one being reachable from the other via dereference?
 -/



-- TODO: theorem stating that typecheck_usage does no introduce duplicate sites
-- and that it only increases the domain of the path environment



/- ---------------------------------------------------- -/
/- Typing relations for expressions -/
/- ---------------------------------------------------- -/

-- ⟨L; E; R⟩ ⊢ (e : expr) ⤳ ⟨L'; E'; R'⟩
inductive typecheck_expr : TypeEnv → Expr → TypeEnv → Site → MoveType → Prop where
  | usage : ∀ env env' u s τ,
     typecheck_usage env u env' s τ ->
     typecheck_expr env (Expr.usage u) env s τ
  | borrowField : ∀ env s a f s',
     typecheck_expr env (Expr.borrowField s a f) env s' TInt
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

-- Macro to mimic the notation ⟨L; E; R⟩  ⊢ s ⤳ ⟨L'; E'; R'⟩
macro "typecheck_stmt_macro" env:term "⊢" s:term "⤳" env':term : term =>
  `(typecheck_stmt $env $s $env')

/- ---------------------------------------------------- -/
/-    Simple theorems about the typing relations        -/
/- ---------------------------------------------------- -/

/-
A well-typed statement in an empty site and path environments,
   produces a path environment that only has sites for variables, but not temporaries
-/

end LeanMove.Checker
