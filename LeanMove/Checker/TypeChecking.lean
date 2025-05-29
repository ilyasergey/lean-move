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
  | borrowedImm
  | borrowedMut
  | notBorrowed
deriving Repr, DecidableEq, Inhabited, Hashable

instance : LE VarBorrowStatus where
  le a b := match a, b with
    | .notBorrowed, _ => true
    | _, .notBorrowed => false
    | .borrowedImm, .borrowedMut => true
    | .borrowedMut, .borrowedImm => false
    | .borrowedImm, .borrowedImm => true
    | .borrowedMut, .borrowedMut => true

-- Environment mapping sites to their types and borrow marker
abbrev SiteEnv := AssocMap Site (MoveType × VarBorrowStatus)

-- Environment mapping variables to their site, types, mutability, and borrow status
abbrev VarEnv := AssocMap Var (Site × MoveType × Mut × VarBorrowStatus)

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
  varEnv : VarEnv
  pathEnv : PathEnv

/- ---------------------------------------------------- -/
/- Typing relations for usages, expressions, statements -/
/- ---------------------------------------------------- -/

-- TODO: track borrowed status of the variables in varEnv

open AssocMap

-- relation L; E; R ⊢ u ⤳ L'; R'; τ for the type Usage

-- [Q] TODO: should we update the R as a result of the last two clauses (borrowImm and borrowMut)?

inductive typecheck_usage : TypeEnv → Usage → TypeEnv → MoveType → Prop where

  /- Moving the contents of the variable to a new site, purge it from varEnv -/
  | t_umove : ∀ env env' x s τ ms,
     -- Can only move from non-borrowed variables
     AssocMap.lookup env.varEnv x = some (s, τ, ms, .notBorrowed ) →
     env' = { env with siteEnv := insert env.siteEnv s (τ, .notBorrowed),
                       varEnv  := delete env.varEnv x } →
     -- Note: R is not affected by this, as no new sites created
     typecheck_usage env (.copy x) env' τ

  /- Copying: make a new site for the copied variable, no not delete the old one -/
  | t_ucopy : ∀ env env' x τ ms sid i,
     AssocMap.lookup env.varEnv x = some (varsite, τ, ms, _) →
     varsite = ⟨.svar sid, i⟩ →
     -- Should we make the site related to the variable or new temporary?
     env' = { env with siteEnv := insert env.siteEnv (.mk (.svar sid) (i + 1)) (τ, .notBorrowed)} →
     -- Note: R is not affected by this, as no new sharing introduced
     typecheck_usage env (.copy x) env' τ

  /- Borrowing the reference to a variable's payload -/
  | t_uborrowImm : ∀ env x τ ms bs sid i varSite newSite,
     AssocMap.lookup env.varEnv x = some (varSite, τ, ms, bs) →
     LE.le bs .borrowedImm → -- Borrow status: either unborrowed or immutable borrowed
     -- Change the status of the variable
     varSite = ⟨.svar sid, i⟩ →
     newSite = ⟨.svar sid, i + 1⟩ →
     -- varSite is now reachable from newSite via epsilon-transition
     env' = { env with varEnv := update env.varEnv x (s, τ, ms, .borrowedImm)
                       siteEnv := insert env.siteEnv newSite (.ref τ, .borrowedImm)
                       pathEnv := update_path_env env.pathEnv newSite varSite Regex.epsilon } →
     typecheck_usage env (.borrowImm x) env (.ref τ)

  /- Mutably borrowing the reference to a variable's payload -/
  | t_uborrowMut : ∀ env x s τ ms bs sid i varSite newSite,
     AssocMap.lookup env.varEnv x = some (varSite, τ, ms, bs) →
     LE.le bs .notBorrowed   → -- Borrow status: must be unborrowed
     LE.le .mutable ms  →     -- Can only mutably borrow if the variable is mutable
     varSite = ⟨.svar sid, i⟩ →
     newSite = ⟨.svar sid, i + 1⟩ →
     -- Change the status of the variable and add new reachability
     -- varSite is now reachable from newSite via epsilon-transition
     env' = { env with varEnv := update env.varEnv x (s, τ, ms, .borrowedMut)
                       siteEnv := insert env.siteEnv newSite (.ref τ, .borrowedMut)
                       pathEnv := update_path_env env.pathEnv newSite varSite Regex.epsilon } →
     typecheck_usage env (.borrowMut x) env τ


-- TODO: theorem stating that typecheck_usage does no introduce duplicate sites
-- and that it only increases the domain of the path environment



/- ---------------------------------------------------- -/
/- Typing relations for expressions -/
/- ---------------------------------------------------- -/

-- ⟨L; E; R⟩ ⊢ (e : expr) ⤳ ⟨L'; E'; R'⟩
inductive typecheck_expr : TypeEnv → Expr → TypeEnv → MoveType → Prop where
  | usage : ∀ env env' u τ,
     typecheck_usage env u env' τ ->
     typecheck_expr env (Expr.usage u) env τ
  | borrowField : ∀ env s a f,
     typecheck_expr env (Expr.borrowField s a f) env TInt
  | borrowMutField : ∀ env s a f,
     typecheck_expr env (Expr.borrowMutField s a f) env TInt
  | binop : ∀ env s1 s2,
     typecheck_expr env (Expr.binop s1 s2) env TInt
  | readRef : ∀ env s,
     typecheck_expr env (Expr.readRef s) env TInt
  | pack : ∀ env t fs,
     typecheck_expr env (Expr.pack t fs) env TInt

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
