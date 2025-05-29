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

-- Environment mapping sites to their types
abbrev SiteEnv := AssocMap Site MoveType

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

-- Whether the variable is borrowed or not
inductive Borrow where
  | borrowed
  | notBorrowed
deriving Repr, DecidableEq, Inhabited, Hashable

instance : Ord Borrow where
  compare a b := match a, b with
    | .borrowed, .notBorrowed => .lt
    | .notBorrowed, .borrowed => .gt
    | .borrowed, .borrowed => .eq
    | .notBorrowed, .notBorrowed => .eq

-- Environment mapping variables to their types
abbrev VarEnv := AssocMap Var (Site × MoveType × Mut)

-- Environment mapping pairs of sites to sets regular expressions
abbrev PathSet := Regex Field → Prop
abbrev PathEnv := (Site × Site) → PathSet

-- New structure packaging all environments
structure TypeEnv where
  siteEnv : SiteEnv
  varEnv : VarEnv
  pathEnv : PathEnv

/- ---------------------------------------------------- -/
/- Typing relations for usages, expressions, statements -/
/- ---------------------------------------------------- -/

-- TODO: track borrowed status of the variables in varEnv

-- relation L; E; R ⊢ u ⤳ L'; R'; τ for the type Usage
inductive typecheck_usage : TypeEnv → Usage → TypeEnv → MoveType → Prop where
   -- Move the site for the variable to siteEnv, purge it from varEnv
  | t_umove : ∀ env env' x s τ bk,
     AssocMap.lookup env.varEnv x = some (s, τ, bk) →
     env' = { env with siteEnv := AssocMap.insert env.siteEnv s τ,
                       varEnv  := AssocMap.delete env.varEnv x } →
     typecheck_usage env (.copy x) env' τ
-- Copying: make a new site for the copied variable, no not delete the old one
  | t_ucopy : ∀ env env' x τ bk,
     AssocMap.lookup env.varEnv x = some (varsite, τ, bk) →
     varsite = ⟨.svar sid, i⟩ →
     env' = { env with siteEnv := AssocMap.insert env.siteEnv (Site.mk (.svar sid) (i + 1)) τ} →
     typecheck_usage env (.copy x) env' τ
  | t_uborrow : ∀ env x s τ bk,
     AssocMap.lookup env.varEnv x = some (s, τ, bk) →
     typecheck_usage env (.borrow x) env τ
  | t_uborrowMut : ∀ env x s τ bk,
     AssocMap.lookup env.varEnv x = some (s, τ, bk) →
     typecheck_usage env (.borrowMut x) env τ

-- Inductive relation ⟨L; E; R⟩ ⊢ (e : expr) ⤳ ⟨L'; E'; R'⟩
inductive typecheck_expr : TypeEnv → Expr → TypeEnv → MoveType → Prop where
  | usage : ∀ env u τ,
     typecheck_usage env u env τ ->
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
