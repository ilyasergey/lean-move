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
import LeanMove.Checker.TypeChecking

/-!
# Auxiliary Type Checking Definitions

This file contains definitions that are **not necessary** for the main
`typecheck_fun` relation but may be useful for:
- Algorithmic type checking (decidable checking)
- Alternative specifications
- Soundness proofs connecting algorithmic to relational specs

## Contents
- `typecheck_usage` - Relational typing for usages (inlined into `typecheck_stmt`)
- `not_borrowed_bool` - Boolean version of `not_borrowed` for algorithmic checking
- `check_usage` - Algorithmic version of `typecheck_usage`
- `typecheck_expr` - Relational typing for expressions (inlined into `typecheck_stmt`)
- `check_expr` - Algorithmic version of `typecheck_expr`

These definitions were moved here to keep `TypeChecking.lean` focused on
the core relational specification needed for `typecheck_fun`.
-/

namespace LeanMove.Checker

open Lang
open Lang.MoveLight
open AssocMap
open Regex

/- ---------------------------------------------------- -/
/-       Relational specs (inlined into typecheck_stmt) -/
/- ---------------------------------------------------- -/

/--
Type checking relation for variable usages.

**Note:** This relation is **not used** by `typecheck_stmt` - all usage
typing rules have been inlined directly into `typecheck_stmt` constructors
(e.g., `let_bind_move`, `let_bind_borrowImm`, `var_assign_valid`, etc.).

This relation is kept for:
- Documentation purposes
- Potential use in soundness proofs
- Alternative specification style

Judgment form: `⟨env⟩ ⊢ u ⤳ ⟨env'⟩; a : τ`

This relation handles four kinds of variable usages in A-Normal Form:
- **move x**: Transfers ownership of variable x to a new site, invalidating x
- **copy x**: Creates a copy of x's value at a new site, preserving x
- **&x** (borrowImm): Creates an immutable reference to x
- **&mut x** (borrowMut): Creates a mutable reference to x
-/
inductive typecheck_usage : TypeEnv → Usage → TypeEnv → Site -> MoveType → Prop where
  | t_umove : ∀ env env' x τ ms a,
     AssocMap.lookup env.varEnv x = some (.validVar, τ, ms) →
     not_borrowed x env →
     notIn env.siteEnv a →
     env' = { env with varEnv  := update env.varEnv x (.invalidVar, τ, ms)
                       siteEnv := insert env.siteEnv a τ } →
     typecheck_usage env (.move x) env' a τ

  -- Copying a variable value, not a reference
  | t_ucopy_val : ∀ env env' x bt ms a,
     AssocMap.lookup env.varEnv x = some (.validVar, .basic bt, ms) →
     notIn env.siteEnv a →
     env' = { env with siteEnv := insert env.siteEnv a (.basic bt)} →
     typecheck_usage env (.copy x) env' a (.basic bt)

  -- Copying a reference value
  | t_ucopy_ref : ∀ env env' x τ ms a (s t: Aref) isBor,
     AssocMap.lookup env.varEnv x = some (.validVar, .ref τ s isBor, ms) →
     notIn env.siteEnv a →
     freshRefBool t env.pathEnv →
     env' = { env with siteEnv := insert env.siteEnv a (.ref τ t isBor)
                       pathEnv := update_with_epsilon s t env.pathEnv } →
     typecheck_usage env (.copy x) env' a (.ref τ t isBor)

  -- Borrowing the reference to a variable's content, makes a new reference r
  | t_uborrowImm_val : ∀ env env' x τ ms a (r: Aref),
     AssocMap.lookup env.varEnv x = some (.validVar, .basic τ, ms) →
     AssocMap.notIn env.siteEnv a →
     freshRefBool r env.pathEnv →
     env' = { env with siteEnv := insert env.siteEnv a (.ref τ r .siteBorrowImm)
                       pathEnv := update_with_epsilon r r env.pathEnv |>
                                  update_with_extension .root r [.root_to_var x] } →
     typecheck_usage env (.borrowImm x) env' a (.ref τ r .siteBorrowImm)

  -- Mutable borrow to a value
  | t_uborrowMut_val : ∀ env env' x τ ms a (r: Aref),
     LE.le .mutable ms  →
     AssocMap.lookup env.varEnv x = some (.validVar, .basic τ, ms) →
     AssocMap.notIn env.siteEnv a →
     freshRefBool r env.pathEnv →
     env' = { env with siteEnv := insert env.siteEnv a (.ref τ r (.siteBorrowMut))
                       pathEnv := update_with_epsilon r r env.pathEnv |>
                                  update_with_extension .root r [.root_to_var x]  } →
     typecheck_usage env (.borrowMut x) env' a (.ref τ r .siteBorrowMut)

/- ---------------------------------------------------- -/
/-       Algorithmic helpers (not needed for typecheck_fun) -/
/- ---------------------------------------------------- -/

/-- Boolean version of not_borrowed for algorithmic type checking.
    Checks only refs in pathEnv.refs (the live references). -/
def not_borrowed_bool (x: Var) (env: TypeEnv) : Bool :=
  env.pathEnv.refs.all fun r =>
    let regex := env.pathEnv.paths (.root, r)
    -- Check that the regex does not accept the single-element path [root_to_var x]
    -- For common regex forms, we can check this directly
    match regex with
    | .empty => true  -- empty regex accepts nothing
    | .ε => true      -- ε only accepts [], not [root_to_var x]
    | .char c => c != .root_to_var x  -- char c accepts [c], check it's not our path
    | _ => false  -- Conservative: for complex regexes, assume borrowed

/--
Algorithmic version of typecheck_usage.

Given an input environment `env`, a usage `u`, a destination site `a`, and an expected type `τ`,
returns `some env'` if the usage type checks with the given parameters, `none` otherwise.
-/
def check_usage (env : TypeEnv) (u : Usage) (a : Site) (τ : MoveType) : Option TypeEnv :=
  if ¬notIn env.siteEnv a then none
  else match u with
  | .move x =>
    match lookup env.varEnv x with
    | some (.validVar, τ', ms) =>
      if τ' = τ then
        if not_borrowed_bool x env then
          some { env with varEnv  := update env.varEnv x (.invalidVar, τ, ms)
                          siteEnv := insert env.siteEnv a τ }
        else none
      else none
    | _ => none
  | .copy x =>
    match lookup env.varEnv x with
    | some (.validVar, .basic bt, _) =>
      if τ = .basic bt then
        some { env with siteEnv := insert env.siteEnv a (.basic bt)}
      else none
    | some (.validVar, .ref innerτ s isBor, _) =>
      match τ with
      | .ref innerτ' t isBor' =>
        if innerτ = innerτ' ∧ isBor = isBor' ∧ freshRefBool t env.pathEnv then
          some { env with siteEnv := insert env.siteEnv a (.ref innerτ t isBor)
                          pathEnv := update_with_epsilon s t env.pathEnv }
        else none
      | _ => none
    | _ => none
  | .borrowImm x =>
    match lookup env.varEnv x with
    | some (.validVar, .basic bt, _) =>
      match τ with
      | .ref bt' r .siteBorrowImm =>
        if bt = bt' ∧ freshRefBool r env.pathEnv then
          some { env with siteEnv := insert env.siteEnv a (.ref bt r .siteBorrowImm)
                          pathEnv := update_with_epsilon r r env.pathEnv |>
                                     update_with_extension .root r [.root_to_var x] }
        else none
      | _ => none
    | _ => none
  | .borrowMut x =>
    match lookup env.varEnv x with
    | some (.validVar, .basic bt, .mutable) =>
      match τ with
      | .ref bt' r .siteBorrowMut =>
        if bt = bt' ∧ freshRefBool r env.pathEnv then
          some { env with siteEnv := insert env.siteEnv a (.ref bt r .siteBorrowMut)
                          pathEnv := update_with_epsilon r r env.pathEnv |>
                                     update_with_extension .root r [.root_to_var x] }
        else none
      | _ => none
    | _ => none

/- ---------------------------------------------------- -/
/-       Relational expression typing (inlined into typecheck_stmt) -/
/- ---------------------------------------------------- -/

/--
Type checking relation for expressions in A-Normal Form.

**Note:** This relation is **not used** by `typecheck_stmt` - all expression
typing rules have been inlined directly into `typecheck_stmt` constructors
(e.g., `let_bind_move`, `let_bind_borrowImm`, etc.).

This relation is kept for:
- Documentation purposes
- Potential use in soundness proofs
- Alternative specification style

Judgment form: `⟨env⟩ ⊢ e ⤳ ⟨env'⟩; a : τ`
-/
inductive typecheck_expr : TypeEnv → Expr → TypeEnv → Site → MoveType → Prop where

  -- c <- u (see above)
  -- Uses the algorithmic check_usage function; env' is computed, not given
  -- The not_borrowed check for move is now part of check_usage
  | usage : ∀ env u (c : Site) (τ : MoveType) env',
     check_usage env u c τ = some env' →
     typecheck_expr env (Expr.usage u) env' c τ

  -- c <- n (integer literal)
  | intLit : ∀ env env' (n : Nat) (c : Site),
     AssocMap.notIn env.siteEnv c →
     env' = {env with siteEnv := insert env.siteEnv c (.basic .u64)} →
     typecheck_expr env (Expr.intLit n) env' c (.basic .u64)

  -- af <- &a.T::f
  | borrowField : ∀ env env' a f af bt bt' isBor fentries s (rf : Aref),
     -- Site type is τ basic type
     AssocMap.lookup env.siteEnv a = some (.ref bt s isBor) →
     -- This is a record type, here are its entries
     bt = .trecord fentries →
     -- Get the field type via the name f
     lookup fentries f = some bt' →
     AssocMap.notIn env.siteEnv af →
     freshRef rf env.pathEnv →
     -- Update site environment with the new reference
     env' = {env with siteEnv := insert (delete env.siteEnv a) af (.ref bt' rf isBor)
                      pathEnv := update_with_extension s rf [.field f] env.pathEnv  } →
     typecheck_expr env (Expr.borrowField a bt f) env' af (.ref bt' rf isBor)

  -- &mut af <- a.T::f
  | borrowMutField : ∀ env env' a f af bt btf fentries (s rf : Aref),
     -- Site type is τ basic type
     AssocMap.lookup env.siteEnv a = some (.ref bt s .siteBorrowMut) →
     -- This is a record type, here are its entries
     bt = .trecord fentries →
     -- Get the field type via the name f
     lookup fentries f = some btf →
     AssocMap.notIn env.siteEnv af →
     freshRef rf env.pathEnv →
     -- Update site environment with the new reference
     env' = {env with siteEnv := insert (delete env.siteEnv a) af (.ref btf rf .siteBorrowMut)
                      pathEnv := update_with_extension s rf [.field f] env.pathEnv } →
     typecheck_expr env (Expr.borrowMutField a bt f) env' af (.ref btf rf .siteBorrowMut)

  -- c <- a ⊕ b
  | binop : ∀ env env' bop bt1 bt2 bt3 (a b c : Site),
     AssocMap.lookup env.siteEnv a = some (.basic bt1) →
     AssocMap.lookup env.siteEnv b = some (.basic bt2) →
     binop_type bop bt1 bt2 = some bt3 →
     AssocMap.notIn env.siteEnv c →
     env' = {env with siteEnv := insert (delete (delete env.siteEnv a) b) c (.basic bt3)} ->
     typecheck_expr env (Expr.binop bop a b) env' c (.basic bt3)

  -- c <- *a
  | readRef : ∀ env env' (a c : Site) r (τ : BasicMoveType) isBor,
     AssocMap.lookup env.siteEnv a = some (.ref τ r isBor) →
     AssocMap.notIn env.siteEnv c →
     env' = {env with siteEnv := insert (delete env.siteEnv a) c (.basic τ)
                      pathEnv := delete_ref_node env.pathEnv r } →
     typecheck_expr env (Expr.readRef a) env' c (.basic τ)

  -- c <- freeze a
  | freeze : ∀ env env' a c (τ : BasicMoveType) (r r': Aref) isBor,
    -- Freeze converts a reference to immutable, consuming the old reference
    AssocMap.lookup env.siteEnv a = some (.ref τ r isBor) →
    AssocMap.notIn env.siteEnv c →
    freshRef r' env.pathEnv →
    -- Old reference r is consumed; new reference r' inherits r's incoming edges
    env' = {env with siteEnv := insert (delete env.siteEnv a) c (.ref τ r' .siteBorrowImm)
                     pathEnv := consume_ref_transfer env.pathEnv r r' } →
    typecheck_expr env (Expr.freeze a) env' c (.ref τ r' .siteBorrowImm)

  -- b <-- T { f1: a1, ..., fn: an }
  -- Creates a record by consuming field values from sites
  | pack : ∀ env env' (recName : Id) (fields : List (Field × Site)) (b : Site) (fentries : AssocMap Field BasicMoveType),
     -- b must be fresh
     AssocMap.notIn env.siteEnv b →
     -- Check that all field sites exist and have the correct types
     -- For each (f, a) pair, the site a must have type matching fentries[f]
     (∀ (f : Field) (a : Site), (f, a) ∈ fields →
       ∃ (bt : BasicMoveType), AssocMap.lookup env.siteEnv a = some (.basic bt) ∧
                               AssocMap.lookup fentries f = some bt) →
     -- All field sites must be distinct (no aliasing)
     (∀ a₁ a₂, (∃ f₁ f₂, (f₁, a₁) ∈ fields ∧ (f₂, a₂) ∈ fields ∧ f₁ ≠ f₂) → a₁ ≠ a₂) →
     -- Environment update: remove all field sites, add b with record type
     env' = {env with siteEnv := insert (deleteAll env.siteEnv (fields.map Prod.snd)) b (.basic (.trecord fentries))} →
     typecheck_expr env (Expr.pack recName fields) env' b (.basic (.trecord fentries))


/--
Algorithmic version of typecheck_expr.

Given an input environment `env`, an expression `e`, and a destination site `c`,
returns `some (τ, env')` where τ is the type and env' is the updated environment,
or `none` if the expression doesn't type check.

**Note:** This function is **not used** by `typecheck_stmt` - all expression
checking is done directly through the `let_bind_*` constructors.

This function is kept for potential use in:
- Algorithmic type checking implementations
- Soundness proofs
-/
def check_expr (env : TypeEnv) (e : Expr) (c : Site) : Option (MoveType × TypeEnv) :=
  match e with
  | .usage u =>
    -- Try each possible type form that check_usage could produce
    -- For move/copy/borrow, we need to infer the type from the variable lookup
    match u with
    | .move x =>
      match AssocMap.lookup env.varEnv x with
      | some (.validVar, τ, ms) =>
        if ¬notIn env.siteEnv c then none
        else if ¬not_borrowed_bool x env then none
        else some (τ, { env with varEnv  := update env.varEnv x (.invalidVar, τ, ms)
                                 siteEnv := insert env.siteEnv c τ })
      | _ => none
    | .copy x =>
      match AssocMap.lookup env.varEnv x with
      | some (.validVar, .basic bt, _) =>
        if ¬notIn env.siteEnv c then none
        else some (.basic bt, { env with siteEnv := insert env.siteEnv c (.basic bt) })
      | some (.validVar, .ref innerτ s isBor, _) =>
        if ¬notIn env.siteEnv c then none
        else
          let t := nextFreshRef env.pathEnv
          some (.ref innerτ t isBor, { env with siteEnv := insert env.siteEnv c (.ref innerτ t isBor)
                                                pathEnv := update_with_epsilon s t env.pathEnv })
      | _ => none
    | .borrowImm x =>
      match AssocMap.lookup env.varEnv x with
      | some (.validVar, .basic bt, _) =>
        if ¬notIn env.siteEnv c then none
        else
          let r := nextFreshRef env.pathEnv
          some (.ref bt r .siteBorrowImm, { env with siteEnv := insert env.siteEnv c (.ref bt r .siteBorrowImm)
                                                     pathEnv := update_with_epsilon r r env.pathEnv |>
                                                                update_with_extension .root r [.root_to_var x] })
      | _ => none
    | .borrowMut x =>
      match AssocMap.lookup env.varEnv x with
      | some (.validVar, .basic bt, .mutable) =>
        if ¬notIn env.siteEnv c then none
        else
          let r := nextFreshRef env.pathEnv
          some (.ref bt r .siteBorrowMut, { env with siteEnv := insert env.siteEnv c (.ref bt r .siteBorrowMut)
                                                     pathEnv := update_with_epsilon r r env.pathEnv |>
                                                                update_with_extension .root r [.root_to_var x] })
      | _ => none

  | .intLit _ =>
    if ¬notIn env.siteEnv c then none
    else some (.basic .u64, { env with siteEnv := insert env.siteEnv c (.basic .u64) })

  | .borrowField a bt f =>
    match AssocMap.lookup env.siteEnv a with
    | some (.ref bt' s isBor) =>
      if ¬(BasicMoveType.beq bt bt') then none
      else match bt with
      | .trecord fentries =>
        match lookup fentries f with
        | some btf =>
          if ¬notIn env.siteEnv c then none
          else
            let rf := nextFreshRef env.pathEnv
            some (.ref btf rf isBor, { env with siteEnv := insert (delete env.siteEnv a) c (.ref btf rf isBor)
                                                pathEnv := update_with_extension s rf [.field f] env.pathEnv })
        | none => none
      | _ => none
    | _ => none

  | .borrowMutField a bt f =>
    match AssocMap.lookup env.siteEnv a with
    | some (.ref bt' s .siteBorrowMut) =>
      if ¬(BasicMoveType.beq bt bt') then none
      else match bt with
      | .trecord fentries =>
        match lookup fentries f with
        | some btf =>
          if ¬notIn env.siteEnv c then none
          else
            let rf := nextFreshRef env.pathEnv
            some (.ref btf rf .siteBorrowMut, { env with siteEnv := insert (delete env.siteEnv a) c (.ref btf rf .siteBorrowMut)
                                                         pathEnv := update_with_extension s rf [.field f] env.pathEnv })
        | none => none
      | _ => none
    | _ => none

  | .binop bop a b =>
    match AssocMap.lookup env.siteEnv a, AssocMap.lookup env.siteEnv b with
    | some (.basic bt1), some (.basic bt2) =>
      match binop_type bop bt1 bt2 with
      | some bt3 =>
        if ¬notIn env.siteEnv c then none
        else some (.basic bt3, { env with siteEnv := insert (delete (delete env.siteEnv a) b) c (.basic bt3) })
      | none => none
    | _, _ => none

  | .readRef a =>
    match AssocMap.lookup env.siteEnv a with
    | some (.ref τ r _) =>
      if ¬notIn env.siteEnv c then none
      else some (.basic τ, { env with siteEnv := insert (delete env.siteEnv a) c (.basic τ)
                                      pathEnv := delete_ref_node env.pathEnv r })
    | _ => none

  | .freeze a =>
    match AssocMap.lookup env.siteEnv a with
    | some (.ref τ r _) =>
      if ¬notIn env.siteEnv c then none
      else
        let r' := nextFreshRef env.pathEnv
        some (.ref τ r' .siteBorrowImm, { env with siteEnv := insert (delete env.siteEnv a) c (.ref τ r' .siteBorrowImm)
                                                   pathEnv := consume_ref_transfer env.pathEnv r r' })
    | _ => none

  | .pack _ _ =>
    -- Pack expressions require complex field type checking that is handled
    -- by the relational typecheck_expr.pack constructor.
    -- The algorithmic version conservatively returns none.
    none

-- Notation macros for auxiliary type checking relations

-- Usage: ⟨Γ⟩ ⊢ u ⤳ ⟨Γ'⟩ @ a : τ
-- Meaning: typecheck_usage Γ u Γ' a τ
macro "⟨" env:term "⟩" " ⊢ᵤ " u:term " ⤳ " "⟨" env':term "⟩" " @ " a:term " : " τ:term : term =>
  `(typecheck_usage $env $u $env' $a $τ)

-- Expression: ⟨Γ⟩ ⊢ e ⤳ ⟨Γ'⟩ @ a : τ
-- Meaning: typecheck_expr Γ e Γ' a τ
macro "⟨" env:term "⟩" " ⊢ₑ " e:term " ⤳ " "⟨" env':term "⟩" " @ " a:term " : " τ:term : term =>
  `(typecheck_expr $env $e $env' $a $τ)

end LeanMove.Checker
