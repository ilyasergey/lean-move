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
import LeanMove.Typing.Types

/-!
# Type Checking Rules for MoveLight

This file contains the typing relations for the MoveLight language.
Type environment definitions and auxiliary lemmas are in `Types.lean`.
-/

namespace LeanMove.Typing

open Lang
open Lang.MoveLight
open AssocMap
open Regex

/- ---------------------------------------------------- -/
/- Typing relations for usages, expressions, statements -/
/- ---------------------------------------------------- -/

open AssocMap


 -- Check that the variable x is not borrowed
 -- Implementation: walk the graph from the local root and check that no outbound edge
 -- starts with variable x (as discussed with Todd)
 def not_borrowed (x: Var) (env: TypeEnv) : Prop :=
  -- For x not to be borrowed, check all outbound edges from root
  -- and ensure none of them start with a path to x
  ∀ (r : Aref),
    let regex := env.pathEnv.paths (.root, r)
    -- The regex should not accept a path that starts with root_to_var x
    ¬ interpret_regex regex [.root_to_var x]

def all_fresh_sites (env: TypeEnv) (as: List Site) : Prop :=
  List.all as (fun a ↦ notIn env.siteEnv a)

/- ---------------------------------------------------- -/
/- Typing relations for expressions -/
/- ---------------------------------------------------- -/


-- function to take a binop and types of its arguments and return the type of the result
def binop_type (bop : Binop) (τ1 τ2 : BasicMoveType) : Option BasicMoveType :=
  match (bop, τ1, τ2) with
  | (.add, .u64, .u64) => some .u64
  | (.sub, .u64, .u64) => some .u64
  | (.mul, .u64, .u64) => some .u64
  | (.div, .u64, .u64) => some .u64
  | (.mod, .u64, .u64) => some .u64
  | (.lt,  .u64, .u64) => some .tbool
  | (.eq, .u64, .u64) =>  some .tbool
  | (.eq, .tbool, .tbool) => some .tbool
  | (.nand, .tbool, .tbool) => some .tbool
  | _ => none

-- Check that a list of sites conforms to a list of parameter types
-- No submtyping,
def types_conform (alocEnv : SiteEnv) (sites : List Site) (paramTypes : List ParamType) : Prop :=
  match sites, paramTypes with
  | [], [] => True
  | site :: sites', paramType :: paramTypes' =>
    match AssocMap.lookup alocEnv site with
    | some τ =>
      -- the formal is on the left, the actual is on the right
      match paramType, τ with
      | ⟨bt, none⟩, .basic bt' => bt = bt' ∧ types_conform alocEnv sites' paramTypes'
      | ⟨bt, some isRefMut⟩, .ref τ _ isBor =>
        bt = τ ∧
        (match isRefMut, isBor with
         | true, .siteBorrowMut => True -- only mutables here
         | false, .siteBorrowImm => True -- for immutable parameter referenes, the actual can be anything (mut/imm)
         | _, _ => False) ∧
        types_conform alocEnv sites' paramTypes'
      | _, _ => False
    -- Type is not found for the site
    | none => False
  -- Mismatch in sizes
  | _, _ => False

-- Helper for unpack: adds field sites to siteEnv based on record field types
def addFieldSites (fentries : AssocMap Field BasicMoveType) (se : AssocMap Site MoveType) (fields : List (Field × Site)) : AssocMap Site MoveType :=
  List.foldl (fun acc (fa : Field × Site) =>
    match AssocMap.lookup fentries fa.1 with
    | some bt => insert acc fa.2 (.basic bt)
    | none => acc) se fields

def call_connect_inputs_outputs (env: TypeEnv) (as bs: List Site) : TypeEnv :=
  -- Extract reference arefs from inputs (bs) and outputs (as)
  -- We only care about reference types; basic types are disregarded

  let inputs := List.filterMap (fun a ↦ match AssocMap.lookup env.siteEnv a with
    | some (.ref _ r _) => some r
    | _ => none) bs

  -- MI: All mutable inputs
  let mi := List.filterMap (fun a ↦ match AssocMap.lookup env.siteEnv a with
    | some (.ref _ r .siteBorrowMut) => some r
    | _ => none) bs

  -- MO: All mutable outputs
  let mo := List.filterMap (fun a ↦ match AssocMap.lookup env.siteEnv a with
    | some (.ref _ r .siteBorrowMut) => some r
    | _ => none) as

  -- IO: All immutable outputs
  let io := List.filterMap (fun a ↦ match AssocMap.lookup env.siteEnv a with
    | some (.ref _ r .siteBorrowImm) => some r
    | _ => none) as

  -- Rule 1: For any immutable output, it will be .*-extended from any input (mutable and immutable)
  let with_io_from_inputs : PathEnv := List.foldl (fun penv iout ↦
    List.foldl (fun penv' input ↦ extend_with_star input iout penv') penv inputs
  ) env.pathEnv io

  -- Rule 2: For any mutable output, it will be .*-extended from any mutable input only
  let with_mo_from_mi : PathEnv := List.foldl (fun penv mout ↦
    List.foldl (fun penv' minput ↦ extend_with_star minput mout penv') penv mi
  ) with_io_from_inputs mo

  -- Rule 3: Immutable outputs are .*-extended from each other
  -- For each pair (io1, io2) where io1 ≠ io2, add io1 →.* io2
  let with_io_to_io : PathEnv := List.foldl (fun penv io1 ↦
    List.foldl (fun penv' io2 ↦
      if io1 ≠ io2 then extend_with_star io1 io2 penv' else penv'
    ) penv io
  ) with_mo_from_mi io

  { env with pathEnv := with_io_to_io }

/-- Check that no mutable input reaches any other input.

    For each mutable input site mi_site with abstract reference mi_ref,
    and for every other input site other_site with reference other_ref,
    verify that the path regex from mi_ref to other_ref only matches the
    empty string (or nothing), i.e., there is no non-empty path between them.

    This ensures that mutable borrows passed to a function are properly isolated:
    no mutable input can alias or reach any other input parameter, preventing
    unexpected interference between function arguments.
-/
def check_mutable_inputs_isolated (env: TypeEnv) (bs: List Site) : Prop :=
  ∀ (mi_site : Site), mi_site ∈ bs →
    ∀ (mi_bt : BasicMoveType) (mi_ref : Aref),
      AssocMap.lookup env.siteEnv mi_site = some (.ref mi_bt mi_ref .siteBorrowMut) →
      ∀ (other_site : Site), other_site ∈ bs →
        ∀ (other_bt : BasicMoveType) (other_ref : Aref) (bk : BorrowingKind),
          AssocMap.lookup env.siteEnv other_site = some (.ref other_bt other_ref bk) →
          mi_site ≠ other_site →
            only_matches_empty (env.pathEnv.paths (mi_ref, other_ref))

/-- Check that all mutable inputs have non-trivial outbound edges.

    For each mutable input site mi_site with abstract reference mi_ref,
    verify that there exists at least one target reference that mi_ref reaches
    via a non-empty path in PathEnv (checked via `has_nonempty_match`).

    This ensures that mutable borrows passed to functions are "live" and have
    meaningful connections in the path graph (beyond just the trivial ε edge to itself).
    A mutable borrow without outbound edges would indicate it's not properly
    connected to the ownership structure.
-/
def check_mutable_inputs_have_outbound (env: TypeEnv) (bs: List Site) : Prop :=
  ∀ (mi_site : Site), mi_site ∈ bs →
    ∀ (mi_bt : BasicMoveType) (mi_ref : Aref),
      AssocMap.lookup env.siteEnv mi_site = some (.ref mi_bt mi_ref .siteBorrowMut) →
      ∃ (target : Aref), target ∈ env.pathEnv.refs ∧ mi_ref ≠ target ∧
        has_nonempty_match (env.pathEnv.paths (mi_ref, target))

/--
  Check that no local variables are currently borrowed.

  This is used in the return rule to ensure that:
  - No references to local variables escape the function
  - Return values must be bound through input parameters (or be vacuous for natives)
  - Handles the case of vacuous references from native functions

  Implementation: for each variable in varEnv, check that not_borrowed holds.
-/
def no_locals_borrowed (env: TypeEnv) : Prop :=
  ∀ (x : Var) (v : IsValid × MoveType × Mut), (x, v) ∈ env.varEnv.entries → not_borrowed x env

/--
Type checking relation for statements in continuation-passing style.

Judgment form: `Λ; ⟨Γ⟩ ⊢ s : τᵣ`

This relation handles all statement forms, including both:
- **Non-terminal statements** that transform the environment and continue to their continuation
- **Terminal statements** (skip, jump, branch, ret, abort) that end execution

Non-terminal statements take a continuation as their last argument and type check
by constructing the new environment and passing it to the continuation's type check.

Terminal statements:
- **skip**: No-op terminal (just ends)
- **jump L**: Unconditional jump to label L
- **branch a L1 L2**: Conditional branch based on boolean site a
- **ret [a1, ..., an]**: Return from function with values
- **abort a**: Abort execution (error path)

Non-terminal statements:
- **let a = e; cont**: Bind expression result to site, continue with updated env
- **x = a; cont**: Assign site value to variable, continue
- ***a = b; cont**: Write through mutable reference, continue
- **let (a1, ..., an) = f(b1, ..., bm); cont**: Function call, continue
- **T { f1: a1, ..., fn: an } = b; cont**: Unpack record, continue
- **release(a); cont**: Explicitly release a reference, continue

Components:
- `lenv`: Label environment mapping labels to expected entry TypeEnvs
- `env`: Input type environment before executing the statement
- `Stmt`: The statement being type checked
- `retType`: The function's return type (for ret checking)

Key environment transformations (passed to continuations):
⋆ **varEnv updates**: Assignments update variable bindings; moves invalidate variables
⋆ **siteEnv updates**: Sites are consumed by operations and new sites are produced
⋆ **PathEnv updates**:
  - Borrows add edges from root to references
  - Field accesses extend paths with field names
  - Function calls add conservative .*-extensions between inputs/outputs
  - Write operations check for dangling reference prevention (no outbound edges)
⋆ **Reference lifecycle**: Abstract references are allocated, tracked, and garbage collected

Linear resource tracking:
⋆ Sites represent linear resources that are consumed exactly once
⋆ Variables can be invalidated (moved) or preserved (copied/borrowed)
⋆ PathEnv tracks which variables are borrowed (via not_borrowed check)
-/
inductive typecheck_stmt : LabelEnv → TypeEnv → Stmt → MoveType → Prop where
  -- ==================== Terminal Statements ====================

  -- skip // No-op terminal
  | skip : ∀ (lenv : LabelEnv) (env : TypeEnv) retType,
      typecheck_stmt lenv env .skip retType

  -- jump L // Unconditional jump to label L
  -- The target label's environment subsumes the current environment
  -- (envL may be a join of multiple predecessors with wider paths)
  | jump : ∀ (lenv : LabelEnv) (env : TypeEnv) (L : Label) (envL : TypeEnv) retType,
      AssocMap.lookup lenv L = some envL →
      TypeEnv.subsumes envL env →
      typecheck_stmt lenv env (.jump L) retType

  -- branch a L1 L2 // If (a) goto L1 else goto L2
  -- Each target label's environment subsumes the post-branch environment
  | branch : ∀ (lenv : LabelEnv) (env : TypeEnv) (a : Site) (L1 L2 : Label) (envL1 envL2 : TypeEnv) retType,
      AssocMap.lookup env.siteEnv a = some (.basic .tbool) →
      AssocMap.lookup lenv L1 = some envL1 →
      AssocMap.lookup lenv L2 = some envL2 →
      TypeEnv.subsumes envL1 {env with siteEnv := delete env.siteEnv a} →
      TypeEnv.subsumes envL2 {env with siteEnv := delete env.siteEnv a} →
      typecheck_stmt lenv env (.branch a L1 L2) retType

  -- return (a1, ..., an) // Return from function
  -- Uses MoveType.compatible to compare return site types with the declared return type.
  -- This allows the checker to be agnostic to exact Aref refid values in declared types.
  | ret : ∀ (lenv : LabelEnv) (env : TypeEnv) (as : List Site) retType,
      (∀ a, a ∈ as → ∃ τ, AssocMap.lookup env.siteEnv a = some τ ∧ MoveType.compatible τ retType) →
      no_locals_borrowed env →
      typecheck_stmt lenv env (.ret as) retType

  -- abort a // Abort execution with error value
  | abort : ∀ (lenv : LabelEnv) (env : TypeEnv) (a : Site) τ retType,
      AssocMap.lookup env.siteEnv a = some τ →
      typecheck_stmt lenv env (.abort a) retType

  -- ==================== Non-terminal Statements ====================

  -- let a = move(x); cont
  | let_bind_move : ∀ (lenv : LabelEnv) (env : TypeEnv) (a : Site) x τ ms cont retType,
      lookup env.varEnv x = some (.validVar, τ, ms) →
      not_borrowed x env →
      notIn env.siteEnv a →
      typecheck_stmt lenv
        {env with varEnv := update env.varEnv x (.invalidVar, τ, ms)
                  siteEnv := insert env.siteEnv a τ}
        cont retType →
      typecheck_stmt lenv env (.letBind a (.usage (.move x)) cont) retType

  -- let a = copy(x); cont where x has basic type
  | let_bind_copy_val : ∀ (lenv : LabelEnv) (env : TypeEnv) (a : Site) x bt ms cont retType,
      lookup env.varEnv x = some (.validVar, .basic bt, ms) →
      notIn env.siteEnv a →
      typecheck_stmt lenv
        {env with siteEnv := insert env.siteEnv a (.basic bt)}
        cont retType →
      typecheck_stmt lenv env (.letBind a (.usage (.copy x)) cont) retType

  -- let a = copy(x); cont where x has reference type
  | let_bind_copy_ref : ∀ (lenv : LabelEnv) (env : TypeEnv) (a : Site) x τ ms (s t : Aref) isBor cont retType,
      lookup env.varEnv x = some (.validVar, .ref τ s isBor, ms) →
      notIn env.siteEnv a →
      freshRefInEnvBool t env →
      (∀ v, t ≠ .varRef v) →
      typecheck_stmt lenv
        {env with siteEnv := insert env.siteEnv a (.ref τ t isBor)
                  pathEnv := update_with_epsilon s t env.pathEnv}
        cont retType →
      typecheck_stmt lenv env (.letBind a (.usage (.copy x)) cont) retType

  -- let a = &x; cont (immutable borrow)
  | let_bind_borrowImm : ∀ (lenv : LabelEnv) (env : TypeEnv) (a : Site) x τ ms (r : Aref) cont retType,
      lookup env.varEnv x = some (.validVar, .basic τ, ms) →
      notIn env.siteEnv a →
      freshRefInEnvBool r env →
      (∀ v, r ≠ .varRef v) →
      typecheck_stmt lenv
        {env with siteEnv := insert env.siteEnv a (.ref τ r .siteBorrowImm)
                  pathEnv := update_with_epsilon r r env.pathEnv |>
                             update_with_extension r .root [.root_to_var x]}
        cont retType →
      typecheck_stmt lenv env (.letBind a (.usage (.borrowImm x)) cont) retType

  -- let a = &mut x; cont (mutable borrow)
  | let_bind_borrowMut : ∀ (lenv : LabelEnv) (env : TypeEnv) (a : Site) x τ ms (r : Aref) cont retType,
      LE.le .mutable ms →
      lookup env.varEnv x = some (.validVar, .basic τ, ms) →
      notIn env.siteEnv a →
      freshRefInEnvBool r env →
      (∀ v, r ≠ .varRef v) →
      typecheck_stmt lenv
        {env with siteEnv := insert env.siteEnv a (.ref τ r .siteBorrowMut)
                  pathEnv := update_with_epsilon r r env.pathEnv |>
                             update_with_extension r .root [.root_to_var x]}
        cont retType →
      typecheck_stmt lenv env (.letBind a (.usage (.borrowMut x)) cont) retType

  -- let a = n; cont (integer literal)
  | let_bind_intLit : ∀ (lenv : LabelEnv) (env : TypeEnv) (a : Site) (n : Nat) cont retType,
      notIn env.siteEnv a →
      typecheck_stmt lenv
        {env with siteEnv := insert env.siteEnv a (.basic .u64)}
        cont retType →
      typecheck_stmt lenv env (.letBind a (.intLit n) cont) retType

  -- let af = &a.T::f; cont (field borrow)
  | let_bind_borrowField : ∀ (lenv : LabelEnv) (env : TypeEnv) (a af : Site) f bt bt' isBor fentries s (rf : Aref) cont retType,
      lookup env.siteEnv a = some (.ref bt s isBor) →
      bt = .trecord fentries →
      lookup fentries f = some bt' →
      notIn env.siteEnv af →
      freshRefInEnv rf env →
      (∀ v, rf ≠ .varRef v) →
      typecheck_stmt lenv
        {env with siteEnv := insert (delete env.siteEnv a) af (.ref bt' rf isBor)
                  pathEnv := update_with_extension rf s [.field f] env.pathEnv}
        cont retType →
      typecheck_stmt lenv env (.letBind af (.borrowField a bt f) cont) retType

  -- let af = &mut a.T::f; cont (mutable field borrow)
  | let_bind_borrowMutField : ∀ (lenv : LabelEnv) (env : TypeEnv) (a af : Site) f bt btf fentries (s rf : Aref) cont retType,
      lookup env.siteEnv a = some (.ref bt s .siteBorrowMut) →
      bt = .trecord fentries →
      lookup fentries f = some btf →
      notIn env.siteEnv af →
      freshRefInEnv rf env →
      (∀ v, rf ≠ .varRef v) →
      typecheck_stmt lenv
        {env with siteEnv := insert (delete env.siteEnv a) af (.ref btf rf .siteBorrowMut)
                  pathEnv := update_with_extension rf s [.field f] env.pathEnv}
        cont retType →
      typecheck_stmt lenv env (.letBind af (.borrowMutField a bt f) cont) retType

  -- let c = a ⊕ b; cont (binary operation)
  | let_bind_binop : ∀ (lenv : LabelEnv) (env : TypeEnv) bop bt1 bt2 bt3 (a b c : Site) cont retType,
      lookup env.siteEnv a = some (.basic bt1) →
      lookup env.siteEnv b = some (.basic bt2) →
      binop_type bop bt1 bt2 = some bt3 →
      notIn env.siteEnv c →
      typecheck_stmt lenv
        {env with siteEnv := insert (delete (delete env.siteEnv a) b) c (.basic bt3)}
        cont retType →
      typecheck_stmt lenv env (.letBind c (.binop bop a b) cont) retType

  -- let c = *a; cont (dereference)
  | let_bind_readRef : ∀ (lenv : LabelEnv) (env : TypeEnv) (a c : Site) r (τ : BasicMoveType) isBor cont retType,
      lookup env.siteEnv a = some (.ref τ r isBor) →
      notIn env.siteEnv c →
      typecheck_stmt lenv
        {env with siteEnv := insert (delete env.siteEnv a) c (.basic τ)
                  pathEnv := delete_ref_node env.pathEnv r}
        cont retType →
      typecheck_stmt lenv env (.letBind c (.readRef a) cont) retType

  -- let c = freeze a; cont
  | let_bind_freeze : ∀ (lenv : LabelEnv) (env : TypeEnv) (a c : Site) (τ : BasicMoveType) (r r' : Aref) isBor cont retType,
      lookup env.siteEnv a = some (.ref τ r isBor) →
      notIn env.siteEnv c →
      freshRefInEnv r' env →
      (∀ v, r' ≠ .varRef v) →
      typecheck_stmt lenv
        {env with siteEnv := insert (delete env.siteEnv a) c (.ref τ r' .siteBorrowImm)
                  pathEnv := consume_ref_transfer env.pathEnv r r'}
        cont retType →
      typecheck_stmt lenv env (.letBind c (.freeze a) cont) retType

  -- let b = T { f1: a1, ..., fn: an }; cont (pack)
  | let_bind_pack : ∀ (lenv : LabelEnv) (env : TypeEnv) (b : Site) (recName : Id)
      (fields : List (Field × Site)) (fentries : AssocMap Field BasicMoveType) cont retType,
      notIn env.siteEnv b →
      (∀ f a, (f, a) ∈ fields →
         ∃ (bt : BasicMoveType), lookup env.siteEnv a = some (.basic bt) ∧
                                 lookup fentries f = some bt) →
      (∀ a₁ a₂, (∃ f₁ f₂, (f₁, a₁) ∈ fields ∧ (f₂, a₂) ∈ fields ∧ f₁ ≠ f₂) → a₁ ≠ a₂) →
      typecheck_stmt lenv
        {env with siteEnv := insert (deleteAll env.siteEnv (fields.map Prod.snd)) b (.basic (.trecord fentries))}
        cont retType →
      typecheck_stmt lenv env (.letBind b (.pack recName fields) cont) retType

  -- *a = b; cont
  | write_ref : ∀ (lenv : LabelEnv) (env : TypeEnv) a b τ (r: Aref) cont retType,
      AssocMap.lookup env.siteEnv a = some (.ref τ r .siteBorrowMut) →
      AssocMap.lookup env.siteEnv b = some (.basic τ) →
      check_outbound env.pathEnv r (λ re ↦ only_matches_empty (simplify re)) →
      typecheck_stmt lenv
        {env with siteEnv := delete (delete env.siteEnv b) a
                  pathEnv := garbage_collect env.pathEnv r}
        cont retType →
      typecheck_stmt lenv env (.writeRef a b cont) retType

  -- x = a; cont // x is a valid var
  -- Inlines typecheck_usage.t_uborrowMut_val for the mutable borrow of x
  -- Intermediate env has: ax bound to mutable ref, pathEnv updated with borrow
  -- Final env has: ax and a consumed, r garbage collected
  | var_assign_valid : ∀ (lenv : LabelEnv) (env : TypeEnv) x a ax τ ms (r : Aref) cont retType,
      LE.le .mutable ms →
      lookup env.varEnv x = some (.validVar, .basic τ, ms) →
      notIn env.siteEnv ax →
      freshRefInEnvBool r env →
      (∀ v, r ≠ .varRef v) →
      -- After writeRef: both ax and a are consumed, r is garbage collected
      -- The intermediate pathEnv is: update_with_extension r .root [.root_to_var x] (update_with_epsilon r r env.pathEnv)
      -- The intermediate siteEnv has ax with the mutable borrow
      -- After write: ax and a deleted, r garbage collected
      typecheck_stmt lenv
        {env with siteEnv := delete (delete (insert env.siteEnv ax (.ref τ r .siteBorrowMut)) a) ax
                  pathEnv := garbage_collect (update_with_extension r .root [.root_to_var x] (update_with_epsilon r r env.pathEnv)) r}
        cont retType →
      typecheck_stmt lenv env (.assign x a cont) retType

  -- x = a; cont // x is an invalid variable
  | var_assign_invalid : ∀ (lenv : LabelEnv) (env : TypeEnv) x a τ τ' cont retType,
      AssocMap.lookup env.varEnv x = some (.invalidVar, τ, .mutable) →
      AssocMap.lookup env.siteEnv a = some τ' →
      MoveType.compatible τ τ' →
      typecheck_stmt lenv
        {env with varEnv := update env.varEnv x (.validVar, τ', .mutable)
                  siteEnv := delete env.siteEnv a}
        cont retType →
      typecheck_stmt lenv env (.assign x a cont) retType

  -- let (a1, ..., an) = f(b1, ..., bm); cont // Call
  | call : ∀ (lenv : LabelEnv) (env : TypeEnv) fnName (as bs: List Site) (params rets : List ParamType) cont retType,
      all_fresh_sites env as →
      AssocMap.lookup env.funEnv fnName = some ⟨params, rets⟩ →
      types_conform env.siteEnv bs params →
      types_conform env.siteEnv as rets →
      check_mutable_inputs_isolated env bs →
      check_mutable_inputs_have_outbound env bs →
      typecheck_stmt lenv (call_connect_inputs_outputs env as bs) cont retType →
      typecheck_stmt lenv env (.call as fnName bs cont) retType

  -- release(a); cont
  | release : ∀ (lenv : LabelEnv) (env : TypeEnv) (a : Site) (τ : BasicMoveType) (r : Aref) isBor cont retType,
      AssocMap.lookup env.siteEnv a = some (.ref τ r isBor) →
      typecheck_stmt lenv
        {env with siteEnv := delete env.siteEnv a
                  pathEnv := delete_ref_node env.pathEnv r}
        cont retType →
      typecheck_stmt lenv env (.release a cont) retType

  -- T { f1: a1, ..., fn: an } = b; cont
  | unpack : ∀ (lenv : LabelEnv) (env : TypeEnv) (fields : List (Field × Site)) (b : Site)
      (fentries : AssocMap Field BasicMoveType) cont retType,
      AssocMap.lookup env.siteEnv b = some (.basic (.trecord fentries)) →
      (∀ (f : Field) (a : Site), (f, a) ∈ fields → AssocMap.notIn env.siteEnv a) →
      (∀ a₁ a₂, (∃ f₁ f₂, (f₁, a₁) ∈ fields ∧ (f₂, a₂) ∈ fields ∧ f₁ ≠ f₂) → a₁ ≠ a₂) →
      (∀ (f : Field) (a : Site), (f, a) ∈ fields → ∃ bt, AssocMap.lookup fentries f = some bt) →
      typecheck_stmt lenv
        {env with siteEnv := addFieldSites fentries (delete env.siteEnv b) fields}
        cont retType →
      typecheck_stmt lenv env (.unpack fields b cont) retType


/- ---------------------------------------------------- -/
/-       Type checking relation for functions            -/
/- ---------------------------------------------------- -/

/--
  Initialize VarEnv from function parameters.
  Parameters are added as valid, mutable variables.
-/
def init_varEnv_from_params (params : List (Var × MoveType)) : VarEnv :=
  params.foldl (fun venv (x, τ) => insert venv x (.validVar, τ, .mutable)) AssocMap.empty

/--
  Add local variable declarations to VarEnv.
  Locals are added as invalid variables (not yet assigned).
-/
def add_locals_to_varEnv (venv : VarEnv) (locals : List LocalVar) : VarEnv :=
  locals.foldl (fun venv loc => insert venv loc.name (.invalidVar, loc.type, .mutable)) venv

/--
  Build a LabelEnv from a list of blocks and their expected entry environments.
  The expectedEnvs list should have the same length as blocks.
-/
def build_labelEnv (blocks : List Block) (expectedEnvs : List TypeEnv) : LabelEnv :=
  (blocks.zip expectedEnvs).foldl (fun lenv (block, env) => insert lenv block.label env) AssocMap.empty

/--
  Type checking relation for a single block.
  The block's body (which includes the terminal statement) is type checked
  starting from the expected environment for its label.
-/
def typecheck_block (lenv : LabelEnv) (block : Block) (expectedEnv : TypeEnv) (retType : MoveType) : Prop :=
  typecheck_stmt lenv expectedEnv block.body retType

/--
  Compute the initial VarEnv for a function from its parameters and locals.
-/
def init_fun_varEnv (f : FunDef) : VarEnv :=
  add_locals_to_varEnv (init_varEnv_from_params f.params) f.locals

/--
  Type checking relation for functions.

  Judgment form: `⊢ f : ok`

  This relation type checks an entire function definition by:
  1. Initializing TypeEnv from parameters (valid mutable variables)
  2. Adding locals to TypeEnv (invalid variables, not yet assigned)
  3. Using the provided LabelEnv (expected environments for each block)
  4. Type checking each block's body against its expected entry environment
  5. Verifying the entry block starts with the initial environment

  Control flow is handled by terminal statements within each block's body.
  Each block is independent - there is no fall-through between blocks.
  The LabelEnv represents loop invariants / block entry conditions.
-/
inductive typecheck_fun : FunDef → LabelEnv → Prop where
  | fun_ok : ∀ (f : FunDef) (lenv : LabelEnv) (initEnv : TypeEnv),
    -- The initial environment has the initialized varEnv, empty siteEnv, initialized pathEnv
    initEnv.varEnv = init_fun_varEnv f →
    initEnv.siteEnv = AssocMap.empty →
    initEnv.pathEnv = PathEnv.init →
    -- The function must have at least one block (entry block)
    f.blocks ≠ [] →
    -- The entry block (first block) must have an environment equivalent to initEnv
    (∀ entryLabel entryBody entryEnv,
      f.blocks.head? = some ⟨entryLabel, entryBody⟩ →
      AssocMap.lookup lenv entryLabel = some entryEnv →
      TypeEnv.equiv entryEnv initEnv) →
    -- Every block must type check
    (∀ (block : Block),
      block ∈ f.blocks →
      ∀ blockEnv, AssocMap.lookup lenv block.label = some blockEnv →
        typecheck_block lenv block blockEnv f.returnType) →
    -- The function type checks
    typecheck_fun f lenv

-- Notation macros for type checking relations
-- These provide more readable syntax for the relations

-- Statement: Λ; ⟨Γ⟩ ⊢ s ⤳ ⟨Γ'⟩
-- Meaning: typecheck_stmt Λ Γ s Γ'
macro lenv:term "; " "⟨" env:term "⟩" " ⊢ₛ " s:term " ⤳ " "⟨" env':term "⟩" : term =>
  `(typecheck_stmt $lenv $env $s $env')

-- Function: ⊢ f : Λ
-- Meaning: typecheck_fun f Λ
macro " ⊢ᶠ " f:term " : " lenv:term : term =>
  `(typecheck_fun $f $lenv)



end LeanMove.Typing
