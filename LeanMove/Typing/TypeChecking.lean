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
  -- For x not to be borrowed, check all outbound edges from root to tracked refs
  -- and ensure none of them start with a path to x
  ∀ (r : Aref), r ∈ env.pathEnv.refs →
    ¬ interpret_regex (env.pathEnv.paths (.root, r)) [.root_to_var x]

def all_fresh_sites (env: TypeEnv) (as: List Site) : Prop :=
  List.all as (fun a ↦ notIn env.siteEnv a)

/- ---------------------------------------------------- -/
/- Typing relations for expressions -/
/- ---------------------------------------------------- -/


-- function to take a binop and types of its arguments and return the type of the result
def binop_type (bop : Binop) (τ1 τ2 : BasicMoveType) : Option BasicMoveType :=
  match (bop, τ1, τ2) with
  -- Arithmetic and comparison are defined at every integer width, but both
  -- operands must have the *same* width — Move has no implicit coercion, so
  -- `1u8 + 1u64` is a type error rather than a widening.
  | (.add, .int w1, .int w2) => if w1 == w2 then some (.int w1) else none
  | (.sub, .int w1, .int w2) => if w1 == w2 then some (.int w1) else none
  | (.mul, .int w1, .int w2) => if w1 == w2 then some (.int w1) else none
  | (.div, .int w1, .int w2) => if w1 == w2 then some (.int w1) else none
  | (.mod, .int w1, .int w2) => if w1 == w2 then some (.int w1) else none
  | (.lt,  .int w1, .int w2) => if w1 == w2 then some .tbool else none
  | (.gt,  .int w1, .int w2) => if w1 == w2 then some .tbool else none
  | (.le,  .int w1, .int w2) => if w1 == w2 then some .tbool else none
  | (.ge,  .int w1, .int w2) => if w1 == w2 then some .tbool else none
  | (.eq, .int w1, .int w2) => if w1 == w2 then some .tbool else none
  | (.eq, .tbool, .tbool) => some .tbool
  -- `neq` is defined wherever `eq` is: the bytecode `Neq` accepts any droppable type.
  | (.neq, .int w1, .int w2) => if w1 == w2 then some .tbool else none
  | (.neq, .tbool, .tbool) => some .tbool
  | (.and, .tbool, .tbool) => some .tbool
  | (.or, .tbool, .tbool) => some .tbool
  | _ => none

-- function to take a unop and the type of its argument and return the type of the result
def unop_type (uop : Unop) (τ : BasicMoveType) : Option BasicMoveType :=
  match (uop, τ) with
  | (.not, .tbool) => some .tbool
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

-- Helper for variant ref unpack: adds ref field sites with fresh arefs
-- For each (f, site) in fields, looks up f's type in fentries, creates a fresh ref,
-- and inserts a borrow site while extending the pathEnv.
def addRefFieldSites (r : Aref) (bk : BorrowingKind)
    (fentries : AssocMap Field BasicMoveType)
    (qualify : Field → Field)
    (fields : List (Field × Site)) (env : TypeEnv) : TypeEnv :=
  fields.foldl (fun env' (f_s : Field × Site) =>
    let (f, site) := f_s
    match lookup fentries f with
    | some bt =>
      let rf := nextFreshRefInEnv env'
      {env' with
        siteEnv := insert env'.siteEnv site (.ref bt rf bk)
        pathEnv := update_with_extension rf r [.field (qualify f)] env'.pathEnv}
    | none => env') env

-- Helper for vecUnpack: adds basic T sites for each element
def addVecSites (T : BasicMoveType) (se : AssocMap Site MoveType) : List Site → AssocMap Site MoveType
  | [] => se
  | s :: rest => addVecSites T (insert se s (.basic T)) rest

/-- Check that all refs in the list are fresh in the environment. -/
def all_refs_fresh_in_env (env : TypeEnv) (refs : List Aref) : Prop :=
  ∀ r ∈ refs, freshRefInEnv r env

/-- Populate output sites in the environment with types from return type specs.
    Basic returns: insert (.basic bt), consume no ref.
    Reference returns: insert (.ref bt r bk), consume one ref from outRefs,
    add r to pathEnv.refs via update_with_epsilon. -/
def populate_call_outputs (env : TypeEnv) (as : List Site) (rets : List ParamType)
    (outRefs : List Aref) : Option TypeEnv :=
  match as, rets with
  | [], [] => if outRefs.isEmpty then some env else none
  | site :: as', ⟨bt, none⟩ :: rets' =>
    let env' := { env with siteEnv := insert env.siteEnv site (.basic bt) }
    populate_call_outputs env' as' rets' outRefs
  | site :: as', ⟨bt, some true⟩ :: rets' =>
    match outRefs with
    | r :: outRefs' =>
      let env' := { env with
        siteEnv := insert env.siteEnv site (.ref bt r .siteBorrowMut)
        pathEnv := update_with_epsilon r r env.pathEnv }
      populate_call_outputs env' as' rets' outRefs'
    | [] => none
  | site :: as', ⟨bt, some false⟩ :: rets' =>
    match outRefs with
    | r :: outRefs' =>
      let env' := { env with
        siteEnv := insert env.siteEnv site (.ref bt r .siteBorrowImm)
        pathEnv := update_with_epsilon r r env.pathEnv }
      populate_call_outputs env' as' rets' outRefs'
    | [] => none
  | _, _ => none

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
  -- target=iout (output gets new paths), source=input (connectivity template)
  let with_io_from_inputs : PathEnv := List.foldl (fun penv iout ↦
    List.foldl (fun penv' input ↦ extend_with_star iout input penv') penv inputs
  ) env.pathEnv io

  -- Rule 2: For any mutable output, it will be extended from any mutable input only.
  -- Uses extend_with_star_no_outbound: adds only inbound paths (to freeze the input)
  -- but no outbound paths from the mutable output. The callee's return rule guarantees
  -- (ret_mutable_writable_bool + ret_mutable_no_aliases_bool) that mutable returned refs
  -- have no non-trivial outbound to non-returned refs and don't alias each other,
  -- so mutable call outputs are immediately writable.
  let with_mo_from_mi : PathEnv := List.foldl (fun penv mout ↦
    List.foldl (fun penv' minput ↦ extend_with_star_no_outbound mout minput penv') penv mi
  ) with_io_from_inputs mo

  -- Patch: Set outbound from each mutable output to .root = ε.
  -- This restores aliasing detection for later borrows: when a subsequent
  -- borrowImm/borrowMut of a local creates ref r3 via update_with_extension(r3, .root, path),
  -- the path from mout to r3 becomes G(mout, .root) ∘ path = ε ∘ path = path ≠ ∅,
  -- so check_outbound_bool blocks writes through mout when conflicting borrows exist.
  -- Without this patch, G(mout, .root) = ∅ and the conflict is invisible.
  -- For mutable outputs from parameter-level inputs (where source→root paths are ∅),
  -- only_matches_empty(ε) = true, so writes remain allowed when there's no conflict.
  let with_mo_patched := patch_root_outbound mo with_mo_from_mi

  -- Rule 3: Immutable outputs are .*-extended from each other
  -- For each pair (io1, io2) where io1 ≠ io2, add io1 →.* io2
  let with_io_to_io : PathEnv := List.foldl (fun penv io1 ↦
    List.foldl (fun penv' io2 ↦
      if io1 ≠ io2 then extend_with_star io1 io2 penv' else penv'
    ) penv io
  ) with_mo_patched io

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
            ∀ p, interpret_regex (env.pathEnv.paths (mi_ref, other_ref)) p → p = []

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
- `retTypes`: The function's return type (for ret checking)

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
inductive typecheck_stmt : LabelEnv → TypeEnv → Stmt → List ParamType → Prop where
  -- ==================== Terminal Statements ====================

  -- skip // No-op terminal
  | skip : ∀ (lenv : LabelEnv) (env : TypeEnv) retTypes,
      typecheck_stmt lenv env .skip retTypes

  -- jump L // Unconditional jump to label L
  -- The target label's environment subsumes the current environment
  -- (envL may be a join of multiple predecessors with wider paths)
  | jump : ∀ (lenv : LabelEnv) (env : TypeEnv) (L : Label) (envL : TypeEnv) retTypes,
      AssocMap.lookup lenv L = some envL →
      TypeEnv.subsumes envL env →
      typecheck_stmt lenv env (.jump L) retTypes

  -- branch a L1 L2 // If (a) goto L1 else goto L2
  -- Each target label's environment subsumes the post-branch environment
  | branch : ∀ (lenv : LabelEnv) (env : TypeEnv) (a : Site) (L1 L2 : Label) (envL1 envL2 : TypeEnv) retTypes,
      AssocMap.lookup env.siteEnv a = some (.basic .tbool) →
      AssocMap.lookup lenv L1 = some envL1 →
      AssocMap.lookup lenv L2 = some envL2 →
      TypeEnv.subsumes envL1 {env with siteEnv := delete env.siteEnv a} →
      TypeEnv.subsumes envL2 {env with siteEnv := delete env.siteEnv a} →
      typecheck_stmt lenv env (.branch a L1 L2) retTypes

  -- return (a1, ..., an) // Return from function
  -- Checks four conditions:
  -- 1. Types conform: positional matching of returned sites against declared return types
  -- 2. No local borrowing: returned refs don't borrow locals (no path from root to returned ref)
  -- 3. Writability: mutable returned refs have only trivial outbound to non-returned live ref sites
  --    (Checks against refs of live non-returned sites in siteEnv, not all pathEnv.refs)
  -- 4. No aliasing: no other returned ref reaches a mutable return
  | ret : ∀ (lenv : LabelEnv) (env : TypeEnv) (as : List Site) retTypes,
      -- 1. Types conform
      types_conform env.siteEnv as retTypes →
      -- 2. No local borrowing: returned refs don't borrow locals
      (∀ a ∈ as, ∀ bt r bk, AssocMap.lookup env.siteEnv a = some (.ref bt r bk) →
        ∀ p, ¬interpret_regex (env.pathEnv.paths (.root, r)) p) →
      -- 3. Writability: mutable returned refs have only trivial outbound to non-returned live sites
      (∀ a ∈ as, ∀ bt r, AssocMap.lookup env.siteEnv a = some (.ref bt r .siteBorrowMut) →
        ∀ b, b ∉ as →
          ∀ bt' r' bk', AssocMap.lookup env.siteEnv b = some (.ref bt' r' bk') →
            ∀ p, interpret_regex (env.pathEnv.paths (r, r')) p → p = []) →
      -- 4. No aliasing: no other returned ref reaches a mutable return
      (∀ a₁ ∈ as, ∀ bt₁ r₁, AssocMap.lookup env.siteEnv a₁ = some (.ref bt₁ r₁ .siteBorrowMut) →
        ∀ a₂ ∈ as, a₁ ≠ a₂ →
          ∀ bt₂ r₂ bk₂, AssocMap.lookup env.siteEnv a₂ = some (.ref bt₂ r₂ bk₂) →
            ∀ p, ¬interpret_regex (env.pathEnv.paths (r₂, r₁)) p) →
      typecheck_stmt lenv env (.ret as) retTypes

  -- abort a // Abort execution with error value
  | abort : ∀ (lenv : LabelEnv) (env : TypeEnv) (a : Site) τ retTypes,
      AssocMap.lookup env.siteEnv a = some τ →
      typecheck_stmt lenv env (.abort a) retTypes

  -- ==================== Non-terminal Statements ====================

  -- let a = move(x); cont
  | let_bind_move : ∀ (lenv : LabelEnv) (env : TypeEnv) (a : Site) x τ ms cont retTypes,
      lookup env.varEnv x = some (.validVar, τ, ms) →
      not_borrowed x env →
      notIn env.siteEnv a →
      typecheck_stmt lenv
        {env with varEnv := update env.varEnv x (.invalidVar, τ, ms)
                  siteEnv := insert env.siteEnv a τ}
        cont retTypes →
      typecheck_stmt lenv env (.letBind a (.usage (.move x)) cont) retTypes

  -- let a = copy(x); cont where x has basic type
  | let_bind_copy_val : ∀ (lenv : LabelEnv) (env : TypeEnv) (a : Site) x bt ms cont retTypes,
      lookup env.varEnv x = some (.validVar, .basic bt, ms) →
      notIn env.siteEnv a →
      typecheck_stmt lenv
        {env with siteEnv := insert env.siteEnv a (.basic bt)}
        cont retTypes →
      typecheck_stmt lenv env (.letBind a (.usage (.copy x)) cont) retTypes

  -- let a = copy(x); cont where x has reference type
  | let_bind_copy_ref : ∀ (lenv : LabelEnv) (env : TypeEnv) (a : Site) x τ ms (s t : Aref) isBor cont retTypes,
      lookup env.varEnv x = some (.validVar, .ref τ s isBor, ms) →
      notIn env.siteEnv a →
      freshRefInEnv t env →
      typecheck_stmt lenv
        {env with siteEnv := insert env.siteEnv a (.ref τ t isBor)
                  pathEnv := update_with_epsilon t s env.pathEnv}
        cont retTypes →
      typecheck_stmt lenv env (.letBind a (.usage (.copy x)) cont) retTypes

  -- let a = &x; cont (immutable borrow)
  | let_bind_borrowImm : ∀ (lenv : LabelEnv) (env : TypeEnv) (a : Site) x τ ms (r : Aref) cont retTypes,
      lookup env.varEnv x = some (.validVar, .basic τ, ms) →
      notIn env.siteEnv a →
      freshRefInEnv r env →
      typecheck_stmt lenv
        {env with siteEnv := insert env.siteEnv a (.ref τ r .siteBorrowImm)
                  pathEnv := update_with_epsilon r r env.pathEnv |>
                             update_with_extension r .root [.root_to_var x]}
        cont retTypes →
      typecheck_stmt lenv env (.letBind a (.usage (.borrowImm x)) cont) retTypes

  -- let a = &mut x; cont (mutable borrow)
  | let_bind_borrowMut : ∀ (lenv : LabelEnv) (env : TypeEnv) (a : Site) x τ ms (r : Aref) cont retTypes,
      LE.le .mutable ms →
      lookup env.varEnv x = some (.validVar, .basic τ, ms) →
      notIn env.siteEnv a →
      freshRefInEnv r env →
      typecheck_stmt lenv
        {env with siteEnv := insert env.siteEnv a (.ref τ r .siteBorrowMut)
                  pathEnv := update_with_epsilon r r env.pathEnv |>
                             update_with_extension r .root [.root_to_var x]}
        cont retTypes →
      typecheck_stmt lenv env (.letBind a (.usage (.borrowMut x)) cont) retTypes

  -- let a = n; cont (integer literal)
  | let_bind_intLit : ∀ (lenv : LabelEnv) (env : TypeEnv) (a : Site) (n : Nat) (w : IntType) cont retTypes,
      notIn env.siteEnv a →
      typecheck_stmt lenv
        {env with siteEnv := insert env.siteEnv a (.basic (.int w))}
        cont retTypes →
      typecheck_stmt lenv env (.letBind a (.intLit n w) cont) retTypes

  -- let af = &a.T::f; cont (field borrow)
  | let_bind_borrowField : ∀ (lenv : LabelEnv) (env : TypeEnv) (a af : Site) f bt bt' isBor fentries s (rf : Aref) cont retTypes,
      lookup env.siteEnv a = some (.ref bt s isBor) →
      bt = .trecord fentries →
      lookup fentries f = some bt' →
      notIn env.siteEnv af →
      freshRefInEnv rf env →
      typecheck_stmt lenv
        {env with siteEnv := insert (delete env.siteEnv a) af (.ref bt' rf isBor)
                  pathEnv := update_with_extension rf s [.field f] env.pathEnv}
        cont retTypes →
      typecheck_stmt lenv env (.letBind af (.borrowField a bt f) cont) retTypes

  -- let af = &mut a.T::f; cont (mutable field borrow)
  | let_bind_borrowMutField : ∀ (lenv : LabelEnv) (env : TypeEnv) (a af : Site) f bt btf fentries (s rf : Aref) cont retTypes,
      lookup env.siteEnv a = some (.ref bt s .siteBorrowMut) →
      bt = .trecord fentries →
      lookup fentries f = some btf →
      notIn env.siteEnv af →
      freshRefInEnv rf env →
      typecheck_stmt lenv
        {env with siteEnv := insert (delete env.siteEnv a) af (.ref btf rf .siteBorrowMut)
                  pathEnv := update_with_extension rf s [.field f] env.pathEnv}
        cont retTypes →
      typecheck_stmt lenv env (.letBind af (.borrowMutField a bt f) cont) retTypes

  -- let c = a ⊕ b; cont (binary operation)
  | let_bind_binop : ∀ (lenv : LabelEnv) (env : TypeEnv) bop bt1 bt2 bt3 (a b c : Site) cont retTypes,
      lookup env.siteEnv a = some (.basic bt1) →
      lookup env.siteEnv b = some (.basic bt2) →
      binop_type bop bt1 bt2 = some bt3 →
      notIn env.siteEnv c →
      typecheck_stmt lenv
        {env with siteEnv := insert (delete (delete env.siteEnv a) b) c (.basic bt3)}
        cont retTypes →
      typecheck_stmt lenv env (.letBind c (.binop bop a b) cont) retTypes

  -- let c = ⊖ a; cont (unary operation)
  | let_bind_unop : ∀ (lenv : LabelEnv) (env : TypeEnv) uop bt1 bt2 (a c : Site) cont retTypes,
      lookup env.siteEnv a = some (.basic bt1) →
      unop_type uop bt1 = some bt2 →
      notIn env.siteEnv c →
      typecheck_stmt lenv
        {env with siteEnv := insert (delete env.siteEnv a) c (.basic bt2)}
        cont retTypes →
      typecheck_stmt lenv env (.letBind c (.unop uop a) cont) retTypes

  -- let c = *a; cont (dereference)
  | let_bind_readRef : ∀ (lenv : LabelEnv) (env : TypeEnv) (a c : Site) r (τ : BasicMoveType) isBor cont retTypes,
      lookup env.siteEnv a = some (.ref τ r isBor) →
      notIn env.siteEnv c →
      typecheck_stmt lenv
        {env with siteEnv := insert (delete env.siteEnv a) c (.basic τ)
                  pathEnv := delete_ref_node env.pathEnv r}
        cont retTypes →
      typecheck_stmt lenv env (.letBind c (.readRef a) cont) retTypes

  -- let c = freeze a; cont
  | let_bind_freeze : ∀ (lenv : LabelEnv) (env : TypeEnv) (a c : Site) (τ : BasicMoveType) (r r' : Aref) isBor cont retTypes,
      lookup env.siteEnv a = some (.ref τ r isBor) →
      notIn env.siteEnv c →
      freshRefInEnv r' env →
      typecheck_stmt lenv
        {env with siteEnv := insert (delete env.siteEnv a) c (.ref τ r' .siteBorrowImm)
                  pathEnv := consume_ref_transfer env.pathEnv r r'}
        cont retTypes →
      typecheck_stmt lenv env (.letBind c (.freeze a) cont) retTypes

  -- let b = T { f1: a1, ..., fn: an }; cont (pack)
  | let_bind_pack : ∀ (lenv : LabelEnv) (env : TypeEnv) (b : Site) (recName : Id)
      (fields : List (Field × Site)) (fentries : AssocMap Field BasicMoveType) cont retTypes,
      notIn env.siteEnv b →
      (∀ f a, (f, a) ∈ fields →
         ∃ (bt : BasicMoveType), lookup env.siteEnv a = some (.basic bt) ∧
                                 lookup fentries f = some bt) →
      (∀ f, lookup fentries f ≠ none → ∃ a, (f, a) ∈ fields) →
      (∀ a₁ a₂, (∃ f₁ f₂, (f₁, a₁) ∈ fields ∧ (f₂, a₂) ∈ fields ∧ f₁ ≠ f₂) → a₁ ≠ a₂) →
      typecheck_stmt lenv
        {env with siteEnv := insert (deleteAll env.siteEnv (fields.map Prod.snd)) b (.basic (.trecord fentries))}
        cont retTypes →
      typecheck_stmt lenv env (.letBind b (.pack recName fields) cont) retTypes

  -- *a = b; cont
  | write_ref : ∀ (lenv : LabelEnv) (env : TypeEnv) a b τ (r: Aref) cont retTypes,
      AssocMap.lookup env.siteEnv a = some (.ref τ r .siteBorrowMut) →
      AssocMap.lookup env.siteEnv b = some (.basic τ) →
      check_outbound env.pathEnv r (λ re ↦ only_matches_empty (simplify re)) →
      typecheck_stmt lenv
        {env with siteEnv := delete (delete env.siteEnv b) a
                  pathEnv := garbage_collect env.pathEnv r}
        cont retTypes →
      typecheck_stmt lenv env (.writeRef a b cont) retTypes

  -- x = a; cont // x is a valid var
  -- Inlines typecheck_usage.t_uborrowMut_val for the mutable borrow of x
  -- Intermediate env has: ax bound to mutable ref, pathEnv updated with borrow
  -- Final env has: ax and a consumed, r garbage collected
  | var_assign_valid : ∀ (lenv : LabelEnv) (env : TypeEnv) x a ax τ ms (r : Aref) cont retTypes,
      LE.le .mutable ms →
      lookup env.varEnv x = some (.validVar, .basic τ, ms) →
      lookup env.siteEnv a = some (.basic τ) →
      notIn env.siteEnv ax →
      freshRefInEnv r env →
      -- After writeRef: both ax and a are consumed, r is garbage collected
      -- The intermediate pathEnv is: update_with_extension r .root [.root_to_var x] (update_with_epsilon r r env.pathEnv)
      -- The intermediate siteEnv has ax with the mutable borrow
      -- After write: ax and a deleted, r garbage collected
      typecheck_stmt lenv
        {env with siteEnv := delete (delete (insert env.siteEnv ax (.ref τ r .siteBorrowMut)) a) ax
                  pathEnv := garbage_collect (update_with_extension r .root [.root_to_var x] (update_with_epsilon r r env.pathEnv)) r}
        cont retTypes →
      typecheck_stmt lenv env (.assign x a cont) retTypes

  -- x = a; cont // x is a valid var with ref type (reassign releases old borrow)
  | var_assign_valid_ref : ∀ (lenv : LabelEnv) (env : TypeEnv) x a
      (τ_old : BasicMoveType) (r_old : Aref) (bk_old : BorrowingKind) (τ' : MoveType) (ms : Mut)
      cont retTypes,
      LE.le .mutable ms →
      lookup env.varEnv x = some (.validVar, .ref τ_old r_old bk_old, ms) →
      lookup env.siteEnv a = some τ' →
      typecheck_stmt lenv
        {env with varEnv := update env.varEnv x (.validVar, τ', ms)
                  siteEnv := delete env.siteEnv a
                  pathEnv := delete_ref_node env.pathEnv r_old}
        cont retTypes →
      typecheck_stmt lenv env (.assign x a cont) retTypes

  -- x = a; cont // x is an invalid variable
  | var_assign_invalid : ∀ (lenv : LabelEnv) (env : TypeEnv) x a τ τ' cont retTypes,
      AssocMap.lookup env.varEnv x = some (.invalidVar, τ, .mutable) →
      AssocMap.lookup env.siteEnv a = some τ' →
      MoveType.compatible τ τ' →
      typecheck_stmt lenv
        {env with varEnv := update env.varEnv x (.validVar, τ', .mutable)
                  siteEnv := delete env.siteEnv a}
        cont retTypes →
      typecheck_stmt lenv env (.assign x a cont) retTypes

  -- x = a; cont // x has basic type (any IsValid status), simplified continuation
  -- This rule is sound because basic values have no resources to release on overwrite.
  | var_assign_overwrite_basic : ∀ (lenv : LabelEnv) (env : TypeEnv) x a
      (isv : IsValid) (τ : BasicMoveType) cont retTypes,
      AssocMap.lookup env.varEnv x = some (isv, .basic τ, .mutable) →
      AssocMap.lookup env.siteEnv a = some (.basic τ) →
      typecheck_stmt lenv
        {env with varEnv := update env.varEnv x (.validVar, .basic τ, .mutable)
                  siteEnv := delete env.siteEnv a}
        cont retTypes →
      typecheck_stmt lenv env (.assign x a cont) retTypes

  -- let (a1, ..., an) = f(b1, ..., bm); cont // Call
  | call : ∀ (lenv : LabelEnv) (env : TypeEnv) fnName (as bs : List Site)
        (params rets : List ParamType) (outRefs : List Aref) (env' : TypeEnv)
        cont retTypes,
      -- Function signature
      AssocMap.lookup env.funEnv fnName = some ⟨params, rets⟩ →
      -- Inputs conform to parameter types
      types_conform env.siteEnv bs params →
      -- Output sites are fresh and unique
      all_fresh_sites env as →
      List.Nodup as →
      -- Fresh abstract refs for reference-typed outputs
      all_refs_fresh_in_env env outRefs →
      List.Nodup outRefs →
      -- Populate output sites → env'
      populate_call_outputs env as rets outRefs = some env' →
      -- Mutable inputs isolated
      check_mutable_inputs_isolated env bs →
      -- Continuation typed in env after output population + path connections + input consumption
      typecheck_stmt lenv
        (let env'' := call_connect_inputs_outputs env' as bs
         {env'' with siteEnv := AssocMap.deleteAll env''.siteEnv bs})
        cont retTypes →
      typecheck_stmt lenv env (.call as fnName bs cont) retTypes

  -- release(a); cont — for ref sites (deletes ref from pathEnv)
  | release : ∀ (lenv : LabelEnv) (env : TypeEnv) (a : Site) (τ : BasicMoveType) (r : Aref) isBor cont retTypes,
      AssocMap.lookup env.siteEnv a = some (.ref τ r isBor) →
      typecheck_stmt lenv
        {env with siteEnv := delete env.siteEnv a
                  pathEnv := delete_ref_node env.pathEnv r}
        cont retTypes →
      typecheck_stmt lenv env (.release a cont) retTypes

  -- release(a); cont — for basic sites (just removes from siteEnv)
  | release_basic : ∀ (lenv : LabelEnv) (env : TypeEnv) (a : Site) (bt : BasicMoveType) cont retTypes,
      AssocMap.lookup env.siteEnv a = some (.basic bt) →
      typecheck_stmt lenv
        {env with siteEnv := delete env.siteEnv a}
        cont retTypes →
      typecheck_stmt lenv env (.release a cont) retTypes

  -- T { f1: a1, ..., fn: an } = b; cont
  | unpack : ∀ (lenv : LabelEnv) (env : TypeEnv) (fields : List (Field × Site)) (b : Site)
      (fentries : AssocMap Field BasicMoveType) cont retTypes,
      AssocMap.lookup env.siteEnv b = some (.basic (.trecord fentries)) →
      (∀ (f : Field) (a : Site), (f, a) ∈ fields → AssocMap.notIn env.siteEnv a) →
      (∀ a₁ a₂, (∃ f₁ f₂, (f₁, a₁) ∈ fields ∧ (f₂, a₂) ∈ fields ∧ f₁ ≠ f₂) → a₁ ≠ a₂) →
      (∀ (f : Field) (a : Site), (f, a) ∈ fields → ∃ bt, AssocMap.lookup fentries f = some bt) →
      typecheck_stmt lenv
        {env with siteEnv := addFieldSites fentries (delete env.siteEnv b) fields}
        cont retTypes →
      typecheck_stmt lenv env (.unpack fields b cont) retTypes

  -- ============================================================
  -- Vector operations
  -- ============================================================

  -- let b = vec_pack<T>(elems); cont
  | let_bind_vecPack : ∀ (lenv : LabelEnv) (env : TypeEnv) (b : Site) (T : BasicMoveType)
      (elems : List Site) cont retTypes,
      notIn env.siteEnv b →
      (∀ a, a ∈ elems → AssocMap.lookup env.siteEnv a = some (.basic T)) →
      List.Nodup elems →
      typecheck_stmt lenv
        {env with siteEnv := insert (deleteAll env.siteEnv elems) b (.basic (.tvec T))}
        cont retTypes →
      typecheck_stmt lenv env (.letBind b (.vecPack T elems) cont) retTypes

  -- vec_unpack<T>(results, src); cont
  | vecUnpack_rule : ∀ (lenv : LabelEnv) (env : TypeEnv) (T : BasicMoveType)
      (results : List Site) (src : Site) cont retTypes,
      AssocMap.lookup env.siteEnv src = some (.basic (.tvec T)) →
      (∀ a, a ∈ results → notIn env.siteEnv a) →
      List.Nodup results →
      typecheck_stmt lenv
        {env with siteEnv := addVecSites T (delete env.siteEnv src) results}
        cont retTypes →
      typecheck_stmt lenv env (.vecUnpack T results src cont) retTypes

  -- let a = vec_len(src); cont
  | let_bind_vecLen : ∀ (lenv : LabelEnv) (env : TypeEnv) (a src : Site)
      (T : BasicMoveType) (r : Aref) isBor cont retTypes,
      AssocMap.lookup env.siteEnv src = some (.ref (.tvec T) r isBor) →
      notIn env.siteEnv a →
      typecheck_stmt lenv
        {env with siteEnv := insert (delete env.siteEnv src) a (.basic .u64)
                  pathEnv := delete_ref_node env.pathEnv r}
        cont retTypes →
      typecheck_stmt lenv env (.letBind a (.vecLen src) cont) retTypes

  -- let a = vec_imm_borrow(src, idx); cont
  | let_bind_vecImmBorrow : ∀ (lenv : LabelEnv) (env : TypeEnv)
      (a src idx : Site) (T : BasicMoveType) (s rf : Aref) isBor cont retTypes,
      AssocMap.lookup env.siteEnv src = some (.ref (.tvec T) s isBor) →
      AssocMap.lookup env.siteEnv idx = some (.basic .u64) →
      notIn env.siteEnv a →
      (isBor = .siteBorrowMut → check_outbound env.pathEnv s (λ re ↦ only_matches_empty (simplify re))) →
      freshRefInEnv rf env →
      typecheck_stmt lenv
        {env with siteEnv := insert (delete (delete env.siteEnv src) idx) a (.ref T rf .siteBorrowImm)
                  pathEnv := update_with_extension rf s [.vecElem] env.pathEnv}
        cont retTypes →
      typecheck_stmt lenv env (.letBind a (.vecImmBorrow src idx) cont) retTypes

  -- let a = vec_mut_borrow(src, idx); cont
  | let_bind_vecMutBorrow : ∀ (lenv : LabelEnv) (env : TypeEnv)
      (a src idx : Site) (T : BasicMoveType) (s rf : Aref) cont retTypes,
      AssocMap.lookup env.siteEnv src = some (.ref (.tvec T) s .siteBorrowMut) →
      AssocMap.lookup env.siteEnv idx = some (.basic .u64) →
      notIn env.siteEnv a →
      check_outbound env.pathEnv s (λ re ↦ only_matches_empty (simplify re)) →
      freshRefInEnv rf env →
      typecheck_stmt lenv
        {env with siteEnv := insert (delete (delete env.siteEnv src) idx) a (.ref T rf .siteBorrowMut)
                  pathEnv := update_with_extension rf s [.vecElem] env.pathEnv}
        cont retTypes →
      typecheck_stmt lenv env (.letBind a (.vecMutBorrow src idx) cont) retTypes

  -- let a = vec_pop_back(src); cont
  | let_bind_vecPopBack : ∀ (lenv : LabelEnv) (env : TypeEnv)
      (a src : Site) (T : BasicMoveType) (r : Aref) cont retTypes,
      AssocMap.lookup env.siteEnv src = some (.ref (.tvec T) r .siteBorrowMut) →
      check_outbound env.pathEnv r (λ re ↦ only_matches_empty (simplify re)) →
      notIn env.siteEnv a →
      typecheck_stmt lenv
        {env with siteEnv := insert (delete env.siteEnv src) a (.basic T)
                  pathEnv := garbage_collect env.pathEnv r}
        cont retTypes →
      typecheck_stmt lenv env (.letBind a (.vecPopBack src) cont) retTypes

  -- vec_push_back(ref, val); cont
  | vecPushBack_rule : ∀ (lenv : LabelEnv) (env : TypeEnv)
      (refSite val : Site) (T : BasicMoveType) (r : Aref) cont retTypes,
      AssocMap.lookup env.siteEnv refSite = some (.ref (.tvec T) r .siteBorrowMut) →
      AssocMap.lookup env.siteEnv val = some (.basic T) →
      check_outbound env.pathEnv r (λ re ↦ only_matches_empty (simplify re)) →
      typecheck_stmt lenv
        {env with siteEnv := delete (delete env.siteEnv val) refSite
                  pathEnv := garbage_collect env.pathEnv r}
        cont retTypes →
      typecheck_stmt lenv env (.vecPushBack refSite val cont) retTypes

  -- vec_swap(ref, idx1, idx2); cont
  | vecSwap_rule : ∀ (lenv : LabelEnv) (env : TypeEnv)
      (refSite idx1 idx2 : Site) (T : BasicMoveType) (r : Aref) cont retTypes,
      AssocMap.lookup env.siteEnv refSite = some (.ref (.tvec T) r .siteBorrowMut) →
      AssocMap.lookup env.siteEnv idx1 = some (.basic .u64) →
      AssocMap.lookup env.siteEnv idx2 = some (.basic .u64) →
      check_outbound env.pathEnv r (λ re ↦ only_matches_empty (simplify re)) →
      typecheck_stmt lenv
        {env with siteEnv := delete (delete (delete env.siteEnv idx2) idx1) refSite
                  pathEnv := garbage_collect env.pathEnv r}
        cont retTypes →
      typecheck_stmt lenv env (.vecSwap refSite idx1 idx2 cont) retTypes

  -- ============================================================
  -- Enum operations
  -- ============================================================

  -- let b = packVariant(enumName, variantName, fields); cont
  | let_bind_packVariant : ∀ (lenv : LabelEnv) (env : TypeEnv) (b : Site) (enumName variantName : Id)
      (fields : List (Field × Site))
      (enumDef : EnumDef) (variantDef : EnumVariantDef) cont retTypes,
      notIn env.siteEnv b →
      AssocMap.lookup env.enumEnv enumName = some enumDef →
      AssocMap.lookup enumDef.variants variantName = some variantDef →
      (∀ f a, (f, a) ∈ fields →
         ∃ (bt : BasicMoveType), lookup env.siteEnv a = some (.basic bt) ∧
                                 lookup variantDef.fields f = some bt) →
      (∀ f, lookup variantDef.fields f ≠ none → ∃ a, (f, a) ∈ fields) →
      (∀ a₁ a₂, (∃ f₁ f₂, (f₁, a₁) ∈ fields ∧ (f₂, a₂) ∈ fields ∧ f₁ ≠ f₂) → a₁ ≠ a₂) →
      typecheck_stmt lenv
        {env with siteEnv := insert (deleteAll env.siteEnv (fields.map Prod.snd)) b
                                    (.basic (.tenum enumName))}
        cont retTypes →
      typecheck_stmt lenv env (.letBind b (.packVariant enumName variantName fields) cont) retTypes

  -- E.V { f1: a1, ..., fn: an } = b; cont  (owned variant unpack)
  | unpackVariant_rule : ∀ (lenv : LabelEnv) (env : TypeEnv) (variantName : Id)
      (fields : List (Field × Site)) (b : Site)
      (ename : Id) (enumDef : EnumDef) (variantDef : EnumVariantDef) cont retTypes,
      AssocMap.lookup env.siteEnv b = some (.basic (.tenum ename)) →
      AssocMap.lookup env.enumEnv ename = some enumDef →
      AssocMap.lookup enumDef.variants variantName = some variantDef →
      (∀ (f : Field) (a : Site), (f, a) ∈ fields → AssocMap.notIn env.siteEnv a) →
      (∀ a₁ a₂, (∃ f₁ f₂, (f₁, a₁) ∈ fields ∧ (f₂, a₂) ∈ fields ∧ f₁ ≠ f₂) → a₁ ≠ a₂) →
      (∀ (f : Field) (a : Site), (f, a) ∈ fields → ∃ bt, AssocMap.lookup variantDef.fields f = some bt) →
      typecheck_stmt lenv
        {env with siteEnv := addFieldSites variantDef.fields (delete env.siteEnv b) fields}
        cont retTypes →
      typecheck_stmt lenv env (.unpackVariant variantName fields b cont) retTypes

  -- &[mut] E.V { f1: a1, ..., fn: an } = b; cont  (ref variant unpack)
  -- Creates borrows for each field of the variant
  | unpackVariant_ref_rule : ∀ (lenv : LabelEnv) (env : TypeEnv) (variantName : Id)
      (fields : List (Field × Site)) (b : Site)
      (ename : Id) (enumDef : EnumDef) (variantDef : EnumVariantDef)
      (r : Aref) (bk : BorrowingKind) cont retTypes,
      AssocMap.lookup env.siteEnv b = some (.ref (.tenum ename) r bk) →
      AssocMap.lookup env.enumEnv ename = some enumDef →
      AssocMap.lookup enumDef.variants variantName = some variantDef →
      (∀ (f : Field) (a : Site), (f, a) ∈ fields → AssocMap.notIn env.siteEnv a) →
      (∀ a₁ a₂, (∃ f₁ f₂, (f₁, a₁) ∈ fields ∧ (f₂, a₂) ∈ fields ∧ f₁ ≠ f₂) → a₁ ≠ a₂) →
      (∀ (f : Field) (a : Site), (f, a) ∈ fields → ∃ bt, AssocMap.lookup variantDef.fields f = some bt) →
      typecheck_stmt lenv
        (addRefFieldSites r bk variantDef.fields (LeanMove.Lang.MoveLight.qualifyField variantName) fields {env with siteEnv := delete env.siteEnv b})
        cont retTypes →
      typecheck_stmt lenv env (.unpackVariant variantName fields b cont) retTypes

  -- variant_switch src [(v1, l1), ...] (terminal)
  -- Borrows the enum for tag dispatch, then releases the borrow
  | variantSwitch_rule : ∀ (lenv : LabelEnv) (env : TypeEnv) (src : Site)
      (cases : List (Id × Label))
      (ename : Id) (enumDef : EnumDef) (r : Aref) (bk : BorrowingKind) (retTypes : List ParamType),
      AssocMap.lookup env.siteEnv src = some (.ref (.tenum ename) r bk) →
      AssocMap.lookup env.enumEnv ename = some enumDef →
      -- All variants are covered
      (∀ vname, AssocMap.lookup enumDef.variants vname ≠ none → ∃ label, (vname, label) ∈ cases) →
      -- Each case label exists in lenv and target env subsumes current env minus the borrow
      (∀ vname label, (vname, label) ∈ cases →
         ∃ envL, AssocMap.lookup lenv label = some envL ∧
                 TypeEnv.subsumes envL
                   {env with siteEnv := delete env.siteEnv src
                             pathEnv := delete_ref_node env.pathEnv r}) →
      typecheck_stmt lenv env (.variantSwitch src cases) retTypes


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
def typecheck_block (lenv : LabelEnv) (block : Block) (expectedEnv : TypeEnv) (retTypes : List ParamType) : Prop :=
  typecheck_stmt lenv expectedEnv block.body retTypes

/--
  Compute the initial VarEnv for a function from its parameters and locals.
-/
def init_fun_varEnv (f : FunDef) : VarEnv :=
  add_locals_to_varEnv (init_varEnv_from_params f.params) f.locals

/-- Construct the initial TypeEnv for a function.
    Derives siteEnv (empty), varEnv (from params + locals), pathEnv (from params), and enumEnv. -/
def mkInitEnv (f : FunDef) (funEnv : FunEnv := AssocMap.empty) (enumEnv : EnumEnv := AssocMap.empty) : TypeEnv :=
  { siteEnv := AssocMap.empty
    varEnv := init_fun_varEnv f
    pathEnv := init_fun_pathEnv f
    funEnv := funEnv
    enumEnv := enumEnv }

/-- Construct a LabelEnv for a single-block function.
    Uses the first block's label as the entry point. -/
def mkLabelEnv (f : FunDef) (funEnv : FunEnv := AssocMap.empty) (enumEnv : EnumEnv := AssocMap.empty) : LabelEnv :=
  match f.blocks with
  | b :: _ => AssocMap.insert AssocMap.empty b.label (mkInitEnv f funEnv enumEnv)
  | [] => AssocMap.empty

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
inductive typecheck_fun : FunDef → LabelEnv → EnumEnv → Prop where
  | fun_ok : ∀ (f : FunDef) (lenv : LabelEnv) (enumEnv : EnumEnv) (initEnv : TypeEnv),
    -- The initial environment has the initialized varEnv, empty siteEnv, initialized pathEnv, and enumEnv
    initEnv.varEnv = init_fun_varEnv f →
    initEnv.siteEnv = AssocMap.empty →
    initEnv.pathEnv = init_fun_pathEnv f →
    initEnv.enumEnv = enumEnv →
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
    typecheck_fun f lenv enumEnv

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
