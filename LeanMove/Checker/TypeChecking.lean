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
import LeanMove.Checker.Types

/-!
# Type Checking Rules for MoveLight

This file contains the typing relations for the MoveLight language.
Type environment definitions and auxiliary lemmas are in `Types.lean`.
-/

namespace LeanMove.Checker

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
    verify that there is no non-empty path from mi_ref to other_ref in PathEnv.

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
            let regex := env.pathEnv.paths (mi_ref, other_ref)
            ¬ (∃ path, interpret_regex regex path ∧ path ≠ [])

/-- Check that all mutable inputs have non-trivial outbound edges.

    For each mutable input site mi_site with abstract reference mi_ref,
    verify that there exists at least one target reference that mi_ref reaches
    via a non-empty path in PathEnv.

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
        let regex := env.pathEnv.paths (mi_ref, target)
        ∃ path, interpret_regex regex path ∧ path ≠ []

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
Type checking relation for statements (no control flow - that's in Terminator).

Judgment form: `⟨env⟩ ⊢ s ⤳ ⟨env'⟩`

This relation handles all statement forms that transform the environment:
- **skip**: No-op, environment unchanged
- **let a = e**: Bind expression result to site (delegates to typecheck_expr)
- **x = a**: Assign site value to variable, invalidating previous variable binding
- ***a = b**: Write through mutable reference, consuming both sites
- **let (a1, ..., an) = f(b1, ..., bm)**: Function call with path updates
- **T { f1: a1, ..., fn: an } = b**: Unpack record into field sites
- **release(a)**: Explicitly release a reference
- **s1; s2**: Sequential composition - threads environment from s1 to s2

Control flow (jump, branch, ret, abort) is handled separately by typecheck_terminator.

Components:
- `env`: Input type environment before executing the statement
- `Stmt`: The statement being type checked
- `env'`: Output type environment after execution

Key environment transformations:
⋆ **varEnv updates**: Assignments update variable bindings; moves invalidate variables
⋆ **siteEnv updates**: Sites are consumed by operations and new sites are produced
⋆ **PathEnv updates**:
  - Borrows add edges from root to references
  - Field accesses extend paths with field names
  - Function calls add conservative .*-extensions between inputs/outputs
  - Write operations check for dangling reference prevention (no outbound edges)
⋆ **Reference lifecycle**: Abstract references are allocated, tracked, and garbage collected

Function call path update rules (via call_connect_inputs_outputs):
  1. Immutable outputs (IO) ←.* from all inputs (MI ∪ II)
  2. Mutable outputs (MO) ←.* from mutable inputs (MI) only
  3. Immutable outputs ←.* from each other

Validation checks:
⋆ **Mutable input isolation**: No mutable input reaches any other input (prevents aliasing)
⋆ **Liveness**: All mutable inputs have non-trivial outbound edges (properly connected)
⋆ **No dangling references**: Write operations require target has no outbound edges beyond ε
⋆ **Type conformance**: Function arguments/returns match declared types and mutability

Linear resource tracking:
⋆ Sites represent linear resources that are consumed exactly once
⋆ Variables can be invalidated (moved) or preserved (copied/borrowed)
⋆ PathEnv tracks which variables are borrowed (via not_borrowed check)
-/
inductive typecheck_stmt : LabelEnv → TypeEnv → Stmt → TypeEnv → Prop where
  | skip : ∀ (lenv : LabelEnv) (env : TypeEnv), typecheck_stmt lenv env .skip env

  -- let a = move(x)
  | let_bind_move : ∀ (lenv : LabelEnv) (env env' : TypeEnv) (a : Site) x τ ms,
     lookup env.varEnv x = some (.validVar, τ, ms) →
     not_borrowed x env →
     notIn env.siteEnv a →
     env' = {env with varEnv := update env.varEnv x (.invalidVar, τ, ms)
                      siteEnv := insert env.siteEnv a τ} →
     typecheck_stmt lenv env (.letBind a (.usage (.move x))) env'

  -- let a = copy(x) where x has basic type
  | let_bind_copy_val : ∀ (lenv : LabelEnv) (env env' : TypeEnv) (a : Site) x bt ms,
     lookup env.varEnv x = some (.validVar, .basic bt, ms) →
     notIn env.siteEnv a →
     env' = {env with siteEnv := insert env.siteEnv a (.basic bt)} →
     typecheck_stmt lenv env (.letBind a (.usage (.copy x))) env'

  -- let a = copy(x) where x has reference type
  | let_bind_copy_ref : ∀ (lenv : LabelEnv) (env env' : TypeEnv) (a : Site) x τ ms (s t : Aref) isBor,
     lookup env.varEnv x = some (.validVar, .ref τ s isBor, ms) →
     notIn env.siteEnv a →
     freshRefBool t env.pathEnv →
     env' = {env with siteEnv := insert env.siteEnv a (.ref τ t isBor)
                      pathEnv := update_with_epsilon s t env.pathEnv} →
     typecheck_stmt lenv env (.letBind a (.usage (.copy x))) env'

  -- let a = &x (immutable borrow)
  | let_bind_borrowImm : ∀ (lenv : LabelEnv) (env env' : TypeEnv) (a : Site) x τ ms (r : Aref),
     lookup env.varEnv x = some (.validVar, .basic τ, ms) →
     notIn env.siteEnv a →
     freshRefBool r env.pathEnv →
     env' = {env with siteEnv := insert env.siteEnv a (.ref τ r .siteBorrowImm)
                      pathEnv := update_with_epsilon r r env.pathEnv |>
                                 update_with_extension .root r [.root_to_var x]} →
     typecheck_stmt lenv env (.letBind a (.usage (.borrowImm x))) env'

  -- let a = &mut x (mutable borrow)
  | let_bind_borrowMut : ∀ (lenv : LabelEnv) (env env' : TypeEnv) (a : Site) x τ ms (r : Aref),
     LE.le .mutable ms →
     lookup env.varEnv x = some (.validVar, .basic τ, ms) →
     notIn env.siteEnv a →
     freshRefBool r env.pathEnv →
     env' = {env with siteEnv := insert env.siteEnv a (.ref τ r .siteBorrowMut)
                      pathEnv := update_with_epsilon r r env.pathEnv |>
                                 update_with_extension .root r [.root_to_var x]} →
     typecheck_stmt lenv env (.letBind a (.usage (.borrowMut x))) env'

  -- let a = n (integer literal)
  | let_bind_intLit : ∀ (lenv : LabelEnv) (env env' : TypeEnv) (a : Site) (n : Nat),
     notIn env.siteEnv a →
     env' = {env with siteEnv := insert env.siteEnv a (.basic .u64)} →
     typecheck_stmt lenv env (.letBind a (.intLit n)) env'

  -- let af = &a.T::f (field borrow)
  | let_bind_borrowField : ∀ (lenv : LabelEnv) (env env' : TypeEnv) (a af : Site) f bt bt' isBor fentries s (rf : Aref),
     lookup env.siteEnv a = some (.ref bt s isBor) →
     bt = .trecord fentries →
     lookup fentries f = some bt' →
     notIn env.siteEnv af →
     freshRef rf env.pathEnv →
     env' = {env with siteEnv := insert (delete env.siteEnv a) af (.ref bt' rf isBor)
                      pathEnv := update_with_extension s rf [.field f] env.pathEnv} →
     typecheck_stmt lenv env (.letBind af (.borrowField a bt f)) env'

  -- let af = &mut a.T::f (mutable field borrow)
  | let_bind_borrowMutField : ∀ (lenv : LabelEnv) (env env' : TypeEnv) (a af : Site) f bt btf fentries (s rf : Aref),
     lookup env.siteEnv a = some (.ref bt s .siteBorrowMut) →
     bt = .trecord fentries →
     lookup fentries f = some btf →
     notIn env.siteEnv af →
     freshRef rf env.pathEnv →
     env' = {env with siteEnv := insert (delete env.siteEnv a) af (.ref btf rf .siteBorrowMut)
                      pathEnv := update_with_extension s rf [.field f] env.pathEnv} →
     typecheck_stmt lenv env (.letBind af (.borrowMutField a bt f)) env'

  -- let c = a ⊕ b (binary operation)
  | let_bind_binop : ∀ (lenv : LabelEnv) (env env' : TypeEnv) bop bt1 bt2 bt3 (a b c : Site),
     lookup env.siteEnv a = some (.basic bt1) →
     lookup env.siteEnv b = some (.basic bt2) →
     binop_type bop bt1 bt2 = some bt3 →
     notIn env.siteEnv c →
     env' = {env with siteEnv := insert (delete (delete env.siteEnv a) b) c (.basic bt3)} →
     typecheck_stmt lenv env (.letBind c (.binop bop a b)) env'

  -- let c = *a (dereference)
  | let_bind_readRef : ∀ (lenv : LabelEnv) (env env' : TypeEnv) (a c : Site) r (τ : BasicMoveType) isBor,
     lookup env.siteEnv a = some (.ref τ r isBor) →
     notIn env.siteEnv c →
     env' = {env with siteEnv := insert (delete env.siteEnv a) c (.basic τ)
                      pathEnv := delete_ref_node env.pathEnv r} →
     typecheck_stmt lenv env (.letBind c (.readRef a)) env'

  -- let c = freeze a
  | let_bind_freeze : ∀ (lenv : LabelEnv) (env env' : TypeEnv) (a c : Site) (τ : BasicMoveType) (r r' : Aref) isBor,
     lookup env.siteEnv a = some (.ref τ r isBor) →
     notIn env.siteEnv c →
     freshRef r' env.pathEnv →
     env' = {env with siteEnv := insert (delete env.siteEnv a) c (.ref τ r' .siteBorrowImm)
                      pathEnv := consume_ref_transfer env.pathEnv r r'} →
     typecheck_stmt lenv env (.letBind c (.freeze a)) env'

  -- let b = T { f1: a1, ..., fn: an } (pack)
  | let_bind_pack : ∀ (lenv : LabelEnv) (env env' : TypeEnv) (b : Site) (recName : Id)
      (fields : List (Field × Site)) (fentries : AssocMap Field BasicMoveType),
     notIn env.siteEnv b →
     (∀ f a, (f, a) ∈ fields →
        ∃ (bt : BasicMoveType), lookup env.siteEnv a = some (.basic bt) ∧
                                lookup fentries f = some bt) →
     (∀ a₁ a₂, (∃ f₁ f₂, (f₁, a₁) ∈ fields ∧ (f₂, a₂) ∈ fields ∧ f₁ ≠ f₂) → a₁ ≠ a₂) →
     env' = {env with siteEnv := insert (deleteAll env.siteEnv (fields.map Prod.snd)) b (.basic (.trecord fentries))} →
     typecheck_stmt lenv env (.letBind b (.pack recName fields)) env'

  -- *a = b
  | write_ref : ∀ (lenv : LabelEnv) (env env' : TypeEnv) a b τ (r: Aref),
      -- a is of type reference to a basic typ τ, its aref is s
      AssocMap.lookup env.siteEnv a = some (.ref τ r .siteBorrowMut) →
      -- b has the same basic type
      AssocMap.lookup env.siteEnv b = some (.basic τ) →
      -- [Path Checking] This is an important check to ensure the absence of
      -- dangling pointers. All outbound edges from a.s are ε: nothing extends
      -- this reference. This ensures no dangling references.  We don't care
      -- about inbound edges: they won't cause dangling references
      check_outbound env.pathEnv r (λ r ↦ r = .ε ∨ r = .empty) →
      -- remove all involved sites a and b from the environment
      -- retire the abstract reference s
      env' = {env with siteEnv := delete (delete env.siteEnv b) a
                       pathEnv := garbage_collect env.pathEnv r } →
      typecheck_stmt lenv env (.writeRef a b) env'

  -- x = a // x is a valid var
  -- Inlines typecheck_usage.t_uborrowMut_val for the mutable borrow of x
  | var_assign_valid : ∀ (lenv : LabelEnv) (env env' env'' : TypeEnv) x a ax τ ms (r : Aref),
      -- Premises from t_uborrowMut_val (mutable borrow of x into intermediate site ax):
      LE.le .mutable ms →
      lookup env.varEnv x = some (.validVar, .basic τ, ms) →
      notIn env.siteEnv ax →
      freshRefBool r env.pathEnv →
      env' = {env with siteEnv := insert env.siteEnv ax (.ref τ r .siteBorrowMut)
                       pathEnv := update_with_epsilon r r env.pathEnv |>
                                  update_with_extension .root r [.root_to_var x]} →
      -- Then write through the reference (ax will be removed from env'')
      typecheck_stmt lenv env' (.writeRef ax a) env'' →
      typecheck_stmt lenv env (.assign x a) env''

  -- x = a // x is an invalid variable
  | var_assign_invalid : ∀ (lenv : LabelEnv) (env env' : TypeEnv) x a τ,
    -- Only works if x invalid
    AssocMap.lookup env.varEnv x = some (.invalidVar, τ, .mutable) →
    -- Checking the type confromance
    AssocMap.lookup env.siteEnv a = some τ →
    typecheck_stmt lenv env (.assign x a) env'

  -- let (a1, ..., an) = f(b1, ..., bm) // Call
  | call : ∀ (lenv : LabelEnv) (env env' : TypeEnv) fnName (as bs: List Site) (params rets : List ParamType),
    -- Check that as are all fresh
    all_fresh_sites env as →
    -- Check that the function exists
    AssocMap.lookup env.funEnv fnName = some ⟨params, rets⟩  →
    -- Check type conformance for parameters and return types
    types_conform env.siteEnv bs params →
    types_conform env.siteEnv as rets →
    -- Validation: No mutable input reaches any other input
    check_mutable_inputs_isolated env bs →
    -- Validation: All mutable inputs have non-trivial outbound edges
    check_mutable_inputs_have_outbound env bs →
    -- Update environment: remove input sites, add output sites, connect paths
    env' = call_connect_inputs_outputs env as bs →
    typecheck_stmt lenv env (.call as fnName bs) env'

  -- s1; s2 // Sequential composition
  -- Threads the environment through: s1 produces env', which becomes input to s2
  | seq : ∀ (lenv : LabelEnv) (env env' env'' : TypeEnv) s1 s2,
    -- Type check first statement, transforming env to env'
    typecheck_stmt lenv env s1 env' →
    -- Type check second statement, transforming env' to env''
    typecheck_stmt lenv env' s2 env'' →
    -- The final environment is the result of executing both statements in sequence
    typecheck_stmt lenv env (.seq s1 s2) env''

  -- release(a)
  -- Explicitly release a reference, consuming it without producing any value
  | release : ∀ (lenv : LabelEnv) (env env' : TypeEnv) (a : Site) (τ : BasicMoveType) (r : Aref) isBor,
    -- Site a must hold a reference
    AssocMap.lookup env.siteEnv a = some (.ref τ r isBor) →
    -- Remove site a and delete reference r from pathEnv
    env' = {env with siteEnv := delete env.siteEnv a
                     pathEnv := delete_ref_node env.pathEnv r } →
    typecheck_stmt lenv env (.release a) env'

  -- T { f1: a1, ..., fn: an } = b
  -- Unpack a record into its constituent field sites (dual of pack expression)
  | unpack : ∀ (lenv : LabelEnv) (env env' : TypeEnv) (fields : List (Field × Site)) (b : Site) (fentries : AssocMap Field BasicMoveType),
    -- b must hold a record type
    AssocMap.lookup env.siteEnv b = some (.basic (.trecord fentries)) →
    -- All output field sites must be fresh
    (∀ (f : Field) (a : Site), (f, a) ∈ fields → AssocMap.notIn env.siteEnv a) →
    -- All output field sites must be distinct (no aliasing)
    (∀ a₁ a₂, (∃ f₁ f₂, (f₁, a₁) ∈ fields ∧ (f₂, a₂) ∈ fields ∧ f₁ ≠ f₂) → a₁ ≠ a₂) →
    -- Fields in unpack must match record's field entries
    (∀ (f : Field) (a : Site), (f, a) ∈ fields → ∃ bt, AssocMap.lookup fentries f = some bt) →
    -- Environment update: remove b, add all field sites with their types
    env' = {env with siteEnv := addFieldSites fentries (delete env.siteEnv b) fields} →
    typecheck_stmt lenv env (.unpack fields b) env'


/- ---------------------------------------------------- -/
/-       Type checking relation for terminators          -/
/- ---------------------------------------------------- -/

/--
Type checking relation for block terminators (control flow).

Judgment form: `Λ; ⟨Γ⟩ ⊢ t`

This relation handles all terminator forms that end a block:
- **jump L**: Unconditional jump to label L
- **branch a L1 L2**: Conditional branch based on boolean site a
- **ret [a1, ..., an]**: Return from function with values
- **abort a**: Abort execution (error path)

Components:
- `lenv`: Label environment mapping labels to expected entry TypeEnvs
- `env`: Type environment at the end of the block (after executing body)
- `Terminator`: The terminator being type checked
- `returnType`: The function's return type (for ret checking)

Key invariants:
⋆ Jump targets must exist in lenv and environment must be equivalent to target's expected env
⋆ Branch requires boolean condition and environment must match both targets (after consuming condition)
⋆ Return values must match the function's declared return type
⋆ No local variables may be borrowed at return (prevents escaping references)
-/
inductive typecheck_terminator : LabelEnv → TypeEnv → Terminator → MoveType → Prop where
  -- jump L // Unconditional jump to label L
  -- The current environment must be equivalent to the environment expected at label L
  | t_jump : ∀ (lenv : LabelEnv) (env : TypeEnv) (L : Label) (envL : TypeEnv) retType,
    -- Look up the expected environment for label L
    AssocMap.lookup lenv L = some envL →
    -- Current environment must be equivalent to the target label's environment
    TypeEnv.equiv env envL →
    typecheck_terminator lenv env (Terminator.jump L) retType

  -- branch a L1 L2 // If (a) goto L1 else goto L2
  -- The site a must hold a boolean, and the environment must match both targets
  | t_branch : ∀ (lenv : LabelEnv) (env : TypeEnv) (a : Site) (L1 L2 : Label) (envL1 envL2 : TypeEnv) retType,
    -- Site a must hold a boolean value
    AssocMap.lookup env.siteEnv a = some (.basic .tbool) →
    -- Look up the expected environment for label L1
    AssocMap.lookup lenv L1 = some envL1 →
    -- Look up the expected environment for label L2
    AssocMap.lookup lenv L2 = some envL2 →
    -- Current environment (minus the condition site) must be equivalent to L1's environment
    TypeEnv.equiv {env with siteEnv := delete env.siteEnv a} envL1 →
    -- Current environment (minus the condition site) must be equivalent to L2's environment
    TypeEnv.equiv {env with siteEnv := delete env.siteEnv a} envL2 →
    typecheck_terminator lenv env (Terminator.branch a L1 L2) retType

  -- return (a1, ..., an) // Return from function
  -- Return values must have the expected return type
  | t_ret : ∀ (lenv : LabelEnv) (env : TypeEnv) (as : List Site) τ,
    -- All sites must have the same type τ (simplified: single return value)
    -- For multiple return values, check each matches expected type
    (∀ a, a ∈ as → AssocMap.lookup env.siteEnv a = some τ) →
    -- All sites must be consumed (removed from environment)
    -- No local variables may be borrowed (prevents references from escaping)
    no_locals_borrowed env →
    typecheck_terminator lenv env (Terminator.ret as) τ

  -- abort a // Abort execution with error value
  -- Control never continues past abort
  | t_abort : ∀ (lenv : LabelEnv) (env : TypeEnv) (a : Site) τ retType,
    -- Site a must exist (consumed by abort)
    AssocMap.lookup env.siteEnv a = some τ →
    typecheck_terminator lenv env (Terminator.abort a) retType


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
  The block's body is type checked starting from the expected environment for its label,
  producing an intermediate environment, then the terminator is checked against that environment.
-/
def typecheck_block (lenv : LabelEnv) (block : Block) (expectedEnv : TypeEnv) (retType : MoveType) : Prop :=
  ∃ midEnv, typecheck_stmt lenv expectedEnv block.body midEnv ∧
            typecheck_terminator lenv midEnv block.terminator retType

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
  5. Type checking each block's terminator against the resulting environment
  6. Verifying the entry block starts with the initial environment

  Control flow is handled entirely by terminators (jump, branch, ret, abort).
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
    (∀ entryLabel entryBody entryTerm entryEnv,
      f.blocks.head? = some ⟨entryLabel, entryBody, entryTerm⟩ →
      AssocMap.lookup lenv entryLabel = some entryEnv →
      TypeEnv.equiv entryEnv initEnv) →
    -- Every block must type check: body produces an environment, then terminator is checked
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



end LeanMove.Checker
