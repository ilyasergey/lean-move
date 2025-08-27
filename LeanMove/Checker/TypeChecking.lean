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

-- Whether the variable is valid to move/copy from
-- Better than Boolean
inductive IsValid where
  | validVar
  | invalidVar
deriving Repr, DecidableEq, Inhabited, Hashable


-- Environment mapping abstract locations to their types, abstract references, and borrow marker
abbrev SiteEnv := AssocMap Site MoveType

-- Environment mapping variables to their site, types, mutability, abstract references, and borrow status
abbrev VarEnv := AssocMap Var (IsValid × MoveType × Mut)

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


-- Check that the property p holds for all paths from s in penv
def check_outbound (penv: PathEnv) (s: Aref) (p: Regex PathElement → Prop) :=
  forall s', p (penv.paths  (s, s'))

-- Garbage collect the reference from penv
def garbage_collect (penv: PathEnv) (r: Aref) : PathEnv :=
  let G := penv.paths
  let paths' := fun (u, v) => if u = r ∨ v = r then Regex.empty else G (u, v)
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
    -- [Q2] Discuss what is going on here compared ot the previous case.
    -- if u = target then der (G (source, v)) p else
    G (u, v)
  let refs' := if target ∉ pe.refs then target :: pe.refs else pe.refs
  { pe with paths := paths', refs := refs' }

-- z = &x
def update_with_epsilon (z x : Aref) (pe: PathEnv)  : PathEnv :=
  update_with_extension z x [] pe


def delete_ref_node (pe: PathEnv) (r : Aref) : PathEnv :=
  let G := pe.paths
  let paths' := fun (u, v) => if u = r ∨ v = r then Regex.empty else G (u, v)
  { pe with refs  := List.filter (fun r' => r' ≠ r) pe.refs,
            paths := paths' }


def freshRef (r: Aref) (pe: PathEnv) := r ∉ pe.refs

structure ParamType where
  -- inner type
  basicType : BasicMoveType
  -- mutable    = some true
  -- immmutable = some false
  -- not a reference = none
  isRefMut : Option Bool
deriving Repr, Inhabited, Hashable

-- Function table
structure FunSig where
  params : List ParamType
  returnType : List ParamType
deriving Repr, Inhabited, Hashable

abbrev FunEnv := AssocMap Id FunSig

-- New structure packaging all environments
structure TypeEnv where
  siteEnv : SiteEnv
  varEnv  : VarEnv
  pathEnv : PathEnv
  funEnv  : FunEnv

/- ---------------------------------------------------- -/
/-       Well-formedness of the environments            -/
/- ---------------------------------------------------- -/

structure WellFormedEnv (typeEnv : TypeEnv) where
  -- All abstract locations
  uniqueSites : uniqueKeys typeEnv.siteEnv
  -- TODO: say that for all pairs in pathEnv there is either
  -- a variable in varEnv or a site in siteEnv

/- ---------------------------------------------------- -/
/- Typing relations for usages, expressions, statements -/
/- ---------------------------------------------------- -/

open AssocMap

-- relation ⟨L; E; G⟩ ⊢ u ⤳ ⟨L'; E'; G'; Aloc; τ⟩ for the type Usage

/-
[Notes on typecheck_usage]

* Most of the constructors require fresh reference and fresh abstract location
  and  fresh reference. To simplify things those are provided externally and
  checked for being fresh within the respective rule.

* The association between a variable/aloc and the respective abstract reference
  is now packaged into the type to avoid clutter. This might bite us in the butt
  later. In any event, one needs to be careful when comparing MoveType instances
  for equality, as they might be the same "type-wise", but differ in the
  abstract references they carry. There is no such problem for basic types,
  which can be compared for equality freely.

* The logic for updating the graph are still missing, and need to be clarified
  with Todd before incorporated into the type checking rules.

 -/

 -- Check that the variable x is not borrowed by browsing through all sites
 def not_borrowed (x: Var) (env: TypeEnv) : Prop :=
  -- For x not to be borrowed, it should have no outbound edges from the root
  -- [Q3] Check that this is how the implementation does it? Is it that shallow?
  ∀ (r : Aref),
    let regex := env.pathEnv.paths (.root, r)
    forall y, interpret_regex regex [.root_to_var y] → y ≠ x

def all_fresh_sites (env: TypeEnv) (as: List Site) : Prop :=
  List.all as (fun a ↦ notIn env.siteEnv a)

/--
Invariants:
⋆ Every sites that belongs to a variable (e.g., x) is reachable from the root via path "x"
 -/
inductive typecheck_usage : TypeEnv → Usage → TypeEnv → Site -> MoveType → Prop where
  | t_umove : ∀ env env' x τ ms a,
     AssocMap.lookup env.varEnv x = some (.validVar, τ, ms) →
     -- How else we would express it?
     -- Checking by walking the graph from the local roots L.
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
     freshRef t env.pathEnv →
     env' = { env with siteEnv := insert env.siteEnv a (.ref τ t isBor)
                       -- [Fun fact] since s is reachable from the root, so is t now
                       pathEnv := update_with_epsilon s t env.pathEnv } →
     typecheck_usage env (.copy x) env' a (.ref τ t isBor)

  -- Borrowing the reference to a variable's content, makes a new reference r
  | t_uborrowImm_val : ∀ env env' x τ ms a (r: Aref),
     AssocMap.lookup env.varEnv x = some (.validVar, .basic τ, ms) →
     AssocMap.notIn env.siteEnv a →
     freshRef r env.pathEnv →
     env' = { env with siteEnv := insert env.siteEnv a (.ref τ r .siteBorrowImm)
                       -- The graph is updated with a var-transition from from Root to r
                       pathEnv := update_with_epsilon r r env.pathEnv |>
                                  update_with_extension .root r [.root_to_var x] } →
     typecheck_usage env (.borrowImm x) env' a (.ref τ r .siteBorrowImm)

  -- Mutable borrow to a value
  -- r is supposed to be the root; perhaps that needs to be made specific
  | t_uborrowMut_val : ∀ env env' x τ ms a (r: Aref),
     LE.le .mutable ms  →
     AssocMap.lookup env.varEnv x = some (.validVar, .basic τ, ms) →
     AssocMap.notIn env.siteEnv a →
     freshRef r env.pathEnv →
     env' = { env with siteEnv := insert env.siteEnv a (.ref τ r (.siteBorrowMut))
                       -- The graph is updated with a var-transition from from Root to r
                       pathEnv := update_with_epsilon r r env.pathEnv |>
                                  update_with_extension .root r [.root_to_var x]  } →
     typecheck_usage env (.borrowMut x) env' a (.ref τ r .siteBorrowMut)

/- ---------------------------------------------------- -/
/- Typing relations for expressions -/
/- ---------------------------------------------------- -/

-- function to take a binop and types of its arguments and return the type of the result
def binop_type (bop : Binop) (τ1 τ2 : BasicMoveType) : Option BasicMoveType :=
  match (bop, τ1, τ2) with
  | (.add, .tint, .tint) => some .tint
  | (.sub, .tint, .tint) => some .tint
  | (.mul, .tint, .tint) => some .tint
  | (.div, .tint, .tint) => some .tint
  | (.mod, .tint, .tint) => some .tint
  | (.lt,  .tint, .tint) => some .tbool
  | (.eq, .tint, .tint) =>  some .tbool
  | (.eq, .tbool, .tbool) => some .tbool
  | (.nand, .tbool, .tbool) => some .tbool
  | _ => none

-- Check that a list of sites conforms to a list of parameter types
-- No submtyping,
def types_confrom (alocEnv : SiteEnv) (sites : List Site) (paramTypes : List ParamType) : Prop :=
  match sites, paramTypes with
  | [], [] => True
  | site :: sites', paramType :: paramTypes' =>
    match AssocMap.lookup alocEnv site with
    | some τ =>
      -- the formal is on the left, the actual is on the right
      match paramType, τ with
      | ⟨bt, none⟩, .basic bt' => bt = bt' ∧ types_confrom alocEnv sites' paramTypes'
      | ⟨bt, some isRefMut⟩, .ref τ _ isBor =>
        bt = τ ∧
        (match isRefMut, isBor with
         | true, .siteBorrowMut => True -- only mutables here
         | false, .siteBorrowImm => True -- for immutable parameter referenes, the actual can be anything (mut/imm)
         | _, _ => False) ∧
        types_confrom alocEnv sites' paramTypes'
      | _, _ => False
    -- Type is not found for the site
    | none => False
  -- Mismatch in sizes
  | _, _ => False

-- ⟨L; E; G⟩ ⊢ (e : expr) ⤳ ⟨L'; E'; G'⟩; a; τ


inductive typecheck_expr : TypeEnv → Expr → TypeEnv → Site → MoveType → Prop where

  -- c <- u (see above)
  | usage : ∀ env env' u (c : Site) (τ : MoveType),
     typecheck_usage env u env' c τ ->
     typecheck_expr env (Expr.usage u) env' c τ

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
     typecheck_expr env (Expr.borrowField a bt f) env' af (.ref btf rf .siteBorrowMut)

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

  | freeze : ∀ env env' a c (τ : BasicMoveType) (r r': Aref) isBor x,
    -- [Q] Are there any constraints on a? Does it make a difference whether a
    -- is a reference borrowed mutably or immutably?
    AssocMap.lookup env.siteEnv a = some (.ref τ r isBor) →
    -- creates an immutable reference r' and an immutable ε-extension from this refernce
    AssocMap.notIn env.siteEnv c →
    freshRef r' env.pathEnv →
    env' = {env with siteEnv := insert (delete env.siteEnv a) c (.ref τ r' .siteBorrowImm)
                     pathEnv := update_with_epsilon r r' env.pathEnv } →
    typecheck_expr env (Expr.freeze a) env' c (.ref τ r' .siteBorrowImm)

  -- TODO: implement me!
  -- b <-- T { f: a1, ...,  f: an }
  | pack : ∀ env env' fs as ts bs b τ,
     -- retrieve types for all as from env.alocEnv
     -- [TODO]: Okay, this is straightforward, but requires a few auxiliary functions
     -- Will do so later
     -- Remove all as from env.alocEnv
     typecheck_expr env (Expr.pack fs as) env' b τ

-- let (a1, ..., an) = f(b1, ..., bm) // Call
-- [Q2] is it okay that we exclude this signature, as it over-approximates what is actually passed
-- as actuals and we have already ensured confromance?

def call_connect_inputs_outputs (env: TypeEnv) (as bs: List Site) : TypeEnv :=
  let inputs := List.filterMap (fun a ↦ match AssocMap.lookup env.siteEnv a with
    | some (.ref _ r _) => some r
    | _ => none) bs
  let mi := List.filterMap (fun a ↦ match AssocMap.lookup env.siteEnv a with
    | some (.ref _ r .siteBorrowMut) => some r
    | _ => none) bs
  let ii := List.filterMap (fun a ↦ match AssocMap.lookup env.siteEnv a with
    | some (.ref _ r .siteBorrowImm) => some r
    | _ => none) bs
  -- The following two are problematic: what exactly are the `_x` in the references?
  let mo := List.filterMap (fun a ↦ match AssocMap.lookup env.siteEnv a with
    | some (.ref _ r .siteBorrowMut) => some r
    | _ => none) as
  let io := List.filterMap (fun a ↦ match AssocMap.lookup env.siteEnv a with
    | some (.ref _ r .siteBorrowImm) => some r
    | _ => none) as

  -- For any immutable output, it will be .*-extended from any input (mutable and immutable)
  let with_io_from_inputs : PathEnv := List.foldl (fun env iout ↦
    let res := List.foldl (fun env' input ↦ extend_with_star input iout env') env inputs
    res) env.pathEnv io

  -- TODO: finish the others

/-
        -- Consider 4 sets:
           * All mutable inputs (MI)
           * All immutable inputs (II)
           * All mutable outputs (MO)
           * All immutable outputs (IO)

           We can disregard any inputs/outputs of basic types

           For any immutable output, it will be .*-extended from any input (mutable and immutable)

           For any mutable output, it will be .*-extended from any mutable input

           All outputs will be .*-extended from each other, except
              - there should be no edges between mutable outputs
              - mutable outputs cannot reach each other or another output
              - same from immutable to mutable

           Similar property is enforced for inputs
              - No mutable inputs allow to reach any other inputs
                (i.e., non-reachable in the graph, ∨ia ε or by paths)
              - All mutable inputs have outbound edges other than ε
-/


  env

inductive typecheck_stmt : TypeEnv → Stmt → TypeEnv → Prop where
  | skip : ∀ env, typecheck_stmt env .skip env

  | let_bind : ∀ env env' a e τ,
     typecheck_expr env e env' a τ →
     typecheck_stmt env (.letBind a e) env'

  -- *a = b
  | write_ref : ∀ env env' a b τ (r: Aref),
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
      typecheck_stmt env (.writeRef a b) env'

  -- x = a // x is a valid var
  | var_assign_valid : ∀ env env' env'' x a ax rtype,
      -- Take a mutable borrow to a variable, so that `ax` is an "intermediate"
      -- site holding its reference location. The usage check below will also nicely
      -- ensure that the variable `x` is actually valid.
      typecheck_usage env (.borrowMut x) env' ax rtype →
      -- So we reduce it  to the previous case of writing to a reference.
      -- Another nice touch is that the intermediate `ax` will be removed from
      -- `env''` at the end.
      typecheck_stmt env' (.writeRef ax a) env'' →
      typecheck_stmt env (.assign x a) env''

  -- x = a // x is an invalid variable
  | var_assign_invalid : ∀ env env' x a τ,
    -- Only works if x invalid
    AssocMap.lookup env.varEnv x = some (.invalidVar, τ, .mutable) →
    -- Checking the type confromance
    AssocMap.lookup env.siteEnv a = some τ →
    typecheck_stmt env (.assign x a) env'

  -- let (a1, ..., an) = f(b1, ..., bm) // Call
  | call : ∀ env env' fnName (as bs: List Site) (params rets : List ParamType),
    -- Check that as are all fresh
    all_fresh_sites env as →
    -- Check type conformance for parameters and return types
    types_confrom env.siteEnv bs params →
    types_confrom env.siteEnv as rets →
    -- Check that the function exists
    AssocMap.lookup env.funEnv fnName = some ⟨params, rets⟩  →
    -- Check that the arguments are of the correct type


    -- Check that the return type is of the correct type
    typecheck_stmt env (.call as fnName bs) env'

  /- Done above this line -/

/-

    [ ] let (a1, ..., an) = f(b1, ..., bm) // Call
        -- Check the types of parameters and their mutability annotations
        -- No subtyping
        -- Consider 4 sets:
           * All mutable inputs (MI)
           * All immutable inputs (II)
           * All mutable outputs (MO)
           * All immutable outputs (IO)

           We can disregard any inputs/outputs of basic types

           For any immutable output, it will be .*-extended from any input (mutable and immutable)

           For any mutable output, it will be .*-extended from any mutable input

           All outputs will be .*-extended from each other, except
              - there should be no edges between mutable outputs
              - mutable outputs cannot reach each other or another output
              - same from immutable to mutable

           Similar property is enforced for inputs
              - No mutable inputs allow to reach any other inputs
                (i.e., non-reachable in the graph, ∨ia ε or by paths)
              - All mutable inputs have outbound edges other than ε

    [ ] return (a1, ..., an) // Return
           Enforces constraints similar to what call does for its inputs

           Everything except in the return is released


    [ ] T { fi: ai, ...} = b // Unpack, consuming, hence no aliasing
    [ ] abort a              // Abort the transaction, aka panic!
    [ ] release(a)           // Invalidates a reference
    [ ] { s;+ }              // Block
    [ ] if (a) s else s      // If/loop condition is always a variable [?]
    [ ] while (x) s

 -/


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
