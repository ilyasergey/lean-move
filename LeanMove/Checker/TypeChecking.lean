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
abbrev AlocEnv := AssocMap Aloc MoveType

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

-- z = &x
def update_with_epsilon (z x : Aref) (pe: PathEnv)  : PathEnv :=
  update_with_extension z x [] pe


def delete_ref_node (pe: PathEnv) (r : Aref) : PathEnv :=
  let G := pe.paths
  let paths' := fun (u, v) => if u = r ∨ v = r then Regex.empty else G (u, v)
  { pe with refs  := List.filter (fun r' => r' ≠ r) pe.refs,
            paths := paths' }


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
  -- For x not to be borrowed, all abstract location of the reference type that
  -- are borrowed should not  coincide with x
  ∀ a b τ isBor, AssocMap.lookup env.alocEnv a = some (.ref τ b isBor) →
    match isBor with
    | .siteBorrowImm x' => x' ≠ x
    | .siteBorrowMut x' => x' ≠ x
    | .siteNotBorrowed => true

/--
Invariants:
⋆ Every sites that belongs to a variable (e.g., x) is reachable from the root via path "x"
 -/
inductive typecheck_usage : TypeEnv → Usage → TypeEnv → Aloc -> MoveType → Prop where
  | t_umove : ∀ env env' x τ ms a,
     AssocMap.lookup env.varEnv x = some (.validVar, τ, ms) →
     not_borrowed x env →
     notIn env.alocEnv a →
     env' = { env with varEnv  := update env.varEnv x (.invalidVar, τ, ms)
                       alocEnv := insert env.alocEnv a τ } →
     typecheck_usage env (.move x) env' a τ

  -- Copying a variable value, not a reference
  | t_ucopy_val : ∀ env env' x bt ms a,
     AssocMap.lookup env.varEnv x = some (.validVar, .basic bt, ms) →
     notIn env.alocEnv a →
     env' = { env with alocEnv := insert env.alocEnv a (.basic bt)} →
     typecheck_usage env (.copy x) env' a (.basic bt)

  -- Copying a reference value
  | t_ucopy_ref : ∀ env env' x τ ms a (s t: Aref) isBor,
     AssocMap.lookup env.varEnv x = some (.validVar, .ref τ s isBor, ms) →
     notIn env.alocEnv a →
     freshRef t env.pathEnv →
     env' = { env with alocEnv := insert env.alocEnv a (.ref τ t isBor)
                       -- [Fun fact] since s is reachable from the root, so is t now
                       pathEnv := update_with_epsilon s t env.pathEnv } →
     typecheck_usage env (.copy x) env' a (.ref τ t isBor)

  -- Borrowing the reference to a variable's content, makes a new reference r
  | t_uborrowImm_val : ∀ env env' x τ ms a (r: Aref),
     AssocMap.lookup env.varEnv x = some (.validVar, .basic τ, ms) →
     AssocMap.notIn env.alocEnv a →
     freshRef r env.pathEnv →
     env' = { env with alocEnv := insert env.alocEnv a (.ref τ r (.siteBorrowImm x))
                       -- The graph is updated with a var-transition from from Root to r
                       pathEnv := update_with_epsilon r r env.pathEnv |>
                                  update_with_extension .root r [.root_to_var x] } →
     typecheck_usage env (.borrowImm x) env' a (.ref τ r (.siteBorrowImm x))

  -- Mutable borrow to a value
  | t_uborrowMut_val : ∀ env env' x τ ms a (r: Aref),
     LE.le .mutable ms  →
     AssocMap.lookup env.varEnv x = some (.validVar, .basic τ, ms) →
     AssocMap.notIn env.alocEnv a →
     freshRef r env.pathEnv →
     env' = { env with alocEnv := insert env.alocEnv a (.ref τ r (.siteBorrowMut x))
                       -- The graph is updated with a var-transition from from Root to r
                       pathEnv := update_with_epsilon r r env.pathEnv |>
                                  update_with_extension .root r [.root_to_var x]  } →
     typecheck_usage env (.borrowMut x) env' a (.ref τ r (.siteBorrowMut x))

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

-- ⟨L; E; G⟩ ⊢ (e : expr) ⤳ ⟨L'; E'; G'⟩; a; τ

/-
-- TODO add freezing
     [ ] freeze(a)
        -- a should be of type reference
        -- creates an immutable reference r and an immutable ε-extension from this refernce
 -/

inductive typecheck_expr : TypeEnv → Expr → TypeEnv → Aloc → MoveType → Prop where

  -- a <- u (see above)
  | usage : ∀ env env' u (a : Aloc) (τ : MoveType),
     typecheck_usage env u env' a τ ->
     typecheck_expr env (Expr.usage u) env' a τ

  -- af <- &a.T::f
  -- [Q] Does a have to have a reference type? Can it be a value?
  | borrowField : ∀ env env' a f af bt bt' isBor fentries s (rf : Aref),
     -- Site type is τ basic type
     AssocMap.lookup env.alocEnv a = some (.ref bt s isBor) →
     -- This is a record type, here are its entries
     bt = .trecord fentries →
     -- Get the field type via the name f
     lookup fentries f = some bt' →
     AssocMap.notIn env.alocEnv af →
     freshRef rf env.pathEnv →
     -- Update site environment with the new reference
     env' = {env with alocEnv := insert (delete env.alocEnv a) af (.ref bt' rf isBor)
                      pathEnv := update_with_extension s rf [.field f] env.pathEnv  } →
     typecheck_expr env (Expr.borrowField a bt f) env' af (.ref bt' rf isBor)

  -- &mut af <- a.T::f
  | borrowMutField : ∀ env env' a f x af bt btf fentries (s rf : Aref),
     -- Site type is τ basic type
     AssocMap.lookup env.alocEnv a = some (.ref bt s (.siteBorrowMut x)) →
     -- This is a record type, here are its entries
     bt = .trecord fentries →
     -- Get the field type via the name f
     lookup fentries f = some btf →
     AssocMap.notIn env.alocEnv af →
     freshRef rf env.pathEnv →
     -- Update site environment with the new reference
     env' = {env with alocEnv := insert (delete env.alocEnv a) af (.ref btf rf (.siteBorrowMut x))
                      pathEnv := update_with_extension s rf [.field f] env.pathEnv } →
     typecheck_expr env (Expr.borrowField a bt f) env' af (.ref btf rf (.siteBorrowMut x))

  -- c <- a ⊕ b
  | binop : ∀ env env' bop bt1 bt2 bt3 (a b c : Aloc),
     AssocMap.lookup env.alocEnv a = some (.basic bt1) →
     AssocMap.lookup env.alocEnv b = some (.basic bt2) →
     binop_type bop bt1 bt2 = some bt3 →
     AssocMap.notIn env.alocEnv c →
     env' = {env with alocEnv := insert (delete (delete env.alocEnv a) b) c (.basic bt3)} ->
     typecheck_expr env (Expr.binop bop a b) env' c (.basic bt3)

  -- c <- *a
  | readRef : ∀ env env' (a c : Aloc) r (τ : BasicMoveType) isBor,
     AssocMap.lookup env.alocEnv a = some (.ref τ r isBor) →
     AssocMap.notIn env.alocEnv c →
     env' = {env with alocEnv := insert (delete env.alocEnv a) c (.basic τ)
                      pathEnv := delete_ref_node env.pathEnv r } →
     typecheck_expr env (Expr.readRef a) env' c (.basic τ)

  -- TODO: implement me!
  -- b <-- T { f: a1, ...,  f: an }
  | pack : ∀ env env' fs as ts bs b τ,
     -- retrieve types for all as from env.alocEnv
     -- [TODO]: Okay, this is straightforward, but requires a few auxiliary functions
     -- Will do so later
     -- Remove all as from env.alocEnv
     typecheck_expr env (Expr.pack fs as) env' b τ

inductive typecheck_stmt : TypeEnv → Stmt → TypeEnv → Prop where
  | skip : ∀ env, typecheck_stmt env .skip env

  | let_bind : ∀ env env' a e τ,
     typecheck_expr env e env' a τ →
     typecheck_stmt env (.letBind a e) env'


  -- *a = b
  | write_ref : ∀ env env' a b τ (r: Aref),
      -- a is of type reference to a basic typ τ, its aref is s
      AssocMap.lookup env.alocEnv a = some (.ref τ r (.siteBorrowMut _)) →
      -- b has the same basic type
      AssocMap.lookup env.alocEnv b = some (.basic τ) →
      -- [Path Checking] This is an important check to ensure the absence of
      -- dangling pointers. All outbound edges from a.s are ε: nothing extends
      -- this reference. This ensures no dangling references.  We don't care
      -- about inbound edges: they won't cause dangling references
      check_outbound env.pathEnv r (λ r ↦ r = .ε ∨ r = .empty) →
      -- remove all involved sites a and b from the environment
      -- retire the abstract reference s
      env' = {env with alocEnv := delete (delete env.alocEnv b) a
                       pathEnv := garbage_collect env.pathEnv r } →
      typecheck_stmt env (.writeRef a b) env'

  -- x = a // x is a valid var
  | var_assign_valid : ∀ env env' env'' x a ax rtype,
      -- Take a mutable borrow to a variable, so that `ax` is an "intermediate"
      -- site holding its reference location. The usage check below will also nicely
      typecheck_usage env (.borrowMut x) env' ax rtype →
      -- So we reduce it  to the previous case of writing to a reference.
      -- Another nice touch is that the intermediate `ax` will be removed from
      -- `env''` at the end.
      typecheck_stmt env' (.writeRef ax a) env'' →
      typecheck_stmt env (.assign x a) env''

  -- x = a // x is an invalid variable
  | var_assign_invalid : ∀ env env' x a τ,
    AssocMap.lookup env.varEnv x = some (.invalidVar, τ, .mutable) →
    AssocMap.lookup env.alocEnv a = some τ →
    typecheck_stmt env (.assign x a) env'



  /- Done above this line -/

/-
TODO: add constructors for these cases:
    [v] let a = e            // Evaluate a simple expr, assign it an abstract locations

    [v] *a = b               // Write into a reference
        -- a is a type of reference,
        -- all outbound edges are ε: nothing extends this reference
        -- aliasing is okay
        -- We don't care about inbound edges
        -- This should ensure no dangling references
        -- b has basic type
        -- we consume both a and b
        -- the abstract reference within the type of a is released
    [v] x = a                // Assign a value to a variable
        -- Invalid var is easy: we known it's not borrowed (this is an invariant)
        -- A shortcut: make a mutable reference to x and then repeat the steps from above

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
