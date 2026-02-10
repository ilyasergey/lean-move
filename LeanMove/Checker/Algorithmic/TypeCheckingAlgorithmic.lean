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
# Algorithmic Type Checking for MoveLight

This file contains the algorithmic (executable) type checker that mirrors
the relational specification in `TypeChecking.lean`.

## Contents
- `check_stmt` - Algorithmic statement type checking, returns `Option TypeEnv`
- `check_fun` - Algorithmic function type checking, returns `Bool`
-/

namespace LeanMove.Checker

open Lang
open Lang.MoveLight
open AssocMap
open Regex

/-- Boolean version of not_borrowed for algorithmic type checking.
    Uses the general regex matcher to check that no path from root accepts [.root_to_var x]. -/
def not_borrowed_bool (x: Var) (env: TypeEnv) : Bool :=
  env.pathEnv.refs.all fun r =>
    let regex := env.pathEnv.paths (.root, r)
    !match_bool regex [.root_to_var x]

/-- Boolean equality for Regex -/
def regexBeq [BEq α] : Regex α → Regex α → Bool
  | .empty, .empty => true
  | .ε, .ε => true
  | .char a, .char b => a == b
  | .dot, .dot => true
  | .union r1 r2, .union s1 s2 => regexBeq r1 s1 && regexBeq r2 s2
  | .concat r1 r2, .concat s1 s2 => regexBeq r1 s1 && regexBeq r2 s2
  | .star r, .star s => regexBeq r s
  | .deriv r a, .deriv s b => regexBeq r s && a == b
  | _, _ => false

/-- Boolean check for TypeEnv.equiv -/
def TypeEnv.equiv_bool (env1 env2 : TypeEnv) : Bool :=
  lookup_equiv_bool env1.siteEnv env2.siteEnv &&
  lookup_equiv_bool env1.varEnv env2.varEnv &&
  env1.pathEnv.refs == env2.pathEnv.refs &&
  env1.pathEnv.refs.all fun u =>
    env1.pathEnv.refs.all fun v =>
      regexBeq (env1.pathEnv.paths (u, v)) (env2.pathEnv.paths (u, v))

/-- Conservative check: is L(r1) ⊆ L(r2)?
    Checks if r1 is syntactically equal to r2, or appears as an arm of r2's union tree,
    or r1 has an empty language. -/
def regexSubsumedBy [BEq α] : Regex α → Regex α → Bool
  | r1, .union s1 s2 => is_empty r1 || regexBeq r1 (.union s1 s2) ||
      regexSubsumedBy r1 s1 || regexSubsumedBy r1 s2
  | r1, r2 => is_empty r1 || regexBeq r1 r2

/-- Check that envL subsumes env: same siteEnv/varEnv/refs, and every path regex
    in env is subsumed by the corresponding regex in envL.
    Used at jump/branch targets where envL may be a join of multiple predecessors. -/
def TypeEnv.subsumes_bool (envL env : TypeEnv) : Bool :=
  lookup_equiv_bool env.siteEnv envL.siteEnv &&
  lookup_equiv_bool env.varEnv envL.varEnv &&
  env.pathEnv.refs == envL.pathEnv.refs &&
  env.pathEnv.refs.all fun u =>
    env.pathEnv.refs.all fun v =>
      regexSubsumedBy (env.pathEnv.paths (u, v)) (envL.pathEnv.paths (u, v))

/-- Boolean check for all_fresh_sites -/
def all_fresh_sites_bool (env: TypeEnv) (as: List Site) : Bool :=
  as.all (fun a => notIn env.siteEnv a)

/-- Boolean check for types_conform -/
def types_conform_bool (siteEnv : SiteEnv) (sites : List Site) (paramTypes : List ParamType) : Bool :=
  match sites, paramTypes with
  | [], [] => true
  | site :: sites', paramType :: paramTypes' =>
    match AssocMap.lookup siteEnv site with
    | some τ =>
      match paramType, τ with
      | ⟨bt, none⟩, .basic bt' => bt == bt' && types_conform_bool siteEnv sites' paramTypes'
      | ⟨bt, some isRefMut⟩, .ref τ' _ isBor =>
        bt == τ' &&
        (match isRefMut, isBor with
         | true, .siteBorrowMut => true
         | false, .siteBorrowImm => true
         | _, _ => false) &&
        types_conform_bool siteEnv sites' paramTypes'
      | _, _ => false
    | none => false
  | _, _ => false

/-- Boolean check for check_mutable_inputs_isolated.
    For each mutable input, checks that the path regex to every other input
    only matches the empty string (or nothing). -/
def check_mutable_inputs_isolated_bool (env: TypeEnv) (bs: List Site) : Bool :=
  bs.all fun mi_site =>
    match AssocMap.lookup env.siteEnv mi_site with
    | some (.ref _ mi_ref .siteBorrowMut) =>
      bs.all fun other_site =>
        if mi_site != other_site then
          match AssocMap.lookup env.siteEnv other_site with
          | some (.ref _ other_ref _) =>
            only_matches_empty (env.pathEnv.paths (mi_ref, other_ref))
          | _ => true
        else true
    | _ => true

/-- Boolean check for check_mutable_inputs_have_outbound.
    For each mutable input, checks that at least one distinct target ref
    has a non-empty path from the mutable input's ref. -/
def check_mutable_inputs_have_outbound_bool (env: TypeEnv) (bs: List Site) : Bool :=
  bs.all fun mi_site =>
    match AssocMap.lookup env.siteEnv mi_site with
    | some (.ref _ mi_ref .siteBorrowMut) =>
      env.pathEnv.refs.any fun target =>
        mi_ref != target && has_nonempty_match (env.pathEnv.paths (mi_ref, target))
    | _ => true

/-- Boolean check for no_locals_borrowed -/
def no_locals_borrowed_bool (env: TypeEnv) : Bool :=
  env.varEnv.entries.all fun (x, _) => not_borrowed_bool x env

/-- Boolean check for check_outbound.
    Simplifies regexes (computing stored Brzozowski derivatives) before checking,
    so that derivative-wrapped regexes are correctly recognized as ε/empty. -/
def check_outbound_bool (penv: PathEnv) (s: Aref) : Bool :=
  penv.refs.all fun s' =>
    only_matches_empty (simplify (penv.paths (s, s')))

/-- Check field names and sites are both distinct -/
def check_fields_distinct (fields : List (Field × Site)) : Bool :=
  let sites := fields.map Prod.snd
  let fnames := fields.map Prod.fst
  sites.length == sites.eraseDups.length &&
  fnames.length == fnames.eraseDups.length

/-- Check unpack field freshness -/
def check_unpack_fields_fresh (siteEnv : SiteEnv) (fields : List (Field × Site)) : Bool :=
  fields.all fun (_, a) => notIn siteEnv a

/-- Check unpack fields exist in fentries -/
def check_unpack_fields_exist (fields : List (Field × Site)) (fentries : AssocMap Field BasicMoveType) : Bool :=
  fields.all fun (f, _) =>
    match lookup fentries f with
    | some _ => true
    | none => false

/-- Algorithmic type checking for statements.
    Returns the output TypeEnv if type checking succeeds, None otherwise. -/
def check_stmt (lenv : LabelEnv) (env : TypeEnv) (s : Stmt) (retType : MoveType) : Option TypeEnv :=
  match s with
  | .skip => some env

  | .jump L =>
    match lookup lenv L with
    | some envL => if TypeEnv.subsumes_bool envL env then some env else none
    | none => none

  | .branch a L1 L2 =>
    match lookup env.siteEnv a with
    | some (.basic .tbool) =>
      match lookup lenv L1, lookup lenv L2 with
      | some envL1, some envL2 =>
        let env' := {env with siteEnv := delete env.siteEnv a}
        if TypeEnv.subsumes_bool envL1 env' && TypeEnv.subsumes_bool envL2 env'
        then some env
        else none
      | _, _ => none
    | _ => none

  | .ret as =>
    if as.all (fun a => lookup env.siteEnv a == some retType) &&
       no_locals_borrowed_bool env
    then some env
    else none

  | .abort a =>
    match lookup env.siteEnv a with
    | some _ => some env
    | none => none

  | .letBind a e cont =>
    match e with
    | .usage (.move x) =>
      match lookup env.varEnv x with
      | some (.validVar, τ, ms) =>
        if not_borrowed_bool x env && notIn env.siteEnv a then
          let env' := {env with varEnv := update env.varEnv x (.invalidVar, τ, ms)
                                siteEnv := insert env.siteEnv a τ}
          check_stmt lenv env' cont retType
        else none
      | _ => none

    | .usage (.copy x) =>
      match lookup env.varEnv x with
      | some (.validVar, .basic bt, _) =>
        if notIn env.siteEnv a then
          let env' := {env with siteEnv := insert env.siteEnv a (.basic bt)}
          check_stmt lenv env' cont retType
        else none
      | some (.validVar, .ref τ s isBor, _) =>
        if notIn env.siteEnv a then
          let t := nextFreshRef env.pathEnv
          let env' := {env with siteEnv := insert env.siteEnv a (.ref τ t isBor)
                                pathEnv := update_with_epsilon s t env.pathEnv}
          check_stmt lenv env' cont retType
        else none
      | _ => none

    | .usage (.borrowImm x) =>
      match lookup env.varEnv x with
      | some (.validVar, .basic τ, _) =>
        -- Check site fresh; use nextFreshRef to ensure ref is fresh
        if notIn env.siteEnv a then
          let r := nextFreshRef env.pathEnv
          let env' := {env with siteEnv := insert env.siteEnv a (.ref τ r .siteBorrowImm)
                                pathEnv := update_with_epsilon r r env.pathEnv |>
                                           update_with_extension r .root [.root_to_var x]}
          check_stmt lenv env' cont retType
        else none
      | _ => none

    | .usage (.borrowMut x) =>
      match lookup env.varEnv x with
      | some (.validVar, .basic τ, ms) =>
        -- Check mutable and site fresh; use nextFreshRef to ensure ref is fresh
        if ms == .mutable && notIn env.siteEnv a then
          let r := nextFreshRef env.pathEnv
          let env' := {env with siteEnv := insert env.siteEnv a (.ref τ r .siteBorrowMut)
                                pathEnv := update_with_epsilon r r env.pathEnv |>
                                           update_with_extension r .root [.root_to_var x]}
          check_stmt lenv env' cont retType
        else none
      | _ => none

    | .intLit _ =>
      if notIn env.siteEnv a then
        let env' := {env with siteEnv := insert env.siteEnv a (.basic .u64)}
        check_stmt lenv env' cont retType
      else none

    | .borrowField src bt f =>
      match lookup env.siteEnv src with
      | some (.ref bt' s isBor) =>
        if BasicMoveType.beq bt bt' then
          match bt with
          | .trecord fentries =>
            match lookup fentries f with
            | some btf =>
              if notIn env.siteEnv a then
                let rf := nextFreshRef env.pathEnv
                let env' := {env with siteEnv := insert (delete env.siteEnv src) a (.ref btf rf isBor)
                                      pathEnv := update_with_extension rf s [.field f] env.pathEnv}
                check_stmt lenv env' cont retType
              else none
            | none => none
          | _ => none
        else none
      | _ => none

    | .borrowMutField src bt f =>
      match lookup env.siteEnv src with
      | some (.ref bt' s .siteBorrowMut) =>
        if BasicMoveType.beq bt bt' then
          match bt with
          | .trecord fentries =>
            match lookup fentries f with
            | some btf =>
              if notIn env.siteEnv a then
                let rf := nextFreshRef env.pathEnv
                let env' := {env with siteEnv := insert (delete env.siteEnv src) a (.ref btf rf .siteBorrowMut)
                                      pathEnv := update_with_extension rf s [.field f] env.pathEnv}
                check_stmt lenv env' cont retType
              else none
            | none => none
          | _ => none
        else none
      | _ => none

    | .binop bop src1 src2 =>
      match lookup env.siteEnv src1, lookup env.siteEnv src2 with
      | some (.basic bt1), some (.basic bt2) =>
        match binop_type bop bt1 bt2 with
        | some bt3 =>
          if notIn env.siteEnv a then
            let env' := {env with siteEnv := insert (delete (delete env.siteEnv src1) src2) a (.basic bt3)}
            check_stmt lenv env' cont retType
          else none
        | none => none
      | _, _ => none

    | .readRef src =>
      match lookup env.siteEnv src with
      | some (.ref τ r _) =>
        if notIn env.siteEnv a then
          let env' := {env with siteEnv := insert (delete env.siteEnv src) a (.basic τ)
                                pathEnv := delete_ref_node env.pathEnv r}
          check_stmt lenv env' cont retType
        else none
      | _ => none

    | .freeze src =>
      match lookup env.siteEnv src with
      | some (.ref τ r _) =>
        if notIn env.siteEnv a then
          let r' := nextFreshRef env.pathEnv
          let env' := {env with siteEnv := insert (delete env.siteEnv src) a (.ref τ r' .siteBorrowImm)
                                pathEnv := consume_ref_transfer env.pathEnv r r'}
          check_stmt lenv env' cont retType
        else none
      | _ => none

    | .pack _recName fields =>
      if notIn env.siteEnv a && check_fields_distinct fields then
        let fentries_opt := fields.foldlM (fun acc (f, site) =>
          match lookup env.siteEnv site with
          | some (.basic bt) => some (insert acc f bt)
          | _ => none) AssocMap.empty
        match fentries_opt with
        | some fentries =>
          let env' := {env with siteEnv := insert (deleteAll env.siteEnv (fields.map Prod.snd)) a (.basic (.trecord fentries))}
          check_stmt lenv env' cont retType
        | none => none
      else none

  | .writeRef a b cont =>
    match lookup env.siteEnv a, lookup env.siteEnv b with
    | some (.ref τ r .siteBorrowMut), some (.basic τ') =>
      if τ == τ' && check_outbound_bool env.pathEnv r then
        let env' := {env with siteEnv := delete (delete env.siteEnv b) a
                              pathEnv := garbage_collect env.pathEnv r}
        check_stmt lenv env' cont retType
      else none
    | _, _ => none

  | .assign x a cont =>
    match lookup env.varEnv x with
    | some (.validVar, .basic τ, ms) =>
      if ms == .mutable then
        let ax : Site := .site (env.siteEnv.entries.length)
        if notIn env.siteEnv ax then
          let r := nextFreshRef env.pathEnv
          let env' := {env with siteEnv := delete (delete (insert env.siteEnv ax (.ref τ r .siteBorrowMut)) a) ax
                                pathEnv := garbage_collect (update_with_extension r .root [.root_to_var x] (update_with_epsilon r r env.pathEnv)) r}
          check_stmt lenv env' cont retType
        else none
      else none
    | some (.invalidVar, τ, .mutable) =>
      match lookup env.siteEnv a with
      | some τ' =>
        if τ == τ' then
          let env' := {env with varEnv := update env.varEnv x (.validVar, τ, .mutable)
                                siteEnv := delete env.siteEnv a}
          check_stmt lenv env' cont retType
        else none
      | none => none
    | _ => none

  | .call as fnName bs cont =>
    if all_fresh_sites_bool env as then
      match lookup env.funEnv fnName with
      | some ⟨params, rets⟩ =>
        if types_conform_bool env.siteEnv bs params &&
           types_conform_bool env.siteEnv as rets &&
           check_mutable_inputs_isolated_bool env bs &&
           check_mutable_inputs_have_outbound_bool env bs then
          let env' := call_connect_inputs_outputs env as bs
          check_stmt lenv env' cont retType
        else none
      | none => none
    else none

  | .release a cont =>
    match lookup env.siteEnv a with
    | some (.ref _ r _) =>
      let env' := {env with siteEnv := delete env.siteEnv a
                            pathEnv := delete_ref_node env.pathEnv r}
      check_stmt lenv env' cont retType
    | _ => none

  | .unpack fields b cont =>
    match lookup env.siteEnv b with
    | some (.basic (.trecord fentries)) =>
      if check_unpack_fields_fresh env.siteEnv fields &&
         check_fields_distinct fields &&
         check_unpack_fields_exist fields fentries then
        let env' := {env with siteEnv := addFieldSites fentries (delete env.siteEnv b) fields}
        check_stmt lenv env' cont retType
      else none
    | _ => none

/-- Check a single block -/
def check_block (lenv : LabelEnv) (block : Block) (expectedEnv : TypeEnv) (retType : MoveType) : Bool :=
  (check_stmt lenv expectedEnv block.body retType).isSome

/-- Algorithmic type checking for functions. Returns true if the function type checks. -/
def check_fun (f : FunDef) (lenv : LabelEnv) : Bool :=
  let initVarEnv := init_fun_varEnv f
  let initEnv : TypeEnv := {
    varEnv := initVarEnv,
    siteEnv := AssocMap.empty,
    pathEnv := PathEnv.init,
    funEnv := AssocMap.empty
  }
  match f.blocks with
  | [] => false
  | entry :: _ =>
    match lookup lenv entry.label with
    | some entryEnv =>
      TypeEnv.equiv_bool entryEnv initEnv &&
      f.blocks.all fun block =>
        match lookup lenv block.label with
        | some blockEnv => check_block lenv block blockEnv f.returnType
        | none => false
    | none => false

end LeanMove.Checker
