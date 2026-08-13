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
import LeanMove.Typing.TypeChecking

/-!
# Algorithmic Type Checking for MoveLight

This file contains the algorithmic (executable) type checker that mirrors
the relational specification in `TypeChecking.lean`.

## Contents
- `check_stmt` - Algorithmic statement type checking, returns `Option TypeEnv`
- `check_fun` - Algorithmic function type checking, returns `Bool`
-/

namespace LeanMove.Typing

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

/-- Boolean check for VarEntry compatibility: same IsValid/Mut, compatible MoveType. -/
def varentry_compatible_bool : (IsValid × MoveType × Mut) → (IsValid × MoveType × Mut) → Bool
  | (v1, t1, m1), (v2, t2, m2) => v1 == v2 && MoveType.compatible_bool t1 t2 && m1 == m2

/-- Check compatibility of two optional VarEnv entries. -/
def varenv_entry_compatible_opt : Option (IsValid × MoveType × Mut) → Option (IsValid × MoveType × Mut) → Bool
  | some e1, some e2 => varentry_compatible_bool e1 e2
  | none, none => true
  | _, _ => false

/-- Boolean check for VarEnvLookupCompatible. -/
def varenv_lookup_compatible_bool (m1 m2 : VarEnv) : Bool :=
  m1.entries.all (fun p => varenv_entry_compatible_opt (lookup m1 p.1) (lookup m2 p.1)) &&
  m2.entries.all (fun p => varenv_entry_compatible_opt (lookup m1 p.1) (lookup m2 p.1))

/-- Boolean check for TypeEnv.equiv -/
def TypeEnv.equiv_bool (env1 env2 : TypeEnv) : Bool :=
  lookup_equiv_bool env1.siteEnv env2.siteEnv &&
  varenv_lookup_compatible_bool env1.varEnv env2.varEnv &&
  env1.pathEnv.refs == env2.pathEnv.refs &&
  (env1.pathEnv.refs.all fun u =>
    env1.pathEnv.refs.all fun v =>
      regexBeq (env1.pathEnv.paths (u, v)) (env2.pathEnv.paths (u, v))) &&
  lookup_equiv_bool env1.enumEnv env2.enumEnv

/- ---------------------------------------------------- -/
/-       Refid Substitution (algorithmic)               -/
/- ---------------------------------------------------- -/

/-- Apply a list-based substitution to an Aref.
    Looks up r in the substitution; returns r unchanged if not found. -/
def applySubstArefList (σ : List (Aref × Aref)) (r : Aref) : Aref :=
  match σ.lookup r with
  | some r' => r'
  | none => r

/-- Apply a list-based substitution to a MoveType. -/
def applySubstMoveTypeList (σ : List (Aref × Aref)) : MoveType → MoveType
  | .basic bt => .basic bt
  | .ref bt r bk => .ref bt (applySubstArefList σ r) bk

/-- Apply a list-based substitution to a VarEnv. -/
def applySubstVarEnvList (σ : List (Aref × Aref)) (ve : VarEnv) : VarEnv :=
  ⟨ve.entries.map fun (x, (isv, τ, ms)) => (x, (isv, applySubstMoveTypeList σ τ, ms))⟩

/-- Compute a refid substitution by comparing VALID ref-typed entries in two VarEnvs.
    Maps envL's .refid placeholders → env's actual arefs (which may be .paramRef or .refid).
    Only valid entries participate: invalid entries use MoveType.compatible separately.
    Returns none if conflicting or non-injective. -/
def computeRefSubst (ve_target ve_source : VarEnv) : Option (List (Aref × Aref)) :=
  let refPairs := ve_target.entries.filterMap fun (x, (isv, τ_target, _)) =>
    match isv, τ_target with
    | .validVar, .ref _ (.refid n1) _ =>
      match lookup ve_source x with
      | some (.validVar, .ref _ r2 _, _) =>
        if (.refid n1 : Aref) == r2 then none  -- identity, no remapping needed
        else some (.refid n1, r2)
      | _ => none  -- mismatch caught by varenv_subst_equiv_bool
    | _, _ => none
  -- Build substitution, checking consistency and injectivity
  refPairs.foldl (fun acc pair =>
    match acc with
    | none => none
    | some pairs =>
      let (r1, r2) := pair
      match pairs.lookup r1 with
      | some r2' => if r2 == r2' then some pairs else none  -- consistency
      | none =>
        -- injectivity: r2 must not already be a target
        if pairs.any (fun (_, t) => t == r2) then none
        else some (pair :: pairs)
  ) (some [])

/-- Boolean base type compatibility: checks base type and borrow kind, ignoring Aref. -/
def MoveType.base_compatible_bool : MoveType → MoveType → Bool
  | .basic bt1, .basic bt2 => bt1.beq bt2
  | .ref bt1 _ bk1, .ref bt2 _ bk2 => bt1.beq bt2 && bk1 == bk2
  | _, _ => false

/-- Boolean check for VarEnvSubstEquiv: for valid entries, exact match after σ;
    for invalid entries, base type compatibility (arefs ignored). -/
def varenv_subst_equiv_bool (σ : List (Aref × Aref)) (ve1 ve2 : VarEnv) : Bool :=
  ve1.entries.all (fun (x, (isv1, τ1, ms1)) =>
    match lookup ve2 x with
    | some (isv2, τ2, ms2) =>
      ms1 == ms2 &&
      match isv1, isv2 with
      | .validVar, .validVar => applySubstMoveTypeList σ τ1 == τ2
      | .invalidVar, .invalidVar => MoveType.base_compatible_bool τ1 τ2
      | .invalidVar, .validVar =>
        match τ1, τ2 with
        | .basic bt1, .basic bt2 => bt1.beq bt2
        | _, _ => false
      | .validVar, .invalidVar => false
    | none => false) &&
  ve2.entries.all (fun (x, _) => (lookup ve1 x).isSome)

/-- Boolean check for SiteEnvSubstEquiv: site types match after σ-renaming -/
def siteenv_subst_equiv_bool (σ : List (Aref × Aref)) (se1 se2 : SiteEnv) : Bool :=
  se1.entries.all (fun (k, τ1) =>
    match lookup se2 k with
    | some τ2 => applySubstMoveTypeList σ τ1 == τ2
    | none => false) &&
  se2.entries.all (fun (k, _) => (lookup se1 k).isSome)

/-- EnvL refids that are not yet mapped by σ (not keys in σ).
    Non-refid arefs (.root, .paramRef) are always identity-mapped, never unmapped. -/
private def unmappedRefs (σ : List (Aref × Aref))
    (refsL : List Aref) : List Aref :=
  refsL.filter fun r => match r with
    | .refid _ => !(σ.any (fun (k, _) => k == r))
    | _ => false

/-- Env refs not claimed by σ targets or identity-mapped non-refid arefs. -/
private def unmatchedRefs (σ : List (Aref × Aref))
    (refsL refsE : List Aref) : List Aref :=
  let σ_targets := σ.map (·.2)
  -- Non-refid arefs in envL are identity-mapped
  let nonRefidL := refsL.filter fun r => match r with
    | .refid _ => false
    | _ => true
  refsE.filter fun r =>
    !(σ_targets.contains r) && !(nonRefidL.contains r)

/-- Backtracking search: pair unmapped envL refs with unmatched env refs,
    validated by path subsumption. Structurally recursive on `unmapped`.
    Only pairs .refid keys with non-root values (well-formedness invariant).
    Returns the extended σ if a valid pairing exists, none otherwise. -/
def findRefExtension (σ : List (Aref × Aref))
    (unmapped : List Aref) (unmatched : List Aref)
    (refsL : List Aref) (envL env : TypeEnv)
    : Option (List (Aref × Aref)) :=
  match unmapped with
  | [] =>
    -- All paired: validate full path subsumption
    if unmatched.isEmpty &&
       refsL.all (fun u => refsL.all (fun v =>
         regexSubsumedBy
           (env.pathEnv.paths (applySubstArefList σ u, applySubstArefList σ v))
           (envL.pathEnv.paths (u, v))))
    then some σ
    else none
  | u :: us =>
    -- Only extend with .refid keys (non-refid arefs should be identity-mapped)
    match u with
    | .refid _ =>
      -- Try pairing u with each candidate in unmatched
      unmatched.findSome? fun u' =>
        -- Skip .root as target value
        match u' with
        | .root => none
        | _ =>
          let σ' := (u, u') :: σ
          -- Check injectivity: u' not already a target
          if σ.any (fun (_, t) => t == u') then none
          else findRefExtension σ' us (unmatched.erase u') refsL envL env
    | _ => none  -- non-refid unmapped ref: ill-formed input

/-- Extend σ by finding a valid order-independent pairing for unmapped pathEnv refs.
    Returns the extended σ, or the original σ if no extension needed. -/
def extendRefSubst (σ : List (Aref × Aref))
    (refsL refsE : List Aref) (envL env : TypeEnv)
    : Option (List (Aref × Aref)) :=
  let um := unmappedRefs σ refsL
  let un := unmatchedRefs σ refsL refsE
  if um.length != un.length then none
  else if um.isEmpty then some σ
  else findRefExtension σ um un refsL envL env

/-- Check that envL subsumes env with refid unification.
    Computes σ mapping envL's .refid placeholders to env's actual arefs, then
    extends σ by order-independent matching of unmapped pathEnv refs, and checks:
    1. SiteEnvs match after σ
    2. VarEnvs match after σ (exact for valid, compatible for invalid)
    3. PathEnv refs match after σ
    4. env's paths are subsumed by envL's paths (env ⊆ envL, after σ renaming) -/
def TypeEnv.subsumes_bool (envL env : TypeEnv) : Bool :=
  match computeRefSubst envL.varEnv env.varEnv with
  | none => false
  | some σ_var =>
    match extendRefSubst σ_var envL.pathEnv.refs env.pathEnv.refs envL env with
    | none => false
    | some σ =>
      siteenv_subst_equiv_bool σ envL.siteEnv env.siteEnv &&
      varenv_subst_equiv_bool σ envL.varEnv env.varEnv &&
      -- Check that mapped refs are a permutation of env's refs
      -- (both nodup + same length + containment → Perm)
      (let mapped := envL.pathEnv.refs.map (applySubstArefList σ)
       mapped.length == env.pathEnv.refs.length &&
       mapped.eraseDups.length == mapped.length &&
       mapped.all (fun r => env.pathEnv.refs.contains r)) &&
      -- Check that env's refs have no duplicates (implies σ is injective on envL's refs)
      (env.pathEnv.refs.eraseDups.length == env.pathEnv.refs.length) &&
      (envL.pathEnv.refs.all fun u =>
        envL.pathEnv.refs.all fun v =>
          regexSubsumedBy (env.pathEnv.paths (applySubstArefList σ u, applySubstArefList σ v))
            (envL.pathEnv.paths (u, v))) &&
      lookup_equiv_bool envL.enumEnv env.enumEnv

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

/-- Count the number of reference-typed returns in a list of ParamTypes. -/
def countRefReturns (rets : List ParamType) : Nat :=
  rets.foldl (fun acc pt => match pt.isRefMut with | some _ => acc + 1 | none => acc) 0

/-- Generate a list of fresh refs for reference-typed outputs.
    Allocates sequential refids starting from nextFreshRefInEnv. -/
def generateFreshRefs (env : TypeEnv) (rets : List ParamType) : List Aref :=
  let start := getRefId (nextFreshRefInEnv env)
  let n := countRefReturns rets
  (List.range n).map fun i => .refid (start + i)

/-- Boolean check for all_refs_fresh_in_env. -/
def all_refs_fresh_in_env_bool (env : TypeEnv) (refs : List Aref) : Bool :=
  refs.all (fun r => freshRefInEnvBool r env)

/-- Boolean check: no returned ref borrows a local variable.
    For each ref-typed returned site with aref r, G(root, r) must match nothing. -/
def ret_refs_not_from_locals_bool (env : TypeEnv) (as : List Site) : Bool :=
  as.all fun a =>
    match lookup env.siteEnv a with
    | some (.ref _ r _) => is_empty (simplify (env.pathEnv.paths (.root, r)))
    | _ => true

/-- Boolean check: mutable returned refs have only trivial outbound paths to non-returned live ref sites.
    For each mut ref returned site with aref r, checks all non-returned ref-typed sites b in siteEnv:
    G(r, r') must match only [] where r' is the aref of site b. -/
def ret_mutable_writable_bool (env : TypeEnv) (as : List Site) : Bool :=
  as.all fun a =>
    match lookup env.siteEnv a with
    | some (.ref _ r .siteBorrowMut) =>
      env.siteEnv.entries.all fun (b, ty) =>
        if b ∈ as then true  -- skip returned sites
        else match ty with
        | .ref _ r' _ => only_matches_empty (simplify (env.pathEnv.paths (r, r')))
        | _ => true
    | _ => true

/-- Boolean check: no other returned ref reaches a mutable return.
    For each mutable return r₁ and each other return r₂, G(r₂, r₁) must match nothing. -/
def ret_mutable_no_aliases_bool (env : TypeEnv) (as : List Site) : Bool :=
  as.all fun a₁ =>
    match lookup env.siteEnv a₁ with
    | some (.ref _ r₁ .siteBorrowMut) =>
      as.all fun a₂ =>
        if a₁ != a₂ then
          match lookup env.siteEnv a₂ with
          | some (.ref _ r₂ _) => is_empty (simplify (env.pathEnv.paths (r₂, r₁)))
          | _ => true
        else true
    | _ => true

/-- Algorithmic type checking for statements.
    Returns the output TypeEnv if type checking succeeds, None otherwise. -/
def check_stmt (lenv : LabelEnv) (env : TypeEnv) (s : Stmt) (retTypes : List ParamType) : Option TypeEnv :=
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
    if types_conform_bool env.siteEnv as retTypes &&
       ret_refs_not_from_locals_bool env as &&
       ret_mutable_writable_bool env as &&
       ret_mutable_no_aliases_bool env as
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
          check_stmt lenv env' cont retTypes
        else none
      | _ => none

    | .usage (.copy x) =>
      match lookup env.varEnv x with
      | some (.validVar, .basic bt, _) =>
        if notIn env.siteEnv a then
          let env' := {env with siteEnv := insert env.siteEnv a (.basic bt)}
          check_stmt lenv env' cont retTypes
        else none
      | some (.validVar, .ref τ s isBor, _) =>
        if notIn env.siteEnv a then
          let t := nextFreshRefInEnv env
          let env' := {env with siteEnv := insert env.siteEnv a (.ref τ t isBor)
                                pathEnv := update_with_epsilon t s env.pathEnv}
          check_stmt lenv env' cont retTypes
        else none
      | _ => none

    | .usage (.borrowImm x) =>
      match lookup env.varEnv x with
      | some (.validVar, .basic τ, _) =>
        -- Check site fresh; use nextFreshRefInEnv to ensure ref is fresh
        if notIn env.siteEnv a then
          let r := nextFreshRefInEnv env
          let env' := {env with siteEnv := insert env.siteEnv a (.ref τ r .siteBorrowImm)
                                pathEnv := update_with_epsilon r r env.pathEnv |>
                                           update_with_extension r .root [.root_to_var x]}
          check_stmt lenv env' cont retTypes
        else none
      | _ => none

    | .usage (.borrowMut x) =>
      match lookup env.varEnv x with
      | some (.validVar, .basic τ, ms) =>
        -- Check mutable and site fresh; use nextFreshRefInEnv to ensure ref is fresh
        if ms == .mutable && notIn env.siteEnv a then
          let r := nextFreshRefInEnv env
          let env' := {env with siteEnv := insert env.siteEnv a (.ref τ r .siteBorrowMut)
                                pathEnv := update_with_epsilon r r env.pathEnv |>
                                           update_with_extension r .root [.root_to_var x]}
          check_stmt lenv env' cont retTypes
        else none
      | _ => none

    | .intLit _ w =>
      if notIn env.siteEnv a then
        let env' := {env with siteEnv := insert env.siteEnv a (.basic (.int w))}
        check_stmt lenv env' cont retTypes
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
                let rf := nextFreshRefInEnv env
                let env' := {env with siteEnv := insert (delete env.siteEnv src) a (.ref btf rf isBor)
                                      pathEnv := update_with_extension rf s [.field f] env.pathEnv}
                check_stmt lenv env' cont retTypes
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
                let rf := nextFreshRefInEnv env
                let env' := {env with siteEnv := insert (delete env.siteEnv src) a (.ref btf rf .siteBorrowMut)
                                      pathEnv := update_with_extension rf s [.field f] env.pathEnv}
                check_stmt lenv env' cont retTypes
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
            check_stmt lenv env' cont retTypes
          else none
        | none => none
      | _, _ => none

    | .unop uop src =>
      match lookup env.siteEnv src with
      | some (.basic bt1) =>
        match unop_type uop bt1 with
        | some bt2 =>
          if notIn env.siteEnv a then
            let env' := {env with siteEnv := insert (delete env.siteEnv src) a (.basic bt2)}
            check_stmt lenv env' cont retTypes
          else none
        | none => none
      | _ => none

    | .readRef src =>
      match lookup env.siteEnv src with
      | some (.ref τ r _) =>
        if notIn env.siteEnv a then
          let env' := {env with siteEnv := insert (delete env.siteEnv src) a (.basic τ)
                                pathEnv := delete_ref_node env.pathEnv r}
          check_stmt lenv env' cont retTypes
        else none
      | _ => none

    | .freeze src =>
      match lookup env.siteEnv src with
      | some (.ref τ r _) =>
        if notIn env.siteEnv a then
          let r' := nextFreshRefInEnv env
          let env' := {env with siteEnv := insert (delete env.siteEnv src) a (.ref τ r' .siteBorrowImm)
                                pathEnv := consume_ref_transfer env.pathEnv r r'}
          check_stmt lenv env' cont retTypes
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
          check_stmt lenv env' cont retTypes
        | none => none
      else none

    | .packVariant enumName variantName fields =>
      if notIn env.siteEnv a && check_fields_distinct fields then
        -- Collect field types and verify they match the variant's field entries
        let fentries_opt := fields.foldlM (fun acc (f, site) =>
          match lookup env.siteEnv site with
          | some (.basic bt) => some (insert acc f bt)
          | _ => none) AssocMap.empty
        match fentries_opt with
        | some fentries =>
          -- Verify the variant exists in the enum environment and field types match
          match lookup env.enumEnv enumName with
          | some enumDef =>
            match lookup enumDef.variants variantName with
            | some variantDef =>
              if fentries == variantDef.fields then
                let env' := {env with siteEnv := insert (deleteAll env.siteEnv (fields.map Prod.snd)) a
                                                        (.basic (.tenum enumName))}
                check_stmt lenv env' cont retTypes
              else none
            | none => none
          | none => none
        | none => none
      else none

    | .vecPack T elems =>
      if notIn env.siteEnv a &&
         elems.eraseDups.length == elems.length &&
         elems.all (fun s => match lookup env.siteEnv s with
           | some (.basic T') => T.beq T'
           | _ => false) then
        let env' := {env with siteEnv := insert (deleteAll env.siteEnv elems) a (.basic (.tvec T))}
        check_stmt lenv env' cont retTypes
      else none

    | .vecLen src =>
      match lookup env.siteEnv src with
      | some (.ref (.tvec _) r _) =>
        if notIn env.siteEnv a then
          let env' := {env with siteEnv := insert (delete env.siteEnv src) a (.basic .u64)
                                pathEnv := delete_ref_node env.pathEnv r}
          check_stmt lenv env' cont retTypes
        else none
      | _ => none

    | .vecImmBorrow src idx =>
      match lookup env.siteEnv src, lookup env.siteEnv idx with
      | some (.ref (.tvec T) s .siteBorrowImm), some (.basic .u64) =>
        if notIn env.siteEnv a then
          let rf := nextFreshRefInEnv env
          let env' := {env with siteEnv := insert (delete (delete env.siteEnv src) idx) a (.ref T rf .siteBorrowImm)
                                pathEnv := update_with_extension rf s [.vecElem] env.pathEnv}
          check_stmt lenv env' cont retTypes
        else none
      | some (.ref (.tvec T) s .siteBorrowMut), some (.basic .u64) =>
        if notIn env.siteEnv a && check_outbound_bool env.pathEnv s then
          let rf := nextFreshRefInEnv env
          let env' := {env with siteEnv := insert (delete (delete env.siteEnv src) idx) a (.ref T rf .siteBorrowImm)
                                pathEnv := update_with_extension rf s [.vecElem] env.pathEnv}
          check_stmt lenv env' cont retTypes
        else none
      | _, _ => none

    | .vecMutBorrow src idx =>
      match lookup env.siteEnv src, lookup env.siteEnv idx with
      | some (.ref (.tvec T) s .siteBorrowMut), some (.basic .u64) =>
        if notIn env.siteEnv a && check_outbound_bool env.pathEnv s then
          let rf := nextFreshRefInEnv env
          let env' := {env with siteEnv := insert (delete (delete env.siteEnv src) idx) a (.ref T rf .siteBorrowMut)
                                pathEnv := update_with_extension rf s [.vecElem] env.pathEnv}
          check_stmt lenv env' cont retTypes
        else none
      | _, _ => none

    | .vecPopBack src =>
      match lookup env.siteEnv src with
      | some (.ref (.tvec T) r .siteBorrowMut) =>
        if notIn env.siteEnv a && check_outbound_bool env.pathEnv r then
          let env' := {env with siteEnv := insert (delete env.siteEnv src) a (.basic T)
                                pathEnv := garbage_collect env.pathEnv r}
          check_stmt lenv env' cont retTypes
        else none
      | _ => none

  | .writeRef a b cont =>
    match lookup env.siteEnv a, lookup env.siteEnv b with
    | some (.ref τ r .siteBorrowMut), some (.basic τ') =>
      if τ == τ' && check_outbound_bool env.pathEnv r then
        let env' := {env with siteEnv := delete (delete env.siteEnv b) a
                              pathEnv := garbage_collect env.pathEnv r}
        check_stmt lenv env' cont retTypes
      else none
    | _, _ => none

  | .assign x a cont =>
    match lookup env.varEnv x with
    | some (.validVar, .basic τ, ms) =>
      if ms == .mutable then
        match lookup env.siteEnv a with
        | some (.basic τ') =>
          if τ == τ' then
            let ax : Site := .site (env.siteEnv.entries.length)
            if notIn env.siteEnv ax then
              let r := nextFreshRefInEnv env
              let env' := {env with siteEnv := delete (delete (insert env.siteEnv ax (.ref τ r .siteBorrowMut)) a) ax
                                    pathEnv := garbage_collect (update_with_extension r .root [.root_to_var x] (update_with_epsilon r r env.pathEnv)) r}
              check_stmt lenv env' cont retTypes
            else none
          else none
        | _ => none
      else none
    | some (.validVar, .ref _τ_old r_old _bk_old, ms) =>
      if ms == .mutable then
        match lookup env.siteEnv a with
        | some τ' =>
          let env' := {env with varEnv := update env.varEnv x (.validVar, τ', ms)
                                siteEnv := delete env.siteEnv a
                                pathEnv := delete_ref_node env.pathEnv r_old}
          check_stmt lenv env' cont retTypes
        | none => none
      else none
    | some (.invalidVar, τ, .mutable) =>
      match lookup env.siteEnv a with
      | some τ' =>
        if MoveType.compatible_bool τ τ' then
          let env' := {env with varEnv := update env.varEnv x (.validVar, τ', .mutable)
                                siteEnv := delete env.siteEnv a}
          check_stmt lenv env' cont retTypes
        else none
      | none => none
    | _ => none

  | .call as fnName bs cont =>
    if all_fresh_sites_bool env as && as.eraseDups.length == as.length then
      match lookup env.funEnv fnName with
      | some ⟨params, rets⟩ =>
        if types_conform_bool env.siteEnv bs params &&
           check_mutable_inputs_isolated_bool env bs then
          let outRefs := generateFreshRefs env rets
          match populate_call_outputs env as rets outRefs with
          | some env' =>
            let env'' := call_connect_inputs_outputs env' as bs
            let env''' := {env'' with siteEnv := AssocMap.deleteAll env''.siteEnv bs}
            check_stmt lenv env''' cont retTypes
          | none => none
        else none
      | none => none
    else none

  | .release a cont =>
    match lookup env.siteEnv a with
    | some (.ref _ r _) =>
      let env' := {env with siteEnv := delete env.siteEnv a
                            pathEnv := delete_ref_node env.pathEnv r}
      check_stmt lenv env' cont retTypes
    | some (.basic _) =>
      let env' := {env with siteEnv := delete env.siteEnv a}
      check_stmt lenv env' cont retTypes
    | _ => none

  | .unpack fields b cont =>
    match lookup env.siteEnv b with
    | some (.basic (.trecord fentries)) =>
      if check_unpack_fields_fresh env.siteEnv fields &&
         check_fields_distinct fields &&
         check_unpack_fields_exist fields fentries then
        let env' := {env with siteEnv := addFieldSites fentries (delete env.siteEnv b) fields}
        check_stmt lenv env' cont retTypes
      else none
    | _ => none

  | .vecUnpack T results src cont =>
    match lookup env.siteEnv src with
    | some (.basic (.tvec T')) =>
      if T.beq T' &&
         results.eraseDups.length == results.length &&
         results.all (fun s => notIn env.siteEnv s) then
        let env' := {env with siteEnv := addVecSites T (delete env.siteEnv src) results}
        check_stmt lenv env' cont retTypes
      else none
    | _ => none

  | .vecPushBack refSite val cont =>
    match lookup env.siteEnv refSite, lookup env.siteEnv val with
    | some (.ref (.tvec T) r .siteBorrowMut), some (.basic T') =>
      if T.beq T' && check_outbound_bool env.pathEnv r then
        let env' := {env with siteEnv := delete (delete env.siteEnv val) refSite
                              pathEnv := garbage_collect env.pathEnv r}
        check_stmt lenv env' cont retTypes
      else none
    | _, _ => none

  | .vecSwap refSite idx1 idx2 cont =>
    match lookup env.siteEnv refSite, lookup env.siteEnv idx1, lookup env.siteEnv idx2 with
    | some (.ref (.tvec _) r .siteBorrowMut), some (.basic .u64), some (.basic .u64) =>
      if check_outbound_bool env.pathEnv r then
        let env' := {env with siteEnv := delete (delete (delete env.siteEnv idx2) idx1) refSite
                              pathEnv := garbage_collect env.pathEnv r}
        check_stmt lenv env' cont retTypes
      else none
    | _, _, _ => none

  -- Enum: variant unpack (owned or ref)
  | .unpackVariant variantName fields b cont =>
    match lookup env.siteEnv b with
    -- Owned unpack: source has basic enum type
    | some (.basic (.tenum ename)) =>
      match lookup env.enumEnv ename with
      | some enumDef =>
        match lookup enumDef.variants variantName with
        | some variantDef =>
          let fentries := variantDef.fields
          if check_unpack_fields_fresh env.siteEnv fields &&
             check_fields_distinct fields &&
             check_unpack_fields_exist fields fentries then
            let env' := {env with siteEnv := addFieldSites fentries (delete env.siteEnv b) fields}
            check_stmt lenv env' cont retTypes
          else none
        | none => none
      | none => none
    -- Ref unpack: source has ref to enum type (creates borrows for each field)
    | some (.ref (.tenum ename) r bk) =>
      match lookup env.enumEnv ename with
      | some enumDef =>
        match lookup enumDef.variants variantName with
        | some variantDef =>
          let fentries := variantDef.fields
          if check_unpack_fields_fresh env.siteEnv fields &&
             check_fields_distinct fields &&
             check_unpack_fields_exist fields fentries then
            -- For each field, allocate a fresh ref and create a borrow
            let envInit := {env with siteEnv := delete env.siteEnv b}
            match fields.foldlM (fun env' (f, site) =>
              match lookup fentries f with
              | some bt =>
                if notIn env'.siteEnv site then
                  let rf := nextFreshRefInEnv env'
                  some {env' with
                    siteEnv := insert env'.siteEnv site (.ref bt rf bk)
                    pathEnv := update_with_extension rf r [.field (MoveLight.qualifyField variantName f)] env'.pathEnv}
                else none
              | none => none
            ) envInit with
            | some env' => check_stmt lenv env' cont retTypes
            | none => none
          else none
        | none => none
      | none => none
    | _ => none

  -- Enum: variant switch (terminal)
  | .variantSwitch src cases =>
    match lookup env.siteEnv src with
    | some (.ref (.tenum ename) r _bk) =>
      match lookup env.enumEnv ename with
      | some enumDef =>
        -- Check coverage (every variant has a matching case) AND each case label is valid
        if enumDef.variants.entries.all (fun (vname, _) =>
             cases.any (fun (vname', _) => vname == vname')) &&
         cases.all (fun (_, label) =>
           match lookup lenv label with
           | some envL => TypeEnv.subsumes_bool envL
               {env with siteEnv := delete env.siteEnv src
                         pathEnv := delete_ref_node env.pathEnv r}
           | none => false) then some env
        else none
      | none => none
    | _ => none

/-- Check a single block -/
def check_block (lenv : LabelEnv) (block : Block) (expectedEnv : TypeEnv) (retTypes : List ParamType) : Bool :=
  (check_stmt lenv expectedEnv block.body retTypes).isSome

/-- Algorithmic type checking for functions. Returns true if the function type checks. -/
def check_fun (f : FunDef) (lenv : LabelEnv) (enumEnv : EnumEnv) : Bool :=
  let initVarEnv := init_fun_varEnv f
  let initEnv : TypeEnv := {
    varEnv := initVarEnv,
    siteEnv := AssocMap.empty,
    pathEnv := init_fun_pathEnv f,
    funEnv := AssocMap.empty,
    enumEnv := enumEnv
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

end LeanMove.Typing
