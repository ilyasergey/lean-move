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

import LeanMove.Typing.Algorithmic.AlgorithmicTypingSoundness

/-!
# Decidable TypeEnv Well-Formedness

This file provides a decidable (boolean) well-formedness check for type
environments. The key insight: `PathEnv.paths` is a function, so
`PathEnv.WellFormed` cannot be checked algorithmically. We introduce
`PathEnvDec` where paths are stored as an `AssocMap`, with boolean WF checks and
soundness proofs.

## Main Definitions

- `PathEnvDec` — path environment with `AssocMap`-based paths
- `TypeEnvDec` — type environment using `PathEnvDec`
- `LabelEnvDec` — label environment mapping labels to `TypeEnvDec`
- `check_fun_dec` — wrapper that checks WF, converts, and calls `check_fun`

## Main Results

- `check_fun_dec_sound` — if `check_fun_dec` returns true, the relational
  judgment holds
-/

namespace LeanMove.Typing

open Lang
open Lang.MoveLight
open AssocMap
open Regex

/- ---------------------------------------------------- -/
/-       Decidable Types and Conversions                -/
/- ---------------------------------------------------- -/

/-- Path environment with decidable (AssocMap-based) paths.
    Only non-trivial paths need to be stored: self-loops are always ε,
    and missing entries default to empty. -/
structure PathEnvDec where
  refs : List Aref
  paths : AssocMap (Aref × Aref) (Regex PathElement)

/-- Convert a decidable PathEnv to the standard PathEnv.
    Self-loops always return ε; missing entries return empty. -/
def PathEnvDec.toPathEnv (ped : PathEnvDec) : PathEnv :=
  { refs := ped.refs
    paths := fun (u, v) =>
      if u = v then Regex.ε
      else match lookup ped.paths (u, v) with
           | some r => r
           | none => Regex.empty }

/-- Initial decidable PathEnv with root present and no paths. -/
def PathEnvDec.init : PathEnvDec :=
  { refs := [.root], paths := .empty }

/-- Conversion of init produces PathEnv.init -/
theorem PathEnvDec.init_toPathEnv : PathEnvDec.init.toPathEnv = PathEnv.init := by
  simp only [PathEnvDec.init, toPathEnv, PathEnv.init]
  show PathEnv.mk [.root] _ = PathEnv.mk [.root] _
  congr 1

/-- Initial decidable PathEnv for a function: includes .root and all abstract refs from ref-typed params. -/
def init_fun_pathEnvDec (params : List (Var × MoveType)) : PathEnvDec :=
  let paramRefs := params.filterMap (fun (_, τ) => match τ with
    | .ref _ r _ => some r
    | _ => none)
  { refs := .root :: paramRefs, paths := .empty }

/-- Conversion of init_fun_pathEnvDec produces init_fun_pathEnv -/
theorem init_fun_pathEnvDec_toPathEnv (f : FunDef) :
    (init_fun_pathEnvDec f.params).toPathEnv = init_fun_pathEnv f := by
  simp only [init_fun_pathEnvDec, PathEnvDec.toPathEnv, init_fun_pathEnv]
  congr 1

/-- Type environment using decidable PathEnv -/
structure TypeEnvDec where
  siteEnv : SiteEnv
  varEnv  : VarEnv
  pathEnv : PathEnvDec
  funEnv  : FunEnv

/-- Convert a decidable TypeEnv to the standard TypeEnv -/
def TypeEnvDec.toTypeEnv (ted : TypeEnvDec) : TypeEnv :=
  { siteEnv := ted.siteEnv
    varEnv := ted.varEnv
    pathEnv := ted.pathEnv.toPathEnv
    funEnv := ted.funEnv }

/-- Label environment with decidable type environments -/
abbrev LabelEnvDec := AssocMap Label TypeEnvDec

/-- Convert a decidable label environment to the standard LabelEnv -/
def LabelEnvDec.toLabelEnv (led : LabelEnvDec) : LabelEnv :=
  mapValues led TypeEnvDec.toTypeEnv

/- ---------------------------------------------------- -/
/-       Boolean WF Checks                              -/
/- ---------------------------------------------------- -/

/-- Boolean check for isBorrowPath: is the regex `char (.root_to_var x)`
    or `concat ε (char (.root_to_var x))`? -/
def isBorrowPath_bool (x : Var) (regex : Regex PathElement) : Bool :=
  match regex with
  | .char c => c == .root_to_var x
  | .concat .ε (.char c) => c == .root_to_var x
  | _ => false

/-- Boolean check for Aref.isFreshRef: is it a refid? -/
def Aref.isFreshRef_bool (a : Aref) : Bool :=
  match a with
  | .refid _ => true
  | _ => false

/-- All references in a SiteEnv are not root (boolean check) -/
def SiteEnv.refsNotRoot_bool (senv : SiteEnv) : Bool :=
  senv.entries.all fun (_, τ) =>
    match τ with
    | .ref _ r _ => r != .root
    | .basic _ => true

/-- All references in a VarEnv are not root (boolean check) -/
def VarEnv.refsNotRoot_bool (venv : VarEnv) : Bool :=
  venv.entries.all fun (_, (_, τ, _)) =>
    match τ with
    | .ref _ r _ => r != .root
    | .basic _ => true

/-- Boolean well-formedness check for PathEnvDec:
    1. root ∈ refs
    2. All stored entry keys have source in refs
    3. All stored entry keys have target in refs -/
def PathEnvDec.wellFormed_bool (ped : PathEnvDec) : Bool :=
  ped.refs.contains .root &&
  ped.paths.entries.all (fun ((u, _), _) => ped.refs.contains u) &&
  ped.paths.entries.all (fun ((_, v), _) => ped.refs.contains v)

/-- Boolean check: all valid var refs are tracked in pathEnv.refs -/
def TypeEnvDec.varRefsTracked_bool (ted : TypeEnvDec) : Bool :=
  ted.varEnv.entries.all fun (_, (isv, τ, _)) =>
    match isv, τ with
    | .validVar, .ref _ r _ => ted.pathEnv.refs.contains r
    | _, _ => true

/-- Boolean check: valid var refs are pairwise distinct (no two entries share a ref) -/
def TypeEnvDec.varRefsUnique_bool (ted : TypeEnvDec) : Bool :=
  ted.varEnv.entries.all fun (x, (isv1, τ1, _)) =>
    match isv1, τ1 with
    | .validVar, .ref _ r _ =>
      ted.varEnv.entries.all fun (y, (isv2, τ2, _)) =>
        match isv2, τ2 with
        | .validVar, .ref _ r' _ => decide (x = y) || decide (r ≠ r')
        | _, _ => true
    | _, _ => true

/-- Boolean well-formedness check for TypeEnvDec -/
def TypeEnvDec.wellFormed_bool (ted : TypeEnvDec) : Bool :=
  ted.pathEnv.wellFormed_bool &&
  SiteEnv.refsNotRoot_bool ted.siteEnv &&
  VarEnv.refsNotRoot_bool ted.varEnv

/-- Boolean well-formedness check for all entries in a LabelEnvDec -/
def LabelEnvDec.allWellFormed_bool (led : LabelEnvDec) : Bool :=
  led.entries.all fun (_, ted) => ted.wellFormed_bool

/- ---------------------------------------------------- -/
/-       Soundness Proofs                               -/
/- ---------------------------------------------------- -/

private theorem isBorrowPath_bool_sound (x : Var) (regex : Regex PathElement) :
    isBorrowPath_bool x regex = true → isBorrowPath x regex := by
  intro h
  cases regex with
  | char c =>
    simp only [isBorrowPath_bool, beq_iff_eq] at h
    simp only [isBorrowPath]; exact h
  | concat r1 r2 =>
    cases r1 with
    | ε =>
      cases r2 with
      | char c =>
        simp only [isBorrowPath_bool, beq_iff_eq] at h
        simp only [isBorrowPath]; exact h
      | _ => simp [isBorrowPath_bool] at h
    | _ => simp [isBorrowPath_bool] at h
  | _ => simp [isBorrowPath_bool] at h

private theorem Aref_isFreshRef_bool_sound (a : Aref) :
    Aref.isFreshRef_bool a = true → Aref.isFreshRef a := by
  intro h
  cases a with
  | refid n => exact ⟨n, rfl⟩
  | root => simp [Aref.isFreshRef_bool] at h
  | varRef _ => simp [Aref.isFreshRef_bool] at h

private theorem SiteEnv_refsNotRoot_bool_sound (senv : SiteEnv) :
    SiteEnv.refsNotRoot_bool senv = true → SiteEnv.RefsNotRoot senv := by
  intro h s τ hlookup
  simp only [SiteEnv.refsNotRoot_bool, List.all_eq_true] at h
  have hmem := lookup_some senv s τ hlookup
  have := h (s, τ) hmem
  cases τ with
  | basic _ => trivial
  | ref bt r bk =>
    simp only [bne_iff_ne] at this
    exact this

private theorem VarEnv_refsNotRoot_bool_sound (venv : VarEnv) :
    VarEnv.refsNotRoot_bool venv = true → VarEnv.RefsNotRoot venv := by
  intro h x entry hlookup
  simp only [VarEnv.refsNotRoot_bool, List.all_eq_true] at h
  have hmem := lookup_some venv x entry hlookup
  obtain ⟨isv, τ, m⟩ := entry
  have := h (x, (isv, τ, m)) hmem
  simp only at this
  cases τ with
  | basic _ => trivial
  | ref bt r bk =>
    simp only [bne_iff_ne] at this
    exact this

/-- Key lemma: if u ∉ refs and all stored entries have source in refs,
    then lookup of (u, v) returns none for any v -/
private theorem lookup_none_of_non_member_from (ped : PathEnvDec) (u v : Aref)
    (hguard_from : ped.paths.entries.all (fun ((u, _), _) => ped.refs.contains u) = true)
    (hu_notin : u ∉ ped.refs) :
    lookup ped.paths (u, v) = none := by
  simp only [List.all_eq_true, List.contains_eq_any_beq, List.any_eq_true,
             beq_iff_eq] at hguard_from
  by_cases hlookup : ∃ regex, lookup ped.paths (u, v) = some regex
  · obtain ⟨regex, hlookup⟩ := hlookup
    have hmem := lookup_some ped.paths (u, v) regex hlookup
    have hg := hguard_from ((u, v), regex) hmem
    simp only at hg
    obtain ⟨r', hr'mem, hr'eq⟩ := hg
    rw [← hr'eq] at hr'mem
    exact absurd hr'mem hu_notin
  · cases h : lookup ped.paths (u, v) with
    | none => rfl
    | some regex => exact absurd ⟨regex, h⟩ hlookup

/-- Key lemma: if v ∉ refs and all stored entries have target in refs,
    then lookup of (u, v) returns none for any u -/
private theorem lookup_none_of_non_member_to (ped : PathEnvDec) (u v : Aref)
    (hguard_to : ped.paths.entries.all (fun ((_, v), _) => ped.refs.contains v) = true)
    (hv_notin : v ∉ ped.refs) :
    lookup ped.paths (u, v) = none := by
  simp only [List.all_eq_true, List.contains_eq_any_beq, List.any_eq_true,
             beq_iff_eq] at hguard_to
  by_cases hlookup : ∃ regex, lookup ped.paths (u, v) = some regex
  · obtain ⟨regex, hlookup⟩ := hlookup
    have hmem := lookup_some ped.paths (u, v) regex hlookup
    have hg := hguard_to ((u, v), regex) hmem
    simp only at hg
    obtain ⟨r', hr'mem, hr'eq⟩ := hg
    rw [← hr'eq] at hr'mem
    exact absurd hr'mem hv_notin
  · cases h : lookup ped.paths (u, v) with
    | none => rfl
    | some regex => exact absurd ⟨regex, h⟩ hlookup

theorem PathEnvDec.wellFormed_bool_sound (ped : PathEnvDec) :
    ped.wellFormed_bool = true → PathEnv.WellFormed ped.toPathEnv := by
  intro h
  simp only [wellFormed_bool, Bool.and_eq_true] at h
  obtain ⟨⟨hroot, hguard_from⟩, hguard_to⟩ := h
  constructor
  · -- refs_complete: r ∉ refs → paths (.root, r) = .empty
    intro r hr
    simp only [toPathEnv]
    by_cases hrr : Aref.root = r
    · subst hrr
      simp only [List.contains_eq_any_beq, List.any_eq_true, beq_iff_eq] at hroot
      obtain ⟨r', hr'mem, hr'eq⟩ := hroot
      exact absurd (hr'eq ▸ hr'mem) hr
    · simp only [hrr, ↓reduceIte]
      have := lookup_none_of_non_member_to ped .root r hguard_to hr
      simp only [this]
  · -- root_in_refs: .root ∈ refs
    simp only [toPathEnv, List.contains_eq_any_beq, List.any_eq_true, beq_iff_eq] at hroot ⊢
    obtain ⟨r', hr'mem, hr'eq⟩ := hroot
    exact hr'eq ▸ hr'mem
  · -- from_untracked_to_root_empty: u ∉ refs → u ≠ .root → paths(u, .root) = .empty
    intro u hu huroot
    simp only [toPathEnv]
    simp only [huroot, ↓reduceIte]
    have := lookup_none_of_non_member_from ped u .root hguard_from hu
    simp only [this]
  · -- self_loop_accepts_nil
    intro u; simp only [toPathEnv, ↓reduceIte, interpret_regex]

/-- Non-member refs have no outgoing paths in a well-formed PathEnvDec -/
theorem PathEnvDec.toPathEnv_non_member_from (ped : PathEnvDec)
    (hwf : ped.wellFormed_bool = true) :
    ∀ u v p, u ∉ ped.toPathEnv.refs → u ≠ .root → u ≠ v →
    ¬interpret_regex (ped.toPathEnv.paths (u, v)) p := by
  intro u v p hu _huroot huv
  simp only [wellFormed_bool, Bool.and_eq_true] at hwf
  obtain ⟨⟨_, hguard_from⟩, _⟩ := hwf
  simp only [toPathEnv] at hu ⊢
  simp only [huv, ↓reduceIte]
  rw [lookup_none_of_non_member_from ped u v hguard_from hu]
  exact fun h => h

/-- Non-member refs have no incoming paths in a well-formed PathEnvDec -/
theorem PathEnvDec.toPathEnv_non_member_to (ped : PathEnvDec)
    (hwf : ped.wellFormed_bool = true) :
    ∀ u v p, v ∉ ped.toPathEnv.refs → v ≠ .root → u ≠ v →
    ¬interpret_regex (ped.toPathEnv.paths (u, v)) p := by
  intro u v p hv _hvroot huv
  simp only [wellFormed_bool, Bool.and_eq_true] at hwf
  obtain ⟨⟨_, _⟩, hguard_to⟩ := hwf
  simp only [toPathEnv] at hv ⊢
  simp only [huv, ↓reduceIte]
  rw [lookup_none_of_non_member_to ped u v hguard_to hv]
  exact fun h => h

theorem TypeEnvDec.wellFormed_bool_sound (ted : TypeEnvDec) :
    ted.wellFormed_bool = true → TypeEnv.WellFormed ted.toTypeEnv := by
  intro h
  simp only [wellFormed_bool, Bool.and_eq_true] at h
  obtain ⟨⟨hpe, hse⟩, hve⟩ := h
  exact {
    pathEnv_wf := PathEnvDec.wellFormed_bool_sound ted.pathEnv hpe
    siteEnv_wf := SiteEnv_refsNotRoot_bool_sound ted.siteEnv hse
    varEnv_wf := VarEnv_refsNotRoot_bool_sound ted.varEnv hve
  }

/- ---------------------------------------------------- -/
/-       Wrapper and Soundness                          -/
/- ---------------------------------------------------- -/

/-- Decidable type checking wrapper: checks well-formedness of all label environments,
    converts to standard types, and delegates to `check_fun`. -/
def check_fun_dec (f : FunDef) (lenvDec : LabelEnvDec) : Bool :=
  lenvDec.allWellFormed_bool && check_fun f lenvDec.toLabelEnv

/-- Soundness: if the decidable check succeeds, the relational judgment holds. -/
theorem check_fun_dec_sound (f : FunDef) (lenvDec : LabelEnvDec) :
    check_fun_dec f lenvDec = true → typecheck_fun f lenvDec.toLabelEnv := by
  intro h
  simp only [check_fun_dec, Bool.and_eq_true] at h
  obtain ⟨hwf_all, hcheck⟩ := h
  apply check_fun_sound f lenvDec.toLabelEnv _ hcheck
  -- Prove: ∀ l env, lookup toLabelEnv l = some env → TypeEnv.WellFormed env
  intro l env hlookup
  -- Relate lookup in toLabelEnv to lookup in lenvDec
  simp only [LabelEnvDec.toLabelEnv, lookup_mapValues] at hlookup
  -- hlookup : (lookup lenvDec l).map TypeEnvDec.toTypeEnv = some env
  cases hlenv : lookup lenvDec l with
  | none => simp [hlenv] at hlookup
  | some ted =>
    simp [hlenv, Option.map] at hlookup
    subst hlookup
    -- ted is in lenvDec, so its wellFormed_bool is true
    simp only [LabelEnvDec.allWellFormed_bool, List.all_eq_true] at hwf_all
    have hmem := lookup_some lenvDec l ted hlenv
    exact TypeEnvDec.wellFormed_bool_sound ted (hwf_all (l, ted) hmem)

/-- Extracts well-formedness from a successful check_fun_dec.
    If check_fun_dec succeeds, all label environments are well-formed. -/
theorem check_fun_dec_lenv_wf (f : FunDef) (lenvDec : LabelEnvDec) :
    check_fun_dec f lenvDec = true →
    ∀ l env, lookup lenvDec.toLabelEnv l = some env → TypeEnv.WellFormed env := by
  intro h l env hlookup
  simp only [check_fun_dec, Bool.and_eq_true] at h
  obtain ⟨hwf_all, _⟩ := h
  simp only [LabelEnvDec.toLabelEnv, lookup_mapValues] at hlookup
  cases hlenv : lookup lenvDec l with
  | none => simp [hlenv] at hlookup
  | some ted =>
    simp [hlenv, Option.map] at hlookup
    subst hlookup
    simp only [LabelEnvDec.allWellFormed_bool, List.all_eq_true] at hwf_all
    have hmem := lookup_some lenvDec l ted hlenv
    exact TypeEnvDec.wellFormed_bool_sound ted (hwf_all (l, ted) hmem)

/-- Non-member paths property (from) from a successful check_fun_dec -/
theorem check_fun_dec_lenv_non_member_from (f : FunDef) (lenvDec : LabelEnvDec) :
    check_fun_dec f lenvDec = true →
    ∀ l env, lookup lenvDec.toLabelEnv l = some env →
    ∀ u v p, u ∉ env.pathEnv.refs → u ≠ .root → u ≠ v →
    ¬interpret_regex (env.pathEnv.paths (u, v)) p := by
  intro h l env hlookup
  simp only [check_fun_dec, Bool.and_eq_true] at h
  obtain ⟨hwf_all, _⟩ := h
  simp only [LabelEnvDec.toLabelEnv, lookup_mapValues] at hlookup
  cases hlenv : lookup lenvDec l with
  | none => simp [hlenv] at hlookup
  | some ted =>
    simp [hlenv, Option.map] at hlookup
    subst hlookup
    simp only [LabelEnvDec.allWellFormed_bool, List.all_eq_true] at hwf_all
    have hmem := lookup_some lenvDec l ted hlenv
    have hwf := hwf_all (l, ted) hmem
    simp only [TypeEnvDec.wellFormed_bool, Bool.and_eq_true] at hwf
    exact PathEnvDec.toPathEnv_non_member_from ted.pathEnv hwf.1.1

/-- Non-member paths property (to) from a successful check_fun_dec -/
theorem check_fun_dec_lenv_non_member_to (f : FunDef) (lenvDec : LabelEnvDec) :
    check_fun_dec f lenvDec = true →
    ∀ l env, lookup lenvDec.toLabelEnv l = some env →
    ∀ u v p, v ∉ env.pathEnv.refs → v ≠ .root → u ≠ v →
    ¬interpret_regex (env.pathEnv.paths (u, v)) p := by
  intro h l env hlookup
  simp only [check_fun_dec, Bool.and_eq_true] at h
  obtain ⟨hwf_all, _⟩ := h
  simp only [LabelEnvDec.toLabelEnv, lookup_mapValues] at hlookup
  cases hlenv : lookup lenvDec l with
  | none => simp [hlenv] at hlookup
  | some ted =>
    simp [hlenv, Option.map] at hlookup
    subst hlookup
    simp only [LabelEnvDec.allWellFormed_bool, List.all_eq_true] at hwf_all
    have hmem := lookup_some lenvDec l ted hlenv
    have hwf := hwf_all (l, ted) hmem
    simp only [TypeEnvDec.wellFormed_bool, Bool.and_eq_true] at hwf
    exact PathEnvDec.toPathEnv_non_member_to ted.pathEnv hwf.1.1

/-- Self-loops in toPathEnv are always ε, so they only accept p = [] -/
theorem check_fun_dec_lenv_self_loop (f : FunDef) (lenvDec : LabelEnvDec) :
    check_fun_dec f lenvDec = true →
    ∀ l env, lookup lenvDec.toLabelEnv l = some env →
    ∀ u p, interpret_regex (env.pathEnv.paths (u, u)) p → p = [] := by
  intro _ l env hlookup u p hp
  simp only [LabelEnvDec.toLabelEnv, lookup_mapValues] at hlookup
  cases hlenv : lookup lenvDec l with
  | none => simp [hlenv] at hlookup
  | some ted =>
    simp [hlenv, Option.map] at hlookup
    subst hlookup
    -- env.pathEnv = ted.pathEnv.toPathEnv
    -- toPathEnv.paths (u, u) = if u = u then ε else ... = ε
    simp only [TypeEnvDec.toTypeEnv, PathEnvDec.toPathEnv] at hp
    -- paths (u, u) = ε since u = u
    simp only [↓reduceIte, interpret_regex] at hp
    exact hp

/-- Boolean check: all label env entries have tracked var refs -/
def LabelEnvDec.allVarRefsTracked_bool (led : LabelEnvDec) : Bool :=
  led.entries.all fun (_, ted) => ted.varRefsTracked_bool

/-- Boolean check: all label env entries have unique var refs -/
def LabelEnvDec.allVarRefsUnique_bool (led : LabelEnvDec) : Bool :=
  led.entries.all fun (_, ted) => ted.varRefsUnique_bool

/-- Var refs tracked: all valid var refs are in pathEnv.refs -/
theorem lenvDec_var_tracked (lenvDec : LabelEnvDec)
    (h : lenvDec.allVarRefsTracked_bool = true) :
    ∀ l env, lookup lenvDec.toLabelEnv l = some env →
    ∀ x bt r bk ms, lookup env.varEnv x = some (.validVar, .ref bt r bk, ms) →
    r ∈ env.pathEnv.refs := by
  intro l env hlookup
  simp only [LabelEnvDec.toLabelEnv, lookup_mapValues] at hlookup
  cases hlenv : lookup lenvDec l with
  | none => simp [hlenv] at hlookup
  | some ted =>
    simp [hlenv, Option.map] at hlookup
    subst hlookup
    simp only [LabelEnvDec.allVarRefsTracked_bool, List.all_eq_true] at h
    have hmem := lookup_some lenvDec l ted hlenv
    have hvrt := h (l, ted) hmem
    simp only [TypeEnvDec.varRefsTracked_bool, List.all_eq_true] at hvrt
    intro x bt r bk ms hlook
    have hmem_entry := lookup_some ted.varEnv x (.validVar, .ref bt r bk, ms) hlook
    have := hvrt (x, (.validVar, .ref bt r bk, ms)) hmem_entry
    simp only at this
    simp only [List.contains_eq_any_beq, List.any_eq_true, beq_iff_eq] at this
    obtain ⟨r', hr'mem, hr'eq⟩ := this
    simp only [TypeEnvDec.toTypeEnv, PathEnvDec.toPathEnv]
    rw [hr'eq]; exact hr'mem

/-- Var refs unique: no two distinct valid vars share a ref -/
theorem lenvDec_var_unique (lenvDec : LabelEnvDec)
    (h : lenvDec.allVarRefsUnique_bool = true) :
    ∀ l env, lookup lenvDec.toLabelEnv l = some env →
    ∀ r x y bt bt' bk bk' ms ms', x ≠ y →
    lookup env.varEnv x = some (.validVar, .ref bt r bk, ms) →
    lookup env.varEnv y = some (.validVar, .ref bt' r bk', ms') → False := by
  intro l env hlookup
  simp only [LabelEnvDec.toLabelEnv, lookup_mapValues] at hlookup
  cases hlenv : lookup lenvDec l with
  | none => simp [hlenv] at hlookup
  | some ted =>
    simp [hlenv, Option.map] at hlookup
    subst hlookup
    simp only [LabelEnvDec.allVarRefsUnique_bool, List.all_eq_true] at h
    have hmem := lookup_some lenvDec l ted hlenv
    have hvru := h (l, ted) hmem
    -- hvru : varRefsUnique_bool ted = true
    -- All-pairs check: for any two valid-var ref entries, either same key or different ref
    unfold TypeEnvDec.varRefsUnique_bool at hvru
    rw [List.all_eq_true] at hvru
    intro r x y bt bt' bk bk' ms ms' hne hlook_x hlook_y
    simp only [TypeEnvDec.toTypeEnv] at hlook_x hlook_y
    have hmem_x := lookup_some ted.varEnv x _ hlook_x
    have hmem_y := lookup_some ted.varEnv y _ hlook_y
    have hx := hvru _ hmem_x
    simp only [] at hx
    rw [List.all_eq_true] at hx
    have hy := hx _ hmem_y
    simp only [] at hy
    -- hy : decide (x = y) || decide (r ≠ r) = true
    rw [Bool.or_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hy
    rcases hy with rfl | habs
    · exact hne rfl
    · exact habs rfl

/- ---------------------------------------------------- -/
/-       Decidable Function Environment                  -/
/- ---------------------------------------------------- -/

/-- Decidable typing environments for a set of functions.
    Maps function names to their `LabelEnvDec` typing environments. -/
abbrev FunTypingEnv := AssocMap Id LabelEnvDec

/-- Boolean check: every function in funEnv has a corresponding entry in
    funTypingEnv and passes check_fun_dec. -/
def checkFunEnv (funEnv : AssocMap Id FunDef) (fte : FunTypingEnv) : Bool :=
  funEnv.entries.all fun (fname, fdef) =>
    match lookup fte fname with
    | some lenvDec => check_fun_dec fdef lenvDec
    | none => false

/-- Soundness: if checkFunEnv succeeds, every function in funEnv is well-typed. -/
theorem checkFunEnv_sound (funEnv : AssocMap Id FunDef) (fte : FunTypingEnv) :
    checkFunEnv funEnv fte = true →
    ∀ fname fdef, lookup funEnv fname = some fdef →
      ∃ lenv', typecheck_fun fdef lenv' := by
  intro hcheck fname fdef hlookup
  simp only [checkFunEnv, List.all_eq_true] at hcheck
  have hmem := lookup_some funEnv fname fdef hlookup
  have hentry := hcheck (fname, fdef) hmem
  simp only [] at hentry
  cases hlenv : lookup fte fname with
  | none => simp [hlenv] at hentry
  | some lenvDec =>
    simp [hlenv] at hentry
    exact ⟨lenvDec.toLabelEnv, check_fun_dec_sound fdef lenvDec hentry⟩

/- ---------------------------------------------------- -/
/-       FunEnv consistency across lenv entries           -/
/- ---------------------------------------------------- -/

/-- Boolean check: all TypeEnvDec entries in a LabelEnvDec have the same funEnv. -/
def LabelEnvDec.checkFunEnvConsistent (led : LabelEnvDec) : Bool :=
  match led.entries with
  | [] => true
  | (_, first) :: rest =>
    rest.all (fun (_, ted) => decide (ted.funEnv = first.funEnv))

/-- Soundness: if all entries have the same funEnv, then any two lookups
    in the converted toLabelEnv agree on funEnv. -/
theorem LabelEnvDec.checkFunEnvConsistent_sound (led : LabelEnvDec)
    (h : led.checkFunEnvConsistent = true) :
    ∀ l1 l2 env1 env2,
      lookup led.toLabelEnv l1 = some env1 →
      lookup led.toLabelEnv l2 = some env2 →
      env1.funEnv = env2.funEnv := by
  intro l1 l2 env1 env2 h1 h2
  simp only [LabelEnvDec.toLabelEnv, lookup_mapValues] at h1 h2
  cases hl1 : lookup led l1 with
  | none => simp [hl1] at h1
  | some ted1 =>
    simp [hl1, Option.map] at h1; subst h1
    cases hl2 : lookup led l2 with
    | none => simp [hl2] at h2
    | some ted2 =>
      simp [hl2, Option.map] at h2; subst h2
      simp only [TypeEnvDec.toTypeEnv]
      have hm1 := lookup_some led l1 ted1 hl1
      have hm2 := lookup_some led l2 ted2 hl2
      unfold checkFunEnvConsistent at h
      cases hes : led.entries with
      | nil => simp [hes] at hm1
      | cons first rest =>
        rw [hes] at h hm1 hm2
        simp only [List.all_eq_true, decide_eq_true_eq] at h
        simp only [List.mem_cons] at hm1 hm2
        rcases hm1 with ⟨rfl, rfl⟩ | hm1
        · rcases hm2 with ⟨rfl, rfl⟩ | hm2
          · rfl
          · exact (h _ hm2).symm
        · rcases hm2 with ⟨rfl, rfl⟩ | hm2
          · exact h _ hm1
          · exact (h _ hm1).trans (h _ hm2).symm

end LeanMove.Typing
