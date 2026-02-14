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

/-- All references in a VarEnv are fresh refs (boolean check) -/
def VarEnv.refsAreFresh_bool (venv : VarEnv) : Bool :=
  venv.entries.all fun (_, (_, τ, _)) =>
    match τ with
    | .ref _ r _ => Aref.isFreshRef_bool r
    | .basic _ => true

/-- Boolean well-formedness check for PathEnvDec:
    1. root ∈ refs
    2. varRef x ∈ refs → isBorrowPath x (paths (.root, .varRef x))
    3. For entries with key (.root, r), r must be in refs
    4. For entries with key (u, .root), u must be in refs -/
def PathEnvDec.wellFormed_bool (ped : PathEnvDec) : Bool :=
  ped.refs.contains .root &&
  ped.refs.all (fun r =>
    match r with
    | .varRef x => isBorrowPath_bool x (ped.toPathEnv.paths (.root, .varRef x))
    | _ => true) &&
  ped.paths.entries.all (fun ((u, v), _) =>
    !(u == Aref.root) || ped.refs.contains v) &&
  ped.paths.entries.all (fun ((u, v), _) =>
    !(v == Aref.root) || ped.refs.contains u)

/-- Boolean well-formedness check for TypeEnvDec -/
def TypeEnvDec.wellFormed_bool (ted : TypeEnvDec) : Bool :=
  ted.pathEnv.wellFormed_bool &&
  SiteEnv.refsNotRoot_bool ted.siteEnv &&
  VarEnv.refsAreFresh_bool ted.varEnv

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

private theorem VarEnv_refsAreFresh_bool_sound (venv : VarEnv) :
    VarEnv.refsAreFresh_bool venv = true → VarEnv.RefsAreFresh venv := by
  intro h x entry hlookup
  simp only [VarEnv.refsAreFresh_bool, List.all_eq_true] at h
  have hmem := lookup_some venv x entry hlookup
  obtain ⟨isv, τ, m⟩ := entry
  have := h (x, (isv, τ, m)) hmem
  simp only at this
  cases τ with
  | basic _ => trivial
  | ref bt r bk =>
    simp only at this ⊢
    exact Aref_isFreshRef_bool_sound r this

/-- Key lemma: if r ∉ refs and there's no entry (.root, r) in the AssocMap,
    then lookup of (.root, r) returns none -/
private theorem lookup_none_of_no_root_entry (ped : PathEnvDec) (r : Aref)
    (_hr_not_root : r ≠ .root)
    (hguard : ped.paths.entries.all (fun ((u, v), _) =>
      !(u == Aref.root) || ped.refs.contains v) = true)
    (hr_notin : r ∉ ped.refs) :
    lookup ped.paths (.root, r) = none := by
  simp only [List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
             List.contains_eq_any_beq] at hguard
  -- If lookup returns some, we get a contradiction
  by_cases hlookup : ∃ regex, lookup ped.paths (.root, r) = some regex
  · obtain ⟨regex, hlookup⟩ := hlookup
    have hmem := lookup_some ped.paths (.root, r) regex hlookup
    have hg := hguard ((.root, r), regex) hmem
    simp only [List.any_eq_true, beq_iff_eq] at hg
    -- hg : (Aref.root == Aref.root) = false ∨ ∃ ...
    -- The left disjunct is false, so we get the right
    cases hg with
    | inl habs => simp at habs
    | inr hcontains =>
      obtain ⟨r', hr'mem, hr'eq⟩ := hcontains
      rw [← hr'eq] at hr'mem
      exact absurd hr'mem hr_notin
  · cases h : lookup ped.paths (.root, r) with
    | none => rfl
    | some regex => exact absurd ⟨regex, h⟩ hlookup

/-- Key lemma: if u ∉ refs and the guard check passes, then lookup of (u, .root) returns none -/
private theorem lookup_none_of_no_to_root_entry (ped : PathEnvDec) (u : Aref)
    (_hu_not_root : u ≠ .root)
    (hguard : ped.paths.entries.all (fun ((u, v), _) =>
      !(v == Aref.root) || ped.refs.contains u) = true)
    (hu_notin : u ∉ ped.refs) :
    lookup ped.paths (u, .root) = none := by
  simp only [List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
             List.contains_eq_any_beq] at hguard
  by_cases hlookup : ∃ regex, lookup ped.paths (u, .root) = some regex
  · obtain ⟨regex, hlookup⟩ := hlookup
    have hmem := lookup_some ped.paths (u, .root) regex hlookup
    have hg := hguard ((u, .root), regex) hmem
    simp only [List.any_eq_true, beq_iff_eq] at hg
    cases hg with
    | inl habs => simp at habs
    | inr hcontains =>
      obtain ⟨r', hr'mem, hr'eq⟩ := hcontains
      rw [← hr'eq] at hr'mem
      exact absurd hr'mem hu_notin
  · cases h : lookup ped.paths (u, .root) with
    | none => rfl
    | some regex => exact absurd ⟨regex, h⟩ hlookup

theorem PathEnvDec.wellFormed_bool_sound (ped : PathEnvDec) :
    ped.wellFormed_bool = true → PathEnv.WellFormed ped.toPathEnv := by
  intro h
  simp only [wellFormed_bool, Bool.and_eq_true] at h
  obtain ⟨⟨⟨hroot, hvarrefs⟩, hguard⟩, hguard_to_root⟩ := h
  constructor
  · -- refs_complete: r ∉ refs → paths (.root, r) = .empty
    intro r hr
    simp only [toPathEnv]
    by_cases hrr : Aref.root = r
    · -- root = r, but root ∈ refs by hroot, contradiction
      subst hrr
      simp only [List.contains_eq_any_beq, List.any_eq_true, beq_iff_eq] at hroot
      obtain ⟨r', hr'mem, hr'eq⟩ := hroot
      exact absurd (hr'eq ▸ hr'mem) hr
    · simp only [hrr, ↓reduceIte]
      have hr_ne_root : r ≠ .root := fun h => hrr h.symm
      have := lookup_none_of_no_root_entry ped r hr_ne_root hguard hr
      simp only [this]
  · -- varref_tracked: varRef x ∈ refs → isBorrowPath x (paths (.root, .varRef x))
    intro x hx
    simp only [List.all_eq_true] at hvarrefs
    have := hvarrefs (.varRef x) hx
    simp only at this
    exact isBorrowPath_bool_sound x _ this
  · -- root_in_refs: .root ∈ refs
    simp only [toPathEnv, List.contains_eq_any_beq, List.any_eq_true, beq_iff_eq] at hroot ⊢
    obtain ⟨r', hr'mem, hr'eq⟩ := hroot
    exact hr'eq ▸ hr'mem
  · -- from_untracked_to_root_empty: u ∉ refs → u ≠ .root → paths(u, .root) = .empty
    intro u hu huroot
    simp only [toPathEnv]
    simp only [huroot, ↓reduceIte]
    have := lookup_none_of_no_to_root_entry ped u huroot hguard_to_root hu
    simp only [this]

theorem TypeEnvDec.wellFormed_bool_sound (ted : TypeEnvDec) :
    ted.wellFormed_bool = true → TypeEnv.WellFormed ted.toTypeEnv := by
  intro h
  simp only [wellFormed_bool, Bool.and_eq_true] at h
  obtain ⟨⟨hpe, hse⟩, hve⟩ := h
  exact {
    pathEnv_wf := PathEnvDec.wellFormed_bool_sound ted.pathEnv hpe
    siteEnv_wf := SiteEnv_refsNotRoot_bool_sound ted.siteEnv hse
    varEnv_wf := VarEnv_refsAreFresh_bool_sound ted.varEnv hve
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

end LeanMove.Typing
