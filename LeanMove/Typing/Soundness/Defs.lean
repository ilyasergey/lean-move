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
import LeanMove.Typing.TypesUtils
import LeanMove.Semantics.Smallstep

/-!
# Type Soundness: Definitions and Structural Lemmas

Core definitions and lemmas used by the type soundness proof:
- `HasType`, `RefMap`, `ValueMatchesType`
- readPath/writePath structural lemmas
- `fieldPathOf`, `PathReflectedInHeap`
- `WellTypedState` (17-field central invariant)
- `StackSafe`
- `check_outbound_only_empty` bridge lemma
-/

namespace LeanMove.Typing.TypeSoundness

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Typing
open LeanMove.Semantics
open AssocMap
open Regex

-- ============================================================
-- Part 1: Value–Type Compatibility
-- ============================================================

/-- A runtime `Value` is shape-compatible with a static `BasicMoveType`.
    Recursive: for records, sub-field values must also have matching types.
    Split into two hypotheses to avoid nested inductive issues with ∃.
    Now takes an EnumEnv parameter to resolve enum types. -/
inductive HasType (enumEnv : EnumEnv) : Value → BasicMoveType → Prop where
  | int : ∀ n, HasType enumEnv (.int n) .u64
  | int_u8 : ∀ n, HasType enumEnv (.int n) .u8
  | bool : ∀ b, HasType enumEnv (.bool b) .tbool
  | unit : HasType enumEnv .unit .tunit
  | record : ∀ fields fentries,
      (∀ f, lookup fentries f ≠ none → fields.lookup f ≠ none) →
      (∀ f, fields.lookup f ≠ none → lookup fentries f ≠ none) →
      (∀ f bt v, lookup fentries f = some bt → fields.lookup f = some v → HasType enumEnv v bt) →
      HasType enumEnv (.record fields) (.trecord fentries)
  | vec : ∀ (elems : List Value) (elemTy : BasicMoveType),
      (∀ v, v ∈ elems → HasType enumEnv v elemTy) →
      HasType enumEnv (.vec elemTy elems) (.tvec elemTy)
  | variant : ∀ (vname ename : Id) (fields : List (Field × Value))
      (fentries : AssocMap Field BasicMoveType),
      allEnumQualifiedFieldTypes enumEnv ename = some fentries →
      (∀ f, lookup fentries f ≠ none → fields.lookup f ≠ none) →
      (∀ f, fields.lookup f ≠ none → lookup fentries f ≠ none) →
      (∀ f bt v, lookup fentries f = some bt → fields.lookup f = some v → HasType enumEnv v bt) →
      enumVariantFields enumEnv ename vname ≠ none →
      HasType enumEnv (.variant vname ename fields) (.tenum ename)

/-- HasType transfers across enum environments that agree on all lookups. -/
theorem HasType_enumEnv_transfer {ee1 ee2 : EnumEnv} {v : Value} {bt : BasicMoveType}
    (h : HasType ee1 v bt)
    (heq : ∀ en, ee1.lookup en = ee2.lookup en) :
    HasType ee2 v bt := by
  induction h with
  | int n => exact .int n
  | int_u8 n => exact .int_u8 n
  | bool b => exact .bool b
  | unit => exact .unit
  | record fields fentries h1 h2 h3 ih =>
    exact .record fields fentries h1 h2 (fun f bt v hlookup hfield => ih f bt v hlookup hfield)
  | vec elems elemTy _ ih =>
    exact .vec elems elemTy (fun v hv => ih v hv)
  | variant vname ename fields fentries haqf hdom hrev htyped hvv ih =>
    have haqf2 : allEnumQualifiedFieldTypes ee2 ename = some fentries := by
      unfold allEnumQualifiedFieldTypes at haqf ⊢; rw [← heq]; exact haqf
    have hvv2 : enumVariantFields ee2 ename vname ≠ none := by
      unfold enumVariantFields at hvv ⊢; rw [← heq]; exact hvv
    exact .variant vname ename fields fentries haqf2 hdom hrev
      (fun f bt v hlookup hfield => ih f bt v hlookup hfield) hvv2

/-- HasType weakens: if every enum found in ee1 is also found (same def) in ee2,
    then HasType transfers from ee1 to ee2. -/
theorem HasType_enumEnv_weaken {ee1 ee2 : EnumEnv} {v : Value} {bt : BasicMoveType}
    (h : HasType ee1 v bt)
    (hext : ∀ en ed, ee1.lookup en = some ed → ee2.lookup en = some ed) :
    HasType ee2 v bt := by
  induction h with
  | int n => exact .int n
  | int_u8 n => exact .int_u8 n
  | bool b => exact .bool b
  | unit => exact .unit
  | record fields fentries h1 h2 h3 ih =>
    exact .record fields fentries h1 h2 (fun f bt v hlookup hfield => ih f bt v hlookup hfield)
  | vec elems elemTy _ ih =>
    exact .vec elems elemTy (fun v hv => ih v hv)
  | variant vname ename fields fentries haqf hdom hrev htyped hvv ih =>
    have haqf2 : allEnumQualifiedFieldTypes ee2 ename = some fentries := by
      unfold allEnumQualifiedFieldTypes at haqf ⊢
      cases hee1 : ee1.lookup ename with
      | none => simp [hee1] at haqf
      | some ed => rw [hext ename ed hee1]; simp [hee1] at haqf; simp; exact haqf
    have hvv2 : enumVariantFields ee2 ename vname ≠ none := by
      unfold enumVariantFields at hvv ⊢
      cases hee1 : ee1.lookup ename with
      | none => simp [hee1] at hvv
      | some ed => rw [hext ename ed hee1]; simp [hee1] at hvv; simp; exact hvv
    exact .variant vname ename fields fentries haqf2 hdom hrev
      (fun f bt v hlookup hfield => ih f bt v hlookup hfield) hvv2

/-- If a value has enum type, it must be a variant. -/
theorem HasType.variant_fields {enumEnv : EnumEnv} {v : Value}
    {ename : Id} :
    HasType enumEnv v (.tenum ename) → ∃ vname fields, v = .variant vname ename fields := by
  intro h; cases h with
  | variant vname _ _ _ _ _ _ _ _ => exact ⟨vname, _, rfl⟩

/-- If a value has record type, it must be a record. -/
theorem HasType.record_fields {enumEnv : EnumEnv} {v : Value} {fentries : AssocMap Field BasicMoveType} :
    HasType enumEnv v (.trecord fentries) → ∃ fields, v = .record fields := by
  intro h; cases h with
  | record fields _ _ _ _ => exact ⟨fields, rfl⟩

/-- If a value has vector type, it must be a vector. -/
theorem HasType.vec_elems {enumEnv : EnumEnv} {v : Value} {elemTy : BasicMoveType} :
    HasType enumEnv v (.tvec elemTy) → ∃ elems, v = .vec elemTy elems := by
  intro h; cases h with
  | vec elems _ _ => exact ⟨elems, rfl⟩

/-- readPath at a typed field succeeds and the sub-value has the field type. -/
theorem HasType.readPath_field {enumEnv : EnumEnv} {fields : List (Field × Value)}
    {fentries : AssocMap Field BasicMoveType} {f : Field} {bt : BasicMoveType} :
    HasType enumEnv (.record fields) (.trecord fentries) →
    lookup fentries f = some bt →
    ∃ vf, readPath (.record fields) [f] = some vf ∧ HasType enumEnv vf bt := by
  intro h hlookup
  cases h with
  | record _ _ hexists _ htyped =>
    have hne : fields.lookup f ≠ none := hexists f (by rw [hlookup]; simp)
    cases hfl : fields.lookup f with
    | none => exact absurd hfl hne
    | some vf =>
      exact ⟨vf, by simp [readPath, hfl], htyped f bt vf hlookup hfl⟩

-- ============================================================
-- Part 2: Reference Map
-- ============================================================

/-- Maps abstract references (Aref) to concrete heap locations with field paths.
    This is the key bridge between the static type system and runtime state. -/
structure RefMap where
  map : Aref → Option (Loc × List Field)

/-- A value matches a MoveType, given a reference map for resolving abstract refs.
    For basic types, the value must have that basic type (via `HasType`).
    For ref types, we track the concrete location via the rmap. -/
def ValueMatchesType (enumEnv : EnumEnv) (v : Value) (τ : MoveType) (rmap : RefMap) : Prop :=
  match τ with
  | .basic bt => HasType enumEnv v bt
  | .ref _bt r _bk =>
    ∃ loc path, v = .ref loc path ∧ rmap.map r = some (loc, path)

/-- Extend a RefMap with mappings from returned reference values.
    For each result site that has a ref type in the siteEnv, maps the abstract ref
    to the concrete (loc, path) from the corresponding returned value.
    Existing mappings are preserved (output refs are fresh, so no conflicts). -/
def RefMap.extendWithReturns (rmap : RefMap) (siteEnv : SiteEnv) :
    List Site → List Value → RefMap
  | [], [] => rmap
  | s :: ss, v :: vs =>
    let rmap' := match lookup siteEnv s, v with
      | some (.ref _ r _), .ref loc path =>
        RefMap.mk (fun r' => if r' = r then some (loc, path) else rmap.map r')
      | _, _ => rmap
    rmap'.extendWithReturns siteEnv ss vs
  | _, _ => rmap

/-- extendWithReturns preserves mappings for refs not among the output refs -/
theorem RefMap.extendWithReturns_preserves (rmap : RefMap) (siteEnv : SiteEnv)
    (sites : List Site) (vals : List Value) (r : Aref) (p : Loc × List Field)
    (h : rmap.map r = some p)
    (hne : ∀ s ∈ sites, ∀ bt r' bk, lookup siteEnv s = some (.ref bt r' bk) → r' ≠ r) :
    (RefMap.extendWithReturns rmap siteEnv sites vals).map r = some p := by
  induction sites generalizing vals rmap with
  | nil => cases vals <;> simp [extendWithReturns, h]
  | cons s ss ih =>
    cases vals with
    | nil => simp [extendWithReturns, h]
    | cons v vs =>
      simp only [extendWithReturns]
      have hne_s := hne s (List.mem_cons_self ..)
      have hne_ss : ∀ s' ∈ ss, ∀ bt r' bk, lookup siteEnv s' = some (.ref bt r' bk) → r' ≠ r :=
        fun s' hs' => hne s' (List.mem_cons_of_mem _ hs')
      cases hse : lookup siteEnv s with
      | none => exact ih rmap vs h hne_ss
      | some τ =>
        cases τ with
        | basic _ => exact ih rmap vs h hne_ss
        | ref bt r' bk =>
          have hr'ne : r' ≠ r := hne_s bt r' bk hse
          cases v with
          | ref loc path =>
            apply ih _ vs _ hne_ss
            show (if r = r' then some (loc, path) else rmap.map r) = some p
            rw [if_neg (Ne.symm hr'ne)]
            exact h
          | int _ => exact ih rmap vs h hne_ss
          | bool _ => exact ih rmap vs h hne_ss
          | unit => exact ih rmap vs h hne_ss
          | «record» _ => exact ih rmap vs h hne_ss
          | vec _ _ => exact ih rmap vs h hne_ss
          | variant _ _ _ => exact ih rmap vs h hne_ss

/-- extendWithReturns preserves none for refs not among the output refs -/
theorem RefMap.extendWithReturns_preserves_none (rmap : RefMap) (siteEnv : SiteEnv)
    (sites : List Site) (vals : List Value) (r : Aref)
    (h : rmap.map r = none)
    (hne : ∀ s ∈ sites, ∀ bt r' bk, lookup siteEnv s = some (.ref bt r' bk) → r' ≠ r) :
    (RefMap.extendWithReturns rmap siteEnv sites vals).map r = none := by
  induction sites generalizing vals rmap with
  | nil => cases vals <;> simp [extendWithReturns, h]
  | cons s ss ih =>
    cases vals with
    | nil => simp [extendWithReturns, h]
    | cons v vs =>
      simp only [extendWithReturns]
      have hne_s := hne s (List.mem_cons_self ..)
      have hne_ss : ∀ s' ∈ ss, ∀ bt r' bk, lookup siteEnv s' = some (.ref bt r' bk) → r' ≠ r :=
        fun s' hs' => hne s' (List.mem_cons_of_mem _ hs')
      cases hse : lookup siteEnv s with
      | none => exact ih rmap vs h hne_ss
      | some τ =>
        cases τ with
        | basic _ => exact ih rmap vs h hne_ss
        | ref bt r' bk =>
          have hr'ne : r' ≠ r := hne_s bt r' bk hse
          cases v with
          | ref loc path =>
            apply ih _ vs _ hne_ss
            show (if r = r' then some (loc, path) else rmap.map r) = none
            rw [if_neg (Ne.symm hr'ne)]
            exact h
          | int _ => exact ih rmap vs h hne_ss
          | bool _ => exact ih rmap vs h hne_ss
          | unit => exact ih rmap vs h hne_ss
          | «record» _ => exact ih rmap vs h hne_ss
          | vec _ _ => exact ih rmap vs h hne_ss
          | variant _ _ _ => exact ih rmap vs h hne_ss

/-- If extendWithReturns maps r to (loc, path), then either:
    (1) the original rmap already mapped r to (loc, path), or
    (2) Value.ref loc path is among the vals -/
theorem RefMap.extendWithReturns_values (rmap : RefMap) (siteEnv : SiteEnv)
    (sites : List Site) (vals : List Value) (r : Aref) (loc : Loc) (path : List Field)
    (h : (RefMap.extendWithReturns rmap siteEnv sites vals).map r = some (loc, path)) :
    rmap.map r = some (loc, path) ∨ Value.ref loc path ∈ vals := by
  induction sites generalizing vals rmap with
  | nil => cases vals <;> (simp [extendWithReturns] at h; exact Or.inl h)
  | cons s ss ih =>
    cases vals with
    | nil => simp [extendWithReturns] at h; exact Or.inl h
    | cons v vs =>
      -- Put h back in goal so case-splitting reduces the match
      revert h; simp only [extendWithReturns]
      cases hse : lookup siteEnv s with
      | none =>
        intro h
        rcases ih rmap vs h with hold | hnew
        · exact Or.inl hold
        · exact Or.inr (List.mem_cons_of_mem _ hnew)
      | some τ =>
        cases τ with
        | basic _ =>
          intro h
          rcases ih rmap vs h with hold | hnew
          · exact Or.inl hold
          · exact Or.inr (List.mem_cons_of_mem _ hnew)
        | ref bt r' bk =>
          cases v with
          | ref loc' path' =>
            intro h
            rcases ih _ vs h with hold | hnew
            · -- hold : (if r = r' then some (loc', path') else rmap.map r) = some (loc, path)
              by_cases hrr : r = r'
              · subst hrr; simp at hold; obtain ⟨rfl, rfl⟩ := hold
                exact Or.inr (List.Mem.head _)
              · simp [hrr] at hold; exact Or.inl hold
            · exact Or.inr (List.mem_cons_of_mem _ hnew)
          | int _ =>
            intro h; rcases ih rmap vs h with hold | hnew
            · exact Or.inl hold
            · exact Or.inr (List.mem_cons_of_mem _ hnew)
          | bool _ =>
            intro h; rcases ih rmap vs h with hold | hnew
            · exact Or.inl hold
            · exact Or.inr (List.mem_cons_of_mem _ hnew)
          | unit =>
            intro h; rcases ih rmap vs h with hold | hnew
            · exact Or.inl hold
            · exact Or.inr (List.mem_cons_of_mem _ hnew)
          | «record» _ =>
            intro h; rcases ih rmap vs h with hold | hnew
            · exact Or.inl hold
            · exact Or.inr (List.mem_cons_of_mem _ hnew)
          | vec _ _ =>
            intro h; rcases ih rmap vs h with hold | hnew
            · exact Or.inl hold
            · exact Or.inr (List.mem_cons_of_mem _ hnew)
          | variant _ _ _ =>
            intro h; rcases ih rmap vs h with hold | hnew
            · exact Or.inl hold
            · exact Or.inr (List.mem_cons_of_mem _ hnew)

-- ============================================================
-- Part 3: readPath / writePath structural lemmas
-- ============================================================

/-- readPath distributes over append: reading a concatenated path is the same as
    reading the prefix then reading the suffix from the result -/
theorem readPath_append (v : Value) (p1 p2 : List Field) :
    readPath v (p1 ++ p2) = (readPath v p1).bind (readPath · p2) := by
  induction p1 generalizing v with
  | nil => simp [readPath, Option.bind]
  | cons f p1' ih =>
    cases v with
    | record fields =>
      simp only [List.cons_append, readPath]
      cases h : fields.lookup f with
      | none => simp [Option.bind]
      | some v' => exact ih v'
    | int n => simp [readPath, Option.bind]
    | bool b => simp [readPath, Option.bind]
    | unit => simp [readPath, Option.bind]
    | ref loc path => simp [readPath, Option.bind]
    | vec _ _ => simp [readPath, Option.bind]
    | variant _ _ fields =>
      simp only [List.cons_append, readPath]
      cases h : fields.lookup f with
      | none => simp [Option.bind]
      | some v' => exact ih v'

/-- If readPath succeeds on a longer path, it succeeds on any prefix -/
theorem readPath_prefix_succeeds (v : Value) (p1 p2 : List Field) (w : Value) :
    readPath v (p1 ++ p2) = some w →
    ∃ v', readPath v p1 = some v' := by
  rw [readPath_append]
  intro h
  cases hbind : readPath v p1 with
  | none => simp [hbind, Option.bind] at h
  | some v' => exact ⟨v', rfl⟩

/-- If readPath succeeds, writePath also succeeds with any new value.
    This is because both navigate the same structure: both fail exactly when
    a field lookup fails on a non-record value. -/
theorem readPath_some_implies_writePath_some (v : Value) (path : List Field)
    (w newVal : Value) :
    readPath v path = some w →
    ∃ v', writePath v path newVal = some v' := by
  intro hread
  induction path generalizing v with
  | nil =>
    -- readPath v [] = some v, writePath v [] newVal = some newVal
    exact ⟨newVal, by simp [writePath]⟩
  | cons f rest ih =>
    cases v with
    | record fields =>
      simp only [readPath] at hread
      cases hf : fields.lookup f with
      | none => simp [hf] at hread
      | some oldFieldVal =>
        simp [hf] at hread
        obtain ⟨v', hv'⟩ := ih oldFieldVal hread
        exact ⟨.record (fields.map fun (k, fv) => if k == f then (k, v') else (k, fv)),
               by simp [writePath, hf, hv']⟩
    | int n => simp [readPath] at hread
    | bool b => simp [readPath] at hread
    | unit => simp [readPath] at hread
    | ref l p => simp [readPath] at hread
    | vec _ _ => simp [readPath] at hread
    | variant tag enumTy fields =>
      simp only [readPath] at hread
      cases hf : fields.lookup f with
      | none => simp [hf] at hread
      | some oldFieldVal =>
        simp [hf] at hread
        obtain ⟨v', hv'⟩ := ih oldFieldVal hread
        exact ⟨.variant tag enumTy (fields.map fun (k, fv) => if k == f then (k, v') else (k, fv)),
               by simp [writePath, hf, hv']⟩

/-- If readRef succeeds on a heap, writeRef also succeeds with any new value.
    Follows from readPath_some_implies_writePath_some since both operations
    require the same heap read and path navigation to succeed. -/
theorem readRef_ne_none_implies_writeRef_ne_none (h : Heap) (loc : Loc)
    (path : List Field) (newVal : Value) :
    h.readRef loc path ≠ none →
    ∃ h', h.writeRef loc path newVal = some h' := by
  intro hne
  -- readRef h loc path = do { let v ← h.read loc; readPath v path }
  -- Extract that h.read loc and readPath succeed
  simp only [Heap.readRef, bind, Option.bind] at hne
  cases hread : h.read loc with
  | none => simp [hread] at hne
  | some oldVal =>
    simp [hread] at hne
    -- hne : readPath oldVal path ≠ none
    cases hrp : readPath oldVal path with
    | none => exact absurd hrp hne
    | some w =>
      obtain ⟨v', hv'⟩ := readPath_some_implies_writePath_some oldVal path w newVal hrp
      exact ⟨h.write loc v', by simp [Heap.writeRef, bind, Option.bind, hread, hv']⟩

/-- Writing to a heap location preserves reads at different locations -/
theorem heap_write_preserves_read (h : Heap) (wloc rloc : Loc) (v : Value) :
    wloc ≠ rloc →
    (h.write wloc v).read rloc = h.read rloc := by
  intro hne
  simp only [Heap.write, Heap.read]
  exact AssocMap.lookup_insert_ne h.store wloc rloc v (Ne.symm hne)

/-- Writing through writeRef at one location preserves readRef at a different location -/
theorem heap_writeRef_preserves_readRef_diff_loc (h : Heap) (wloc rloc : Loc)
    (wp rp : List Field) (v : Value) (h' : Heap) :
    wloc ≠ rloc →
    h.writeRef wloc wp v = some h' →
    h'.readRef rloc rp = h.readRef rloc rp := by
  intro hne hwrite
  simp only [Heap.writeRef, bind, Option.bind] at hwrite
  cases hread : h.read wloc with
  | none => simp [hread] at hwrite
  | some oldVal =>
    simp [hread] at hwrite
    cases hwp : writePath oldVal wp v with
    | none => simp [hwp] at hwrite
    | some newVal =>
      simp [hwp] at hwrite
      -- hwrite : h.write wloc newVal = h'
      rw [← hwrite]
      simp only [Heap.readRef, bind, Option.bind]
      rw [heap_write_preserves_read h wloc rloc newVal hne]

/-- After heap.alloc, readRef at a different location is unchanged -/
theorem heap_alloc_preserves_readRef (h : Heap) (v : Value) (loc' : Loc) (path : List Field) :
    loc' ≠ h.nextLoc →
    (h.alloc v).1.readRef loc' path = h.readRef loc' path := by
  intro hne
  simp only [Heap.alloc, Heap.readRef, bind, Option.bind, Heap.read]
  rw [AssocMap.lookup_insert_ne h.store h.nextLoc loc' v hne]

/-- After heap.alloc, reading the new location returns the allocated value -/
theorem heap_alloc_read_new (h : Heap) (v : Value) :
    (h.alloc v).1.read (h.alloc v).2 = some v := by
  simp only [Heap.alloc, Heap.read]
  exact AssocMap.lookup_insert_same h.store h.nextLoc v

/-- If readRef succeeds, then read at the base location also succeeds -/
theorem readRef_implies_read (h : Heap) (loc : Loc) (path : List Field) :
    h.readRef loc path ≠ none → h.read loc ≠ none := by
  intro hne habs
  simp only [Heap.readRef, bind, Option.bind, habs] at hne
  exact hne rfl

/-- heap.alloc preserves heap_loc_bound -/
theorem heap_loc_bound_after_alloc (h : Heap) (v : Value)
    (hlb : ∀ loc, h.read loc ≠ none → loc < h.nextLoc) :
    ∀ loc, (h.alloc v).1.read loc ≠ none → loc < (h.alloc v).1.nextLoc := by
  intro loc hne
  show loc < h.nextLoc + 1
  by_cases heq : loc = h.nextLoc
  · subst heq; exact Nat.lt_succ_of_le (Nat.le_refl _)
  · have hread : (h.alloc v).1.read loc = h.read loc := by
      simp only [Heap.alloc, Heap.read]
      exact AssocMap.lookup_insert_ne h.store h.nextLoc loc v heq
    rw [hread] at hne
    exact Nat.lt_succ_of_lt (hlb loc hne)

/-- After heap.alloc, reading an old location (below nextLoc) is unchanged -/
theorem heap_alloc_preserves_read (h : Heap) (v : Value) (loc : Loc) :
    loc < h.nextLoc →
    (h.alloc v).1.read loc = h.read loc := by
  intro hlt
  have hne : loc ≠ h.nextLoc := by intro h; subst h; exact Nat.lt_irrefl _ hlt
  simp only [Heap.alloc, Heap.read]
  exact AssocMap.lookup_insert_ne h.store h.nextLoc loc v hne

/-- If readRef at (loc, path) yields a record with a typed field,
    then readRef at (loc, path ++ [f]) succeeds. -/
theorem HasType.readRef_field_ne_none {enumEnv : EnumEnv} {fentries : AssocMap Field BasicMoveType}
    {bt : BasicMoveType} (heap : Heap) (loc : Loc) (path : List Field) (f : Field) :
    (∃ v, heap.readRef loc path = some v ∧ HasType enumEnv v (.trecord fentries)) →
    lookup fentries f = some bt →
    heap.readRef loc (path ++ [f]) ≠ none := by
  intro ⟨v, hread, htyped⟩ hlookup
  obtain ⟨fields, hv_eq⟩ := HasType.record_fields htyped
  rw [hv_eq] at hread htyped
  obtain ⟨vf, hreadpath, _⟩ := HasType.readPath_field htyped hlookup
  -- readRef loc (path ++ [f]) decomposes via readPath_append
  simp only [Heap.readRef, bind, Option.bind] at hread ⊢
  cases hbase : heap.read loc with
  | none => simp [hbase] at hread
  | some baseVal =>
    simp [hbase] at hread ⊢
    rw [readPath_append, hread, Option.bind]
    rw [hreadpath]
    simp

-- ============================================================
-- Part 4: PathEnv–Heap Coherence
-- ============================================================

/-- Extract the field elements from a path (dropping root_to_var elements) -/
def fieldPathOf : List PathElement → List Field
  | [] => []
  | (.field f) :: rest => f :: fieldPathOf rest
  | (.root_to_var _) :: rest => fieldPathOf rest
  | .vecElem :: rest => fieldPathOf rest
  | (.variantField _ f) :: rest => f :: fieldPathOf rest

/-- A path in PathEnv is reflected in the heap via RefMap.
    If there's a path from r1 to r2 in PathEnv, then the concrete locations
    referenced by r1 and r2 are related: r2's path extends r1's path
    by the field elements in the abstract path. -/
def PathReflectedInHeap (rmap : RefMap) (heap : Heap)
    (r1 r2 : Aref) (p : List PathElement) : Prop :=
  -- If both abstract refs map to concrete locations...
  match rmap.map r1, rmap.map r2 with
  | some (loc1, path1), some (loc2, path2) =>
    -- ...at the same heap location...
    loc1 = loc2 →
    -- ...then the concrete path of r2 extends r1's path by the field elements
    path2 = path1 ++ fieldPathOf p ∧
    -- ...and reading through r2's path succeeds
    heap.readRef loc2 path2 ≠ none
  | _, _ => True  -- If either ref is unmapped, the constraint is vacuous

-- ============================================================
-- Part 5a: FunTypeSafe (bundled safety for typed functions)
-- ============================================================

/-- A function definition is safely typed if there exists a label environment
    satisfying typecheck_fun AND all the structural properties needed to
    construct a WellTypedState for the callee upon function call. -/
def FunTypeSafe (fdef : FunDef) (runtimeFunEnv : AssocMap Id FunDef) (globalEnumEnv : EnumEnv) : Prop :=
  ∃ (lenv : LabelEnv),
    typecheck_fun fdef lenv globalEnumEnv ∧
    -- All lenv entries are well-formed
    (∀ L envL, lookup lenv L = some envL → TypeEnv.WellFormed envL) ∧
    -- All lenv entries have empty siteEnv
    (∀ L envL, lookup lenv L = some envL → ∀ s, lookup envL.siteEnv s = none) ∧
    -- Valid var refs tracked in pathEnv
    (∀ L envL, lookup lenv L = some envL →
      ∀ x bt r bk ms, lookup envL.varEnv x = some (.validVar, .ref bt r bk, ms) →
      r ∈ envL.pathEnv.refs) ∧
    -- Valid var refs are unique
    (∀ L envL, lookup lenv L = some envL →
      ∀ r x y bt bt' bk bk' ms ms', x ≠ y →
      lookup envL.varEnv x = some (.validVar, .ref bt r bk, ms) →
      lookup envL.varEnv y = some (.validVar, .ref bt' r bk', ms') → False) ∧
    -- lenv entries' funEnv matches runtime
    (∀ L envL, lookup lenv L = some envL →
      ∀ fname sig, lookup envL.funEnv fname = some sig →
      ∃ fdef', lookup runtimeFunEnv fname = some fdef' ∧
              fdef'.params.map (fun (_, τ) => τ.toParamType) = sig.params ∧
              fdef'.returnType = sig.returnType) ∧
    -- Every block has a lenv entry
    (∀ b, b ∈ fdef.blocks → ∃ envL, lookup lenv b.label = some envL) ∧
    -- Every lenv entry has a block (reverse of above)
    (∀ L envL, lookup lenv L = some envL → ∃ b, b ∈ fdef.blocks ∧ b.label = L) ∧
    -- All lenv entries share the same funEnv
    (∀ L envL L' envL',
      lookup lenv L = some envL → lookup lenv L' = some envL' →
      envL.funEnv = envL'.funEnv) ∧
    -- Path properties of lenv entries
    (∀ L envL, lookup lenv L = some envL →
      ∀ u v p, u ∉ envL.pathEnv.refs → u ≠ .root → u ≠ v →
      ¬interpret_regex (envL.pathEnv.paths (u, v)) p) ∧
    (∀ L envL, lookup lenv L = some envL →
      ∀ u v p, v ∉ envL.pathEnv.refs → v ≠ .root → u ≠ v →
      ¬interpret_regex (envL.pathEnv.paths (u, v)) p) ∧
    (∀ L envL, lookup lenv L = some envL →
      ∀ u p, interpret_regex (envL.pathEnv.paths (u, u)) p → p = []) ∧
    -- Parameter names are unique
    (fdef.params.map Prod.fst).Nodup ∧
    -- Parameter ref ids are distinct
    (fdef.params.filterMap (fun (_, τ) => match τ with
      | .ref _ r _ => some r | _ => none)).Nodup ∧
    -- No param ref is .root
    (∀ x bt r bk, (x, .ref bt r bk) ∈ fdef.params → r ≠ .root) ∧
    -- Entry block varEnv matches init_fun_varEnv exactly
    (∀ block env, fdef.blocks.head? = some block →
      lookup lenv block.label = some env →
      LookupEquiv env.varEnv (init_fun_varEnv fdef)) ∧
    -- All lenv entries have enumEnv matching the global one
    (∀ L envL, lookup lenv L = some envL → envL.enumEnv = globalEnumEnv)

-- ============================================================
-- Part 5b: Well-Typed State (Central Invariant)
-- ============================================================

/-- Two values are variant-compatible if they're not both enum variants with different names -/
def variantCompatible (v1 v2 : Value) : Prop :=
  match v1, v2 with
  | .variant name1 _ _, .variant name2 _ _ => name1 = name2
  | _, _ => True

/-- The central invariant: a running machine state is well-typed with respect to
    a type environment, label environment, return type, and reference map. -/
structure WellTypedState (m : Machine) (env : TypeEnv) (lenv : LabelEnv)
    (retTypes : List ParamType) (rmap : RefMap) : Prop where
  -- 1. TypeEnv is well-formed
  env_wf : TypeEnv.WellFormed env

  -- 1b. Machine's enumEnv matches TypeEnv's enumEnv
  enumEnv_consistent : m.enumEnv = env.enumEnv

  -- 1c. Enum definitions have no qualified field name collisions
  --     (needed for flat encoding: qualifyField produces unique keys)
  enum_qualified_nodup : ∀ ename enumDef,
    lookup env.enumEnv ename = some enumDef →
    ((allEnumFieldTypes enumDef).map Prod.fst).Nodup

  -- 1d. Enum names are unique in the enum environment
  --     (needed for defaultValue_HasType: ensures consistent lookups in sublists)
  enum_names_nodup : (env.enumEnv.entries.map Prod.fst).Nodup

  -- 1e. Variant names within each enum are unique.
  --     Required for buildFlatVariantFields_HasType: connects membership to lookup.
  enum_variant_nodup : ∀ ename (ed : EnumDef),
    env.enumEnv.lookup ename = some ed →
    (ed.variants.entries.map Prod.fst).Nodup

  -- 1f. Field names within each enum variant are unique.
  --     Required for buildFlatVariantFields_HasType: converts membership to lookup.
  enum_fields_nodup : ∀ ename (ed : EnumDef) vn (vd : EnumVariantDef),
    env.enumEnv.lookup ename = some ed →
    (vn, vd) ∈ ed.variants.entries →
    (vd.fields.entries.map Prod.fst).Nodup

  -- 1g. Default values for enum field types are well-typed.
  --     Required for packVariant: buildFlatVariantFields uses defaultValue for inactive fields.
  --     Invariant because enumEnv never changes during execution.
  defaultValues_typed : ∀ ename (ed : EnumDef) vn (vd : EnumVariantDef) f bt,
    env.enumEnv.lookup ename = some ed →
    (vn, vd) ∈ ed.variants.entries →
    (f, bt) ∈ vd.fields.entries →
    HasType env.enumEnv (defaultValue m.enumEnv.entries bt) bt

  -- 2. Current statement type-checks in the given environment
  stmt_typed : typecheck_stmt lenv env m.frame.stmt retTypes

  -- 3. Variable consistency: VarEnv tracks what VarStore has
  --    For valid vars, also tracks that the heap value matches the type via rmap
  var_consistent : ∀ x isv τ ms,
    lookup env.varEnv x = some (isv, τ, ms) →
    match isv with
    | .validVar =>
      ∃ loc v, lookup m.frame.varStore x = some (some loc) ∧
               m.heap.read loc = some v ∧ ValueMatchesType env.enumEnv v τ rmap
    | .invalidVar =>
      lookup m.frame.varStore x = some none ∨
      ∃ loc, lookup m.frame.varStore x = some (some loc)

  -- 4. Site consistency: SiteEnv tracks what SiteStore has
  site_consistent : ∀ s τ,
    lookup env.siteEnv s = some τ →
    ∃ v, lookup m.frame.siteStore s = some v ∧ ValueMatchesType env.enumEnv v τ rmap

  -- 5. Heap consistency via rmap:
  --    Every mapped abstract reference points to a valid concrete heap location
  rmap_live : ∀ r loc path,
    r ∈ env.pathEnv.refs →
    rmap.map r = some (loc, path) →
    m.heap.readRef loc path ≠ none

  -- 6. Path–heap coherence:
  --    PathEnv paths correspond to concrete field relationships in the heap
  rmap_paths : ∀ r1 r2,
    r1 ∈ env.pathEnv.refs → r2 ∈ env.pathEnv.refs →
    ∀ p, interpret_regex (env.pathEnv.paths (r1, r2)) p →
    PathReflectedInHeap rmap m.heap r1 r2 p

  -- 7. All blocks in the current frame type-check in their lenv environments
  blocks_typed : ∀ b, b ∈ m.frame.blocks → ∀ blockEnv,
    lookup lenv b.label = some blockEnv →
    typecheck_stmt lenv blockEnv b.body retTypes

  -- 9. lenv entries have empty siteEnv (sites are block-local, reset on jump)
  lenv_empty_siteEnv : ∀ L envL, lookup lenv L = some envL →
    ∀ s, lookup envL.siteEnv s = none

  -- 9b. lenv entries are well-formed (needed for weakening in preservation_jump/branch)
  lenv_wf : ∀ L envL, lookup lenv L = some envL → TypeEnv.WellFormed envL

  -- 9c. lenv entries have tracked var refs (valid var refs ∈ pathEnv.refs)
  lenv_var_tracked : ∀ L envL, lookup lenv L = some envL →
    ∀ x bt r bk ms, lookup envL.varEnv x = some (.validVar, .ref bt r bk, ms) →
    r ∈ envL.pathEnv.refs

  -- 9d. lenv entries have unique var refs (no two distinct vars share a ref)
  lenv_var_unique : ∀ L envL, lookup lenv L = some envL →
    ∀ r x y bt bt' bk bk' ms ms', x ≠ y →
    lookup envL.varEnv x = some (.validVar, .ref bt r bk, ms) →
    lookup envL.varEnv y = some (.validVar, .ref bt' r bk', ms') → False

  -- 9e. lenv entries have the same funEnv as the current env
  lenv_funEnv_eq : ∀ L envL, lookup lenv L = some envL → envL.funEnv = env.funEnv

  -- 10. All functions in funEnv are safely typed (with lenv properties)
  funEnv_typed : ∀ fname fdef,
    lookup m.frame.funEnv fname = some fdef →
    FunTypeSafe fdef m.frame.funEnv env.enumEnv

  -- 11. Heap well-formedness: all readable locations are below nextLoc.
  --     This ensures that heap.alloc produces a genuinely fresh location.
  heap_loc_bound : ∀ loc, m.heap.read loc ≠ none → loc < m.heap.nextLoc

  -- 12. Every ref in a valid varEnv entry is tracked in pathEnv.refs
  varEnv_refs_in_pathEnv : ∀ x bt r bk ms,
    lookup env.varEnv x = some (.validVar, .ref bt r bk, ms) → r ∈ env.pathEnv.refs

  -- 13. Every ref in a siteEnv entry is tracked in pathEnv.refs
  siteEnv_refs_in_pathEnv : ∀ s bt r bk,
    lookup env.siteEnv s = some (.ref bt r bk) → r ∈ env.pathEnv.refs

  -- 14. Each abstract ref appears at most once across valid varEnv and siteEnv
  live_refs_unique : ∀ r,
    (∀ x bt bk ms s bt' bk',
       lookup env.varEnv x = some (.validVar, .ref bt r bk, ms) →
       lookup env.siteEnv s = some (.ref bt' r bk') → False) ∧
    (∀ s s' bt bt' bk bk', s ≠ s' →
       lookup env.siteEnv s = some (.ref bt r bk) →
       lookup env.siteEnv s' = some (.ref bt' r bk') → False) ∧
    (∀ x y bt bt' bk bk' ms ms', x ≠ y →
       lookup env.varEnv x = some (.validVar, .ref bt r bk, ms) →
       lookup env.varEnv y = some (.validVar, .ref bt' r bk', ms') → False)

  -- 15. Root is never mapped in rmap (purely static concept)
  rmap_root_none : rmap.map .root = none

  -- 16. No paths to .root except the self-loop from .root itself
  no_paths_to_root : ∀ u p,
    interpret_regex (env.pathEnv.paths (u, .root)) p → u = .root ∧ p = []

  -- 17. Paths from .root to ref v are coherent with variable locations
  root_path_coherence : ∀ v y rest,
    v ∈ env.pathEnv.refs →
    interpret_regex (env.pathEnv.paths (.root, v)) (.root_to_var y :: rest) →
    ∀ loc_v path_v, rmap.map v = some (loc_v, path_v) →
    ∀ loc_y, lookup m.frame.varStore y = some (some loc_y) →
    loc_v = loc_y → path_v = fieldPathOf rest

  -- 18. Non-member refs (except root) have no outgoing paths to other refs
  paths_from_non_member_empty : ∀ u v p, u ∉ env.pathEnv.refs → u ≠ .root → u ≠ v →
    ¬interpret_regex (env.pathEnv.paths (u, v)) p

  -- 19. Non-member refs (except root) have no incoming paths from other refs
  paths_to_non_member_empty : ∀ u v p, v ∉ env.pathEnv.refs → v ≠ .root → u ≠ v →
    ¬interpret_regex (env.pathEnv.paths (u, v)) p

  -- 20. Self-loops only accept the empty path
  self_loop_only_empty : ∀ u p, interpret_regex (env.pathEnv.paths (u, u)) p → p = []

  -- 21. Rmap entries have matching heap types:
  --     If an abstract ref maps to (loc, path) and has basic type bt in the env,
  --     then the heap value at that location has type bt.
  rmap_has_type : ∀ r bt loc path,
    rmap.map r = some (loc, path) →
    ((∃ x bk ms, lookup env.varEnv x = some (.validVar, .ref bt r bk, ms)) ∨
     (∃ s bk, lookup env.siteEnv s = some (.ref bt r bk))) →
    ∃ v, m.heap.readRef loc path = some v ∧ HasType env.enumEnv v bt

  -- 22. FunEnv signature consistency: typing-level FunSig matches runtime FunDef
  funEnv_sig_consistent : ∀ fname sig,
    lookup env.funEnv fname = some sig →
    ∃ fdef, lookup m.frame.funEnv fname = some fdef ∧
            fdef.params.map (fun (_, τ) => τ.toParamType) = sig.params ∧
            fdef.returnType = sig.returnType

  -- 23. All tracked refs are either root or mapped by rmap
  refs_tracked_mapped : ∀ r, r ∈ env.pathEnv.refs → r = .root ∨ rmap.map r ≠ none

  -- 24. Every lenv entry has a corresponding block in the current frame
  lenv_labels_in_blocks : ∀ L envL, lookup lenv L = some envL →
    ∃ block, block ∈ m.frame.blocks ∧ block.label = L

  -- 25. Non-top-level frames have return info
  has_return_info : m.stack ≠ [] → m.frame.returnInfo.isSome

  -- 26. All varStore locations are within heap bounds
  varStore_locs_bound : ∀ y loc, lookup m.frame.varStore y = some (some loc) → loc < m.heap.nextLoc

/-- Return values are well-typed: each value matches its corresponding site type.
    For ref types, also requires heap readability (needed for rmap_live and rmap_has_type). -/
def ReturnValsWellTyped (enumEnv : EnumEnv) : List Value → List Site → SiteEnv → Heap → Prop
  | [], [], _, _ => True
  | v :: vs, s :: ss, se, heap =>
    (match lookup se s with
     | some (.basic bt) => HasType enumEnv v bt
     | some (.ref bt _ _) => ∃ loc path, v = .ref loc path ∧
         ∃ v', heap.readRef loc path = some v' ∧ HasType enumEnv v' bt
     | none => False) ∧
    ReturnValsWellTyped enumEnv vs ss se heap
  | _, _, _, _ => False

/-- Stack safety: each frame on the stack can be safely restored after ret.
    Fields are inlined from WellTypedState to allow individual heap-dependent
    field maintenance through callee execution. At ret time, these fields are
    combined with ReturnValsWellTyped via wellTypedState_extend_result_sites
    to produce a full WellTypedState.
    Defined by structural recursion on the stack. -/
def StackSafe (globalEnumEnv : EnumEnv) : List Frame → Option ReturnInfo → Heap → List ParamType → Prop
  | [], _, _, _ => True
  | _, none, _, _ => True
  | callerFrame :: rest, some ri, heap, calleeRetTypes =>
    ∃ callerEnv callerLenv callerRetTypes callerRmap,
      -- == Heap-independent fields (unchanged during callee execution) ==
      (callerEnv.enumEnv = globalEnumEnv ∧
      TypeEnv.WellFormed callerEnv ∧
      typecheck_stmt callerLenv callerEnv ri.callerStmt callerRetTypes ∧
      (∀ b, b ∈ callerFrame.blocks → ∀ blockEnv,
        lookup callerLenv b.label = some blockEnv →
        typecheck_stmt callerLenv blockEnv b.body callerRetTypes) ∧
      (∀ L envL, lookup callerLenv L = some envL → ∀ s, lookup envL.siteEnv s = none) ∧
      (∀ L envL, lookup callerLenv L = some envL → TypeEnv.WellFormed envL) ∧
      (∀ L envL, lookup callerLenv L = some envL →
        ∀ x bt r bk ms, lookup envL.varEnv x = some (.validVar, .ref bt r bk, ms) →
        r ∈ envL.pathEnv.refs) ∧
      (∀ L envL, lookup callerLenv L = some envL →
        ∀ r x y bt bt' bk bk' ms ms', x ≠ y →
        lookup envL.varEnv x = some (.validVar, .ref bt r bk, ms) →
        lookup envL.varEnv y = some (.validVar, .ref bt' r bk', ms') → False) ∧
      (∀ L envL, lookup callerLenv L = some envL → envL.funEnv = callerEnv.funEnv) ∧
      -- Every lenv entry has a block (for unknownLabel progress after ret)
      (∀ L envL, lookup callerLenv L = some envL →
        ∃ block, block ∈ callerFrame.blocks ∧ block.label = L) ∧
      -- Caller frame has return info if it's not on top (rest ≠ [])
      (rest ≠ [] → callerFrame.returnInfo.isSome) ∧
      (∀ fname fdef, lookup callerFrame.funEnv fname = some fdef →
        FunTypeSafe fdef callerFrame.funEnv callerEnv.enumEnv) ∧
      (∀ x bt r bk ms, lookup callerEnv.varEnv x = some (.validVar, .ref bt r bk, ms) →
        r ∈ callerEnv.pathEnv.refs) ∧
      (∀ s bt r bk, lookup callerEnv.siteEnv s = some (.ref bt r bk) →
        r ∈ callerEnv.pathEnv.refs) ∧
      -- live_refs_unique (3 conjuncts)
      (∀ r, (∀ x bt bk ms s bt' bk',
          lookup callerEnv.varEnv x = some (.validVar, .ref bt r bk, ms) →
          lookup callerEnv.siteEnv s = some (.ref bt' r bk') → False) ∧
        (∀ s s' bt bt' bk bk', s ≠ s' →
          lookup callerEnv.siteEnv s = some (.ref bt r bk) →
          lookup callerEnv.siteEnv s' = some (.ref bt' r bk') → False) ∧
        (∀ x y bt bt' bk bk' ms ms', x ≠ y →
          lookup callerEnv.varEnv x = some (.validVar, .ref bt r bk, ms) →
          lookup callerEnv.varEnv y = some (.validVar, .ref bt' r bk', ms') → False)) ∧
      callerRmap.map .root = none ∧
      (∀ u p, interpret_regex (callerEnv.pathEnv.paths (u, .root)) p → u = .root ∧ p = []) ∧
      -- root_path_coherence
      (∀ v y rest_pe, v ∈ callerEnv.pathEnv.refs →
        interpret_regex (callerEnv.pathEnv.paths (.root, v)) (.root_to_var y :: rest_pe) →
        ∀ loc_v path_v, callerRmap.map v = some (loc_v, path_v) →
        ∀ loc_y, lookup callerFrame.varStore y = some (some loc_y) →
        loc_v = loc_y → path_v = fieldPathOf rest_pe) ∧
      (∀ u v p, u ∉ callerEnv.pathEnv.refs → u ≠ .root → u ≠ v →
        ¬interpret_regex (callerEnv.pathEnv.paths (u, v)) p) ∧
      (∀ u v p, v ∉ callerEnv.pathEnv.refs → v ≠ .root → u ≠ v →
        ¬interpret_regex (callerEnv.pathEnv.paths (u, v)) p) ∧
      (∀ u p, interpret_regex (callerEnv.pathEnv.paths (u, u)) p → p = []) ∧
      -- Unmapped non-root refs are isolated: only self-loops, no cross-paths
      (∀ r, callerRmap.map r = none → r ≠ .root → r ∈ callerEnv.pathEnv.refs →
        ∀ u, u ≠ r → (∀ p, ¬interpret_regex (callerEnv.pathEnv.paths (u, r)) p) ∧
                       (∀ p, ¬interpret_regex (callerEnv.pathEnv.paths (r, u)) p)) ∧
      -- Result-site refs are unmapped in callerRmap (they're fresh output refs)
      (∀ s bt r bk, s ∈ ri.resultSites →
        lookup callerEnv.siteEnv s = some (.ref bt r bk) → callerRmap.map r = none) ∧
      -- refs_tracked_or_result: tracked refs are root, mapped, or result-site refs
      (∀ r, r ∈ callerEnv.pathEnv.refs → r = .root ∨ callerRmap.map r ≠ none ∨
        (∃ s bt bk, s ∈ ri.resultSites ∧ lookup callerEnv.siteEnv s = some (.ref bt r bk))) ∧

      -- == Heap-dependent fields (maintained through callee heap operations) ==
      (∀ x isv τ ms, lookup callerEnv.varEnv x = some (isv, τ, ms) →
        match isv with
        | .validVar => ∃ loc v, lookup callerFrame.varStore x = some (some loc) ∧
                       heap.read loc = some v ∧ ValueMatchesType callerEnv.enumEnv v τ callerRmap
        | .invalidVar => lookup callerFrame.varStore x = some none ∨
                        ∃ loc, lookup callerFrame.varStore x = some (some loc)) ∧
      -- site_consistent: RESTRICTED to non-result sites
      (∀ s τ, lookup callerEnv.siteEnv s = some τ → s ∉ ri.resultSites →
        ∃ v, lookup callerFrame.siteStore s = some v ∧ ValueMatchesType callerEnv.enumEnv v τ callerRmap) ∧
      (∀ r loc path, r ∈ callerEnv.pathEnv.refs → callerRmap.map r = some (loc, path) → heap.readRef loc path ≠ none) ∧
      (∀ r1 r2, r1 ∈ callerEnv.pathEnv.refs → r2 ∈ callerEnv.pathEnv.refs →
        ∀ p, interpret_regex (callerEnv.pathEnv.paths (r1, r2)) p →
        PathReflectedInHeap callerRmap heap r1 r2 p) ∧
      (∀ loc, heap.read loc ≠ none → loc < heap.nextLoc) ∧
      -- varStore_locs_bound for caller
      (∀ y loc, lookup callerFrame.varStore y = some (some loc) → loc < heap.nextLoc) ∧
      -- rmap_has_type: for refs used in varEnv OR non-result siteEnv
      (∀ r bt loc path, callerRmap.map r = some (loc, path) →
        ((∃ x bk ms, lookup callerEnv.varEnv x = some (.validVar, .ref bt r bk, ms)) ∨
         (∃ s bk, lookup callerEnv.siteEnv s = some (.ref bt r bk) ∧ s ∉ ri.resultSites)) →
        ∃ v, heap.readRef loc path = some v ∧ HasType callerEnv.enumEnv v bt) ∧
      -- funEnv_sig_consistent
      (∀ fname sig, lookup callerEnv.funEnv fname = some sig →
        ∃ fdef, lookup callerFrame.funEnv fname = some fdef ∧
                fdef.params.map (fun (_, τ) => τ.toParamType) = sig.params ∧
                fdef.returnType = sig.returnType) ∧
      -- types_conform: callee return types match caller result site types
      types_conform callerEnv.siteEnv ri.resultSites calleeRetTypes) ∧
    StackSafe globalEnumEnv rest callerFrame.returnInfo heap callerRetTypes

-- ============================================================
-- Part 6: Key Bridge Lemma (check_outbound → paths are trivial)
-- ============================================================

/-- If check_outbound succeeds with only_matches_empty ∘ simplify,
    then all outbound paths from r in the PathEnv match only [] -/
theorem check_outbound_only_empty (penv : PathEnv) (r : Aref) :
    check_outbound penv r (fun re => only_matches_empty (simplify re)) →
    ∀ r', r' ∈ penv.refs →
      ∀ p, interpret_regex (penv.paths (r, r')) p → p = [] := by
  intro hcheck r' hr' p hp
  unfold check_outbound at hcheck
  have home := hcheck r' hr'
  -- only_matches_empty (simplify (penv.paths (r, r'))) = true
  -- By simplify_preserves_semantics: interpret_regex (simplify ...) p ↔ interpret_regex ... p
  have hsimpl := (simplify_preserves_semantics (penv.paths (r, r')) p).mpr hp
  exact only_matches_empty_sound (simplify (penv.paths (r, r'))) home p hsimpl

-- ============================================================
-- Part 7: writePath/readPath interaction lemmas for writeRef preservation
-- ============================================================

/-! ## Intuition: Why writeRef preserves typing

When we execute `*dst = val` (writeRef), the heap changes: a value `v` of type `τ` is
written at `(loc, path)` through a mutable ref `r`. The typing rule garbage-collects `r`
from pathEnv and deletes both `dst` and `val` from siteEnv.

The key challenge is that OTHER refs may point into the same heap location `loc` — specifically,
ancestor refs that `r` was borrowed from. For example:

    y = &mut x           // ref r1 at (loc, [])
    z = &mut y.field      // ref r2 at (loc, [field])
    *z = val              // writeRef with r = r2, writes val at (loc, [field])

After the write, `r1` still maps to `(loc, [])` but the value at `loc` has changed.
We need `HasType` to still hold for `r1`. This works because:
- The value written (`val`) has type `τ` (the ref's content type)
- `r1`'s type is a record containing `τ` at `field`
- `writePath` replaces exactly the field with a same-typed value

The `check_outbound` precondition ensures `r` has no outgoing paths to other tracked refs
(no descendants), so writing at `r` doesn't invalidate any deeper ref's path.

The lemmas below formalize the writePath/readPath/HasType interaction needed for this reasoning. -/

/-- Helper: List.lookup at the written field returns the new value after the map used by writePath.
    Uses explicit projections to match writePath's elaborated lambda form. -/
private theorem writePath_map_lookup_eq
    (fields : List (Field × Value)) (f : Field) (newVal : Value) :
    fields.lookup f ≠ none →
    (fields.map fun x : Field × Value =>
      if x.fst = f then (x.fst, newVal) else (x.fst, x.snd)).lookup f = some newVal := by
  induction fields with
  | nil => simp [List.lookup]
  | cons hd tl ih =>
    obtain ⟨k, v⟩ := hd
    intro hne
    dsimp only [List.map, Prod.fst, Prod.snd]
    by_cases hkf : k = f
    · subst hkf; simp [List.lookup]
    · simp only [if_neg hkf, List.lookup,
                  show (f == k) = false from beq_eq_false_iff_ne.mpr (Ne.symm hkf)]
      exact ih (by simp only [List.lookup,
                    show (f == k) = false from beq_eq_false_iff_ne.mpr (Ne.symm hkf)] at hne; exact hne)

/-- Helper: List.lookup at a different field is unchanged after the map used by writePath -/
private theorem writePath_map_lookup_ne
    (fields : List (Field × Value)) (f f' : Field) (newVal : Value) :
    f' ≠ f →
    (fields.map fun x : Field × Value =>
      if x.fst = f then (x.fst, newVal) else (x.fst, x.snd)).lookup f' = fields.lookup f' := by
  intro hne
  induction fields with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨k, v⟩ := hd
    dsimp only [List.map, Prod.fst, Prod.snd]
    by_cases hkf : k = f
    · subst hkf  -- eliminates f, replaces with k; hne becomes f' ≠ k
      simp only [ite_true, List.lookup,
                  show (f' == k) = false from beq_eq_false_iff_ne.mpr hne, ih]
    · simp only [if_neg hkf, List.lookup, ih]

/-- After writePath at a path, readPath at the same path returns the written value. -/
theorem readPath_after_writePath_same (v : Value) (path : List Field) (w v' : Value) :
    writePath v path w = some v' →
    readPath v' path = some w := by
  induction path generalizing v v' with
  | nil => simp [writePath]; intro h; subst h; simp [readPath]
  | cons f rest ih =>
    intro hwrite
    cases v with
    | record fields =>
      simp only [writePath] at hwrite
      cases hf : fields.lookup f with
      | none => simp [hf] at hwrite
      | some oldFieldVal =>
        simp [hf] at hwrite
        cases hwp : writePath oldFieldVal rest w with
        | none => simp [hwp] at hwrite
        | some updatedFieldVal =>
          simp [hwp] at hwrite; subst hwrite
          simp only [readPath]
          have hlookup := writePath_map_lookup_eq fields f updatedFieldVal (by rw [hf]; simp)
          rw [hlookup]
          exact ih _ _ hwp
    | int n => simp [writePath] at hwrite
    | bool b => simp [writePath] at hwrite
    | unit => simp [writePath] at hwrite
    | ref l p => simp [writePath] at hwrite
    | vec _ _ => simp [writePath] at hwrite
    | variant tag _ fields =>
      simp only [writePath] at hwrite
      cases hf : fields.lookup f with
      | none => simp [hf] at hwrite
      | some oldFieldVal =>
        simp [hf] at hwrite
        cases hwp : writePath oldFieldVal rest w with
        | none => simp [hwp] at hwrite
        | some updatedFieldVal =>
          simp [hwp] at hwrite; subst hwrite
          simp only [readPath]
          have hlookup := writePath_map_lookup_eq fields f updatedFieldVal (by rw [hf]; simp)
          rw [hlookup]
          exact ih _ _ hwp

/-- If the first fields differ, writePath at one field preserves readPath at the other. -/
theorem writePath_preserves_readPath_ne_first
    (v : Value) (f1 f2 : Field) (rest1 rest2 : List Field) (w v' : Value) :
    f1 ≠ f2 →
    writePath v (f1 :: rest1) w = some v' →
    readPath v' (f2 :: rest2) = readPath v (f2 :: rest2) := by
  intro hne hwrite
  cases v with
  | record fields =>
    simp only [writePath] at hwrite
    cases hf : fields.lookup f1 with
    | none => simp [hf] at hwrite
    | some oldFieldVal =>
      simp [hf] at hwrite
      cases hwp : writePath oldFieldVal rest1 w with
      | none => simp [hwp] at hwrite
      | some updatedFieldVal =>
        simp [hwp] at hwrite; subst hwrite
        simp only [readPath]
        rw [writePath_map_lookup_ne fields f1 f2 updatedFieldVal (Ne.symm hne)]
  | int n => simp [writePath] at hwrite
  | bool b => simp [writePath] at hwrite
  | unit => simp [writePath] at hwrite
  | ref l p => simp [writePath] at hwrite
  | vec _ _ => simp [writePath] at hwrite
  | variant tag _ fields =>
    simp only [writePath] at hwrite
    cases hf : fields.lookup f1 with
    | none => simp [hf] at hwrite
    | some oldFieldVal =>
      simp [hf] at hwrite
      cases hwp : writePath oldFieldVal rest1 w with
      | none => simp [hwp] at hwrite
      | some updatedFieldVal =>
        simp [hwp] at hwrite; subst hwrite
        simp only [readPath]
        rw [writePath_map_lookup_ne fields f1 f2 updatedFieldVal (Ne.symm hne)]

/-- writePath preserves HasType when the new value has all types the old value had at path.
    This is the key lemma for writeRef preservation: writing a type-preserving value
    at a subpath maintains the type of the whole value. -/
theorem writePath_preserves_HasType {enumEnv : EnumEnv}
    (v : Value) (path : List Field) (w v' : Value) (bt : BasicMoveType) :
    HasType enumEnv v bt →
    writePath v path w = some v' →
    (∀ u bt_sub, readPath v path = some u → HasType enumEnv u bt_sub → HasType enumEnv w bt_sub) →
    HasType enumEnv v' bt := by
  induction path generalizing v v' bt with
  | nil =>
    simp [writePath, readPath]
    intro hht hveq hcompat; subst hveq
    exact hcompat v bt rfl hht
  | cons f rest ih =>
    intro hht hwrite hcompat
    cases v with
    | record fields =>
      -- v = .record fields, bt = .trecord fentries
      cases hht with
      | record _ fentries hdom hdom_rev htyped =>
        simp only [writePath] at hwrite
        cases hf : fields.lookup f with
        | none => simp [hf] at hwrite
        | some oldFieldVal =>
          simp [hf] at hwrite
          cases hwp : writePath oldFieldVal rest w with
          | none => simp [hwp] at hwrite
          | some updatedFieldVal =>
            simp [hwp] at hwrite; subst hwrite
            -- Need HasType (.record mapped_fields) (.trecord fentries)
            apply HasType.record
            · -- Field existence: ∀ f', fentries has f' → mapped_fields has f'
              intro f' hne_none
              by_cases hf'f : f' = f
              · subst hf'f  -- eliminates f, replaces with f'
                rw [writePath_map_lookup_eq fields f' updatedFieldVal (by rw [hf]; simp)]
                simp
              · rw [writePath_map_lookup_ne fields f f' updatedFieldVal hf'f]
                exact hdom f' hne_none
            · -- Reverse domain: mapped_fields has f' → fentries has f'
              intro f' hne_none
              by_cases hf'f : f' = f
              · subst hf'f; exact hdom_rev f' (by rw [hf]; simp)
              · rw [writePath_map_lookup_ne fields f f' updatedFieldVal hf'f] at hne_none
                exact hdom_rev f' hne_none
            · -- Field typing: ∀ f' bt' v', fentries has f' with bt' → mapped has v' → HasType v' bt'
              intro f' bt' v' hlookup hfield
              by_cases hf'f : f' = f
              · -- Writing at this field: use IH
                subst hf'f  -- eliminates f, replaces with f'
                rw [writePath_map_lookup_eq fields f' updatedFieldVal (by rw [hf]; simp)] at hfield
                simp only [Option.some.injEq] at hfield; subst hfield
                have hht_old := htyped f' bt' oldFieldVal hlookup hf
                exact ih _ _ bt' hht_old hwp
                  (by intro u bt_sub hread hht_u
                      exact hcompat u bt_sub (by simp [readPath, hf, hread]) hht_u)
              · -- Different field: unchanged
                rw [writePath_map_lookup_ne fields f f' updatedFieldVal hf'f] at hfield
                exact htyped f' bt' v' hlookup hfield
    | int n => simp [writePath] at hwrite
    | bool b => simp [writePath] at hwrite
    | unit => simp [writePath] at hwrite
    | ref l p => simp [writePath] at hwrite
    | vec _ _ => simp [writePath] at hwrite
    | variant vname _ fields =>
      cases hht with
      | variant _ _ _ fentries hlookup_v hdom hdom_rev htyped hvv =>
        simp only [writePath] at hwrite
        cases hf : fields.lookup f with
        | none => simp [hf] at hwrite
        | some oldFieldVal =>
          simp [hf] at hwrite
          cases hwp : writePath oldFieldVal rest w with
          | none => simp [hwp] at hwrite
          | some updatedFieldVal =>
            simp [hwp] at hwrite; subst hwrite
            apply HasType.variant <;> try assumption
            · intro f' hne_none
              by_cases hf'f : f' = f
              · subst hf'f
                rw [writePath_map_lookup_eq fields f' updatedFieldVal (by rw [hf]; simp)]
                simp
              · rw [writePath_map_lookup_ne fields f f' updatedFieldVal hf'f]
                exact hdom f' hne_none
            · intro f' hne_none
              by_cases hf'f : f' = f
              · subst hf'f; exact hdom_rev f' (by rw [hf]; simp)
              · rw [writePath_map_lookup_ne fields f f' updatedFieldVal hf'f] at hne_none
                exact hdom_rev f' hne_none
            · intro f' bt' v' hlookup hfield
              by_cases hf'f : f' = f
              · subst hf'f
                rw [writePath_map_lookup_eq fields f' updatedFieldVal (by rw [hf]; simp)] at hfield
                simp only [Option.some.injEq] at hfield; subst hfield
                have hht_old := htyped f' bt' oldFieldVal hlookup hf
                exact ih _ _ bt' hht_old hwp
                  (by intro u bt_sub hread hht_u
                      exact hcompat u bt_sub (by simp [readPath, hf, hread]) hht_u)
              · rw [writePath_map_lookup_ne fields f f' updatedFieldVal hf'f] at hfield
                exact htyped f' bt' v' hlookup hfield

/-- writeRef at (loc, path) with value v: after the write, readRef at (loc, path) returns v -/
theorem heap_writeRef_same_path (h : Heap) (loc : Loc) (path : List Field)
    (v : Value) (h' : Heap) :
    h.writeRef loc path v = some h' →
    h'.readRef loc path = some v := by
  intro hwrite
  simp only [Heap.writeRef, bind, Option.bind] at hwrite
  cases hbase : h.read loc with
  | none => simp [hbase] at hwrite
  | some oldVal =>
    simp [hbase] at hwrite
    cases hwp : writePath oldVal path v with
    | none => simp [hwp] at hwrite
    | some newVal =>
      simp [hwp] at hwrite; rw [← hwrite]
      simp only [Heap.readRef, bind, Option.bind, Heap.write, Heap.read, lookup_insert_same]
      exact readPath_after_writePath_same oldVal path v newVal hwp

/-- heap.writeRef preserves heap_loc_bound (since nextLoc is unchanged) -/
theorem heap_loc_bound_after_writeRef (h : Heap) (loc : Loc) (path : List Field)
    (v : Value) (h' : Heap)
    (hlb : ∀ loc', h.read loc' ≠ none → loc' < h.nextLoc)
    (hwrite : h.writeRef loc path v = some h') :
    ∀ loc', h'.read loc' ≠ none → loc' < h'.nextLoc := by
  simp only [Heap.writeRef, bind, Option.bind] at hwrite
  cases hbase : h.read loc with
  | none => simp [hbase] at hwrite
  | some oldVal =>
    simp [hbase] at hwrite
    cases hwp : writePath oldVal path v with
    | none => simp [hwp] at hwrite
    | some newVal =>
      simp [hwp] at hwrite; rw [← hwrite]
      intro loc' hne
      show loc' < h.nextLoc
      simp only [Heap.write, Heap.read] at hne
      by_cases heq : loc = loc'
      · subst heq; exact hlb loc (by rw [hbase]; simp)
      · rw [lookup_insert_ne h.store loc loc' newVal (Ne.symm heq)] at hne
        exact hlb loc' hne

/-- heap.writeRef preserves nextLoc -/
theorem writeRef_preserves_nextLoc (h : Heap) (loc : Loc) (path : List Field)
    (v : Value) (h' : Heap)
    (hwrite : h.writeRef loc path v = some h') :
    h'.nextLoc = h.nextLoc := by
  simp only [Heap.writeRef, bind, Option.bind] at hwrite
  cases hbase : h.read loc with
  | none => simp [hbase] at hwrite
  | some oldVal =>
    simp [hbase] at hwrite
    cases hwp : writePath oldVal path v with
    | none => simp [hwp] at hwrite
    | some newVal => simp [hwp] at hwrite; rw [← hwrite]; rfl

-- ============================================================
-- Part 8: writePath preserves readPath structure
-- ============================================================

/-- After writePath, readPath at any path still succeeds, provided that if the read path
    extends the write path, readPath on the new value w succeeds at the extension.
    The proof is by induction on the write path wpath. -/
theorem writePath_preserves_readPath_ne_none
    (v : Value) (wpath rpath : List Field) (w v' : Value) :
    writePath v wpath w = some v' →
    readPath v rpath ≠ none →
    (∀ suffix, wpath ++ suffix = rpath → readPath w suffix ≠ none) →
    readPath v' rpath ≠ none := by
  induction wpath generalizing v v' rpath with
  | nil =>
    intro hwrite hread hext
    simp [writePath] at hwrite; subst hwrite
    exact hext rpath (by simp)
  | cons f rest ih =>
    intro hwrite hread hext
    cases v with
    | record fields =>
      simp only [writePath] at hwrite
      cases hf : fields.lookup f with
      | none => simp [hf] at hwrite
      | some fieldVal =>
        simp [hf] at hwrite
        cases hwp : writePath fieldVal rest w with
        | none => simp [hwp] at hwrite
        | some updatedFieldVal =>
          simp [hwp] at hwrite; subst hwrite
          cases rpath with
          | nil => simp [readPath]
          | cons g rrest =>
            by_cases hfg : f = g
            · -- Same field: recurse into the updated field
              subst hfg
              simp only [readPath]
              rw [writePath_map_lookup_eq fields f updatedFieldVal (by rw [hf]; simp)]
              have hread' : readPath fieldVal rrest ≠ none := by
                simp only [readPath] at hread; rw [hf] at hread; simpa using hread
              exact ih fieldVal rrest updatedFieldVal hwp hread'
                (fun suffix hsuffix => hext suffix (by simp [List.cons_append, hsuffix]))
            · -- Different field: unchanged
              simp only [readPath]
              rw [writePath_map_lookup_ne fields f g updatedFieldVal (Ne.symm hfg)]
              exact hread
    | int n => simp [writePath] at hwrite
    | bool b => simp [writePath] at hwrite
    | unit => simp [writePath] at hwrite
    | ref l p => simp [writePath] at hwrite
    | vec _ _ => simp [writePath] at hwrite
    | variant tag _ fields =>
      simp only [writePath] at hwrite
      cases hf : fields.lookup f with
      | none => simp [hf] at hwrite
      | some fieldVal =>
        simp [hf] at hwrite
        cases hwp : writePath fieldVal rest w with
        | none => simp [hwp] at hwrite
        | some updatedFieldVal =>
          simp [hwp] at hwrite; subst hwrite
          cases rpath with
          | nil => simp [readPath]
          | cons g rrest =>
            by_cases hfg : f = g
            · subst hfg
              simp only [readPath]
              rw [writePath_map_lookup_eq fields f updatedFieldVal (by rw [hf]; simp)]
              have hread' : readPath fieldVal rrest ≠ none := by
                simp only [readPath] at hread; rw [hf] at hread; simpa using hread
              exact ih fieldVal rrest updatedFieldVal hwp hread'
                (fun suffix hsuffix => hext suffix (by simp [List.cons_append, hsuffix]))
            · simp only [readPath]
              rw [writePath_map_lookup_ne fields f g updatedFieldVal (Ne.symm hfg)]
              exact hread

/-- After heap.writeRef, readRef at the same location with any path still succeeds,
    provided readPath on the written value w succeeds for any extension. -/
theorem heap_writeRef_preserves_readRef_same_loc
    (h : Heap) (loc : Loc) (wpath rpath : List Field) (w : Value) (h' : Heap) :
    h.writeRef loc wpath w = some h' →
    h.readRef loc rpath ≠ none →
    (∀ suffix, wpath ++ suffix = rpath → readPath w suffix ≠ none) →
    h'.readRef loc rpath ≠ none := by
  intro hwrite hread hext
  simp only [Heap.writeRef, bind, Option.bind] at hwrite
  cases hbase : h.read loc with
  | none => simp [hbase] at hwrite
  | some oldVal =>
    simp [hbase] at hwrite
    cases hwp : writePath oldVal wpath w with
    | none => simp [hwp] at hwrite
    | some newVal =>
      simp [hwp] at hwrite; rw [← hwrite]
      simp only [Heap.readRef, bind, Option.bind, Heap.write, Heap.read, lookup_insert_same]
      simp only [Heap.readRef, bind, Option.bind, hbase] at hread
      exact writePath_preserves_readPath_ne_none oldVal wpath rpath w newVal hwp hread hext

-- ============================================================
-- Part 9: typeAtPath and writePath_preserves_HasType_typed
-- ============================================================

/-- Follow a field path through a BasicMoveType to find the leaf type.
    Returns none if any field is not declared in the type. -/
def typeAtPath : BasicMoveType → List Field → Option BasicMoveType
  | bt, [] => some bt
  | .trecord fentries, f :: rest =>
    match lookup fentries f with
    | some bt' => typeAtPath bt' rest
    | none => none
  | _, _ :: _ => none

/-- Value-guided typeAtPath: uses the runtime value to determine which variant is active,
    providing constructor-qualified field lookup for enum types.
    For records, produces the same result as typeAtPath.
    For enums, inspects the value's variant tag to select the right field-type map. -/
def typeAtPathV (enumEnv : EnumEnv) : Value → BasicMoveType → List Field → Option BasicMoveType
  | _, bt, [] => some bt
  | .record fields, .trecord fentries, f :: rest =>
    match fields.lookup f, lookup fentries f with
    | some v', some bt' => typeAtPathV enumEnv v' bt' rest
    | _, _ => none
  | .variant _vname _ fields, .tenum _ename, f :: rest =>
    match allEnumQualifiedFieldTypes enumEnv _ename with
    | some fentries =>
      match fields.lookup f, lookup fentries f with
      | some v', some bt' => typeAtPathV enumEnv v' bt' rest
      | _, _ => none
    | none => none
  | _, _, _ :: _ => none

/-- If HasType v bt and typeAtPath bt path = some bt_leaf, then readPath v path succeeds
    and the sub-value has type bt_leaf. -/
theorem HasType_typeAtPath {enumEnv : EnumEnv} (v : Value) (bt : BasicMoveType) (path : List Field) (bt_leaf : BasicMoveType) :
    HasType enumEnv v bt →
    typeAtPath bt path = some bt_leaf →
    ∃ u, readPath v path = some u ∧ HasType enumEnv u bt_leaf := by
  induction path generalizing v bt bt_leaf with
  | nil =>
    intro hht htap
    simp [typeAtPath] at htap; subst htap
    exact ⟨v, by simp [readPath], hht⟩
  | cons f rest ih =>
    intro hht htap
    cases v with
    | record fields =>
      cases hht with
      | record _ fentries hdom _ htyped =>
        simp only [typeAtPath] at htap
        cases hfe : (lookup fentries f) with
        | none => simp [hfe] at htap
        | some bt_f =>
          simp [hfe] at htap
          have hfl_ne := hdom f (by rw [hfe]; simp)
          cases hfl : fields.lookup f with
          | none => exact absurd hfl hfl_ne
          | some fieldVal =>
            have hht_f := htyped f bt_f fieldVal hfe hfl
            obtain ⟨u, hread, hht_u⟩ := ih fieldVal bt_f bt_leaf hht_f htap
            exact ⟨u, by simp [readPath, hfl, hread], hht_u⟩
    | int n => cases hht with
      | int => simp [typeAtPath] at htap
      | int_u8 => simp [typeAtPath] at htap
    | bool b => cases hht with | bool => simp [typeAtPath] at htap
    | unit => cases hht with | unit => simp [typeAtPath] at htap
    | ref l p => cases hht
    | vec _ _ => cases hht with | vec => simp [typeAtPath] at htap
    | variant _ _ _ =>
      -- typeAtPath (.tenum ...) (f :: rest) = none, contradicting htap
      cases hht with
      | variant _ _ _ _ _ _ _ _ _ => simp [typeAtPath] at htap

/-- Value-guided HasType_typeAtPath: if typeAtPathV v bt path = some bt_leaf,
    then readPath v path succeeds and the sub-value has type bt_leaf. -/
theorem HasType_typeAtPathV {enumEnv : EnumEnv} (v : Value) (bt : BasicMoveType) (path : List Field) (bt_leaf : BasicMoveType) :
    HasType enumEnv v bt →
    typeAtPathV enumEnv v bt path = some bt_leaf →
    ∃ u, readPath v path = some u ∧ HasType enumEnv u bt_leaf := by
  induction path generalizing v bt bt_leaf with
  | nil =>
    intro hht htap
    simp [typeAtPathV] at htap; subst htap
    exact ⟨v, by simp [readPath], hht⟩
  | cons f rest ih =>
    intro hht htap
    cases v with
    | record fields =>
      cases hht with
      | record _ fentries hdom _ htyped =>
        simp only [typeAtPathV] at htap
        cases hfl : fields.lookup f with
        | none => simp [hfl] at htap
        | some fieldVal =>
          cases hfe : (lookup fentries f) with
          | none => simp [hfl, hfe] at htap
          | some bt_f =>
            simp [hfl, hfe] at htap
            have hht_f := htyped f bt_f fieldVal hfe hfl
            obtain ⟨u, hread, hht_u⟩ := ih fieldVal bt_f bt_leaf hht_f htap
            exact ⟨u, by simp [readPath, hfl, hread], hht_u⟩
    | int n => cases hht with
      | int => simp [typeAtPathV] at htap
      | int_u8 => simp [typeAtPathV] at htap
    | bool b => cases hht with | bool => simp [typeAtPathV] at htap
    | unit => cases hht with | unit => simp [typeAtPathV] at htap
    | ref l p => cases hht
    | vec _ _ => cases hht with | vec => simp [typeAtPathV] at htap
    | variant vname _ fields =>
      cases hht with
      | variant _ _ _ fentries hlookup_var hdom hdom_rev htyped _ =>
        simp only [typeAtPathV, hlookup_var] at htap
        cases hfl : fields.lookup f with
        | none => simp [hfl] at htap
        | some fieldVal =>
          cases hfe : (lookup fentries f) with
          | none => simp [hfl, hfe] at htap
          | some bt_f =>
            simp [hfl, hfe] at htap
            have hht_f := htyped f bt_f fieldVal hfe hfl
            obtain ⟨u, hread, hht_u⟩ := ih fieldVal bt_f bt_leaf hht_f htap
            exact ⟨u, by simp [readPath, hfl, hread], hht_u⟩

/-- If typeAtPath succeeds, then typeAtPathV also succeeds with the same result.
    typeAtPath only succeeds for trecord (where typeAtPathV agrees);
    for tenum, typeAtPath returns none, so the hypothesis is vacuously false. -/
theorem typeAtPath_implies_typeAtPathV {enumEnv : EnumEnv} (v : Value) (bt : BasicMoveType) (path : List Field) (bt' : BasicMoveType) :
    HasType enumEnv v bt → typeAtPath bt path = some bt' → typeAtPathV enumEnv v bt path = some bt' := by
  induction path generalizing v bt bt' with
  | nil =>
    intro _ htap; simp [typeAtPath] at htap; subst htap; simp [typeAtPathV]
  | cons f rest ih =>
    intro hht htap
    cases v with
    | record fields =>
      cases hht with
      | record _ fentries hdom _ htyped =>
        simp only [typeAtPath] at htap
        cases hfe : (lookup fentries f) with
        | none => simp [hfe] at htap
        | some bt_f =>
          simp [hfe] at htap
          have hfl_ne := hdom f (by rw [hfe]; simp)
          cases hfl : fields.lookup f with
          | none => exact absurd hfl hfl_ne
          | some fieldVal =>
            simp [typeAtPathV, hfl, hfe]
            exact ih fieldVal bt_f bt' (htyped f bt_f fieldVal hfe hfl) htap
    | int n => cases hht with
      | int => simp [typeAtPath] at htap
      | int_u8 => simp [typeAtPath] at htap
    | bool b => cases hht with | bool => simp [typeAtPath] at htap
    | unit => cases hht with | unit => simp [typeAtPath] at htap
    | ref l p => cases hht
    | vec _ _ => cases hht with | vec => simp [typeAtPath] at htap
    | variant _ _ _ => cases hht with | variant _ _ _ _ _ _ _ _ _ => simp [typeAtPath] at htap

/-- writePath preserves HasType using typeAtPath to determine the leaf type.
    This avoids the universal quantification over bt_sub in the compat condition. -/
theorem writePath_preserves_HasType_typed {enumEnv : EnumEnv}
    (v : Value) (path : List Field) (w v' : Value) (bt bt_leaf : BasicMoveType) :
    HasType enumEnv v bt →
    writePath v path w = some v' →
    typeAtPath bt path = some bt_leaf →
    HasType enumEnv w bt_leaf →
    HasType enumEnv v' bt := by
  induction path generalizing v v' bt bt_leaf with
  | nil =>
    simp [writePath, typeAtPath]
    intro _ hveq hbt; subst hveq; subst hbt
    intro hhtw; exact hhtw
  | cons f rest ih =>
    intro hht hwrite htap hhtw
    cases v with
    | record fields =>
      cases hht with
      | record _ fentries hdom hdom_rev htyped =>
        simp only [writePath] at hwrite
        cases hfl : fields.lookup f with
        | none => simp [hfl] at hwrite
        | some fieldVal =>
          simp [hfl] at hwrite
          cases hwp : writePath fieldVal rest w with
          | none => simp [hwp] at hwrite
          | some updatedFieldVal =>
            simp [hwp] at hwrite; subst hwrite
            simp only [typeAtPath] at htap
            cases hfe : (lookup fentries f) with
            | none => simp [hfe] at htap
            | some bt_f =>
              simp [hfe] at htap
              apply HasType.record
              · -- Field existence
                intro f' hne_none
                by_cases hf'f : f' = f
                · subst hf'f
                  rw [writePath_map_lookup_eq fields f' updatedFieldVal (by rw [hfl]; simp)]
                  simp
                · rw [writePath_map_lookup_ne fields f f' updatedFieldVal hf'f]
                  exact hdom f' hne_none
              · -- Reverse domain
                intro f' hne_none
                by_cases hf'f : f' = f
                · subst hf'f; exact hdom_rev f' (by rw [hfl]; simp)
                · rw [writePath_map_lookup_ne fields f f' updatedFieldVal hf'f] at hne_none
                  exact hdom_rev f' hne_none
              · -- Field typing
                intro f' bt' val hlookup hfield
                by_cases hf'f : f' = f
                · subst hf'f
                  rw [writePath_map_lookup_eq fields f' updatedFieldVal (by rw [hfl]; simp)] at hfield
                  simp only [Option.some.injEq] at hfield; subst hfield
                  have hfentr : bt_f = bt' :=
                    Option.some.inj (hfe.symm.trans hlookup)
                  subst hfentr
                  exact ih fieldVal updatedFieldVal bt_f bt_leaf
                    (htyped f' bt_f fieldVal hfe hfl) hwp htap hhtw
                · rw [writePath_map_lookup_ne fields f f' updatedFieldVal hf'f] at hfield
                  exact htyped f' bt' val hlookup hfield
    | int n => simp [writePath] at hwrite
    | bool b => simp [writePath] at hwrite
    | unit => simp [writePath] at hwrite
    | ref l p => simp [writePath] at hwrite
    | vec _ _ => simp [writePath] at hwrite
    | variant _ _ _ =>
      cases hht with
      | variant _ _ _ _ _ _ _ _ _ => simp [typeAtPath] at htap

-- ============================================================
-- Part 10: Additional HasType lemmas for writeRef preservation
-- ============================================================

/-- HasType has no constructor for `.ref` values -/
theorem HasType_not_ref {enumEnv : EnumEnv} (loc : Loc) (path : List Field) (bt : BasicMoveType) :
    ¬HasType enumEnv (.ref loc path) bt := by
  intro h; cases h

/-- If HasType v bt and readPath v path succeeds, then typeAtPathV v bt path also succeeds.
    The value-guided version works for both records and enum variants. -/
theorem readPath_ne_none_implies_typeAtPathV {enumEnv : EnumEnv}
    (v : Value) (bt : BasicMoveType) (path : List Field) :
    HasType enumEnv v bt → readPath v path ≠ none → ∃ bt', typeAtPathV enumEnv v bt path = some bt' := by
  induction path generalizing v bt with
  | nil => intro _ _; exact ⟨bt, by simp [typeAtPathV]⟩
  | cons f rest ih =>
    intro hht hread
    cases v with
    | record fields =>
      cases hht with
      | record _ fentries hdom hdom_rev htyped =>
        simp only [readPath] at hread
        cases hfl : fields.lookup f with
        | none => simp [hfl] at hread
        | some fieldVal =>
          simp [hfl] at hread
          have hfent := hdom_rev f (by rw [hfl]; simp)
          cases hfe : lookup fentries f with
          | none => exact absurd hfe hfent
          | some bt_f =>
            have hht_f := htyped f bt_f fieldVal hfe hfl
            obtain ⟨bt', htapV⟩ := ih fieldVal bt_f hht_f hread
            exact ⟨bt', by simp [typeAtPathV, hfl, hfe, htapV]⟩
    | int n => cases hht with
      | int => simp [readPath] at hread
      | int_u8 => simp [readPath] at hread
    | bool b => cases hht with | bool => simp [readPath] at hread
    | unit => cases hht with | unit => simp [readPath] at hread
    | ref l p => cases hht
    | vec _ _ => cases hht with | vec => simp [readPath] at hread
    | variant vname _ fields =>
      cases hht with
      | variant _ _ _ fentries hlookup_var hdom hdom_rev htyped _ =>
        simp only [readPath] at hread
        cases hfl : fields.lookup f with
        | none => simp [hfl] at hread
        | some fieldVal =>
          simp [hfl] at hread
          have hfent := hdom_rev f (by rw [hfl]; simp)
          cases hfe : lookup fentries f with
          | none => exact absurd hfe hfent
          | some bt_f =>
            have hht_f := htyped f bt_f fieldVal hfe hfl
            obtain ⟨bt', htapV⟩ := ih fieldVal bt_f hht_f hread
            exact ⟨bt', by simp [typeAtPathV, hlookup_var, hfl, hfe, htapV]⟩

/-- If HasType v bt and typeAtPath bt path succeeds, then readPath v path succeeds.
    This is a corollary of HasType_typeAtPath, useful for transferring readPath accessibility
    between values of the same type when typeAtPath is known.
    Note: typeAtPath only succeeds for record types (not enums), so this excludes
    paths that go through enum types. For value-dependent paths, use HasType_typeAtPathV. -/
theorem HasType_transfer_readPath_ne_none {enumEnv : EnumEnv}
    (v2 : Value) (bt : BasicMoveType) (path : List Field) (bt' : BasicMoveType) :
    HasType enumEnv v2 bt → typeAtPath bt path = some bt' → readPath v2 path ≠ none := by
  intro hht2 htap
  obtain ⟨u, hread2, _⟩ := HasType_typeAtPath v2 bt path bt' hht2 htap
  rw [hread2]; exact Option.some_ne_none _


/-- For this simplified approach, we'll prove compatibility by structural reasoning.
    In practice, this could be strengthened with additional enum field typing invariants. -/
lemma variantCompatible_refl (v : Value) : variantCompatible v v := by
  simp only [variantCompatible]
  cases v with
  | variant name _ _ => rfl
  | _ => trivial

/-- Stronger lemma: any two values are variant-compatible unless they are different enum variants -/
lemma variantCompatible_of_not_both_different_variants (fv1 fv2 : Value) :
    ¬(∃ n1 bt1 fields1 n2 bt2 fields2, fv1 = .variant n1 bt1 fields1 ∧ fv2 = .variant n2 bt2 fields2 ∧ n1 ≠ n2) →
    variantCompatible fv1 fv2 := by
  intro h
  simp only [variantCompatible]
  cases fv1 with
  | variant n1 bt1 fields1 =>
    cases fv2 with
    | variant n2 bt2 fields2 =>
      by_contra hne
      exact h ⟨n1, bt1, fields1, n2, bt2, fields2, rfl, rfl, hne⟩
    | _ => trivial
  | _ => trivial

/-- Field values of the same type in well-typed states are variant-compatible.
    This relies on an assumption that will be satisfied by a WellTypedState invariant. -/
lemma variantCompatible_record_fields {enumEnv : EnumEnv}
    (enum_compat : ∀ (fv1 fv2 : Value) (bt : BasicMoveType), HasType enumEnv fv1 bt → HasType enumEnv fv2 bt → variantCompatible fv1 fv2)
    (fv1 fv2 : Value) (bt : BasicMoveType)
    (h1 : HasType enumEnv fv1 bt) (h2 : HasType enumEnv fv2 bt) : variantCompatible fv1 fv2 :=
  enum_compat fv1 fv2 bt h1 h2

/-- readPath transfers between two values of the same type: if v1 has type bt
    and readPath v1 path ≠ none, then for any v2 with HasType v2 bt,
    readPath v2 path ≠ none.
    Works for all types including enums (flat encoding: all variants share
    the same qualified field types via allEnumQualifiedFieldTypes). -/
theorem readPath_HasType_transfer {enumEnv : EnumEnv}
    (v1 v2 : Value) (bt : BasicMoveType) (path : List Field)
    (h1 : HasType enumEnv v1 bt) (h2 : HasType enumEnv v2 bt)
    (hread : readPath v1 path ≠ none) :
    readPath v2 path ≠ none := by
  induction path generalizing v1 v2 bt with
  | nil => simp [readPath]
  | cons f rest ih =>
    cases h1 with
    | int => simp [readPath] at hread
    | int_u8 => simp [readPath] at hread
    | bool => simp [readPath] at hread
    | unit => simp [readPath] at hread
    | vec => simp [readPath] at hread
    | record fields1 fentries hdom1 hrev1 htyped1 =>
      cases h2 with
      | record fields2 _ hdom2 hrev2 htyped2 =>
        simp only [readPath] at hread ⊢
        cases hf1 : fields1.lookup f with
        | none => simp [hf1] at hread
        | some fv1 =>
          simp only [hf1] at hread
          have hfe_ne := hrev1 f (by rw [hf1]; exact Option.some_ne_none _)
          cases hfe : lookup fentries f with
          | none => exact absurd hfe hfe_ne
          | some bt_f =>
            have hf2_ne := hdom2 f (by rw [hfe]; exact Option.some_ne_none _)
            cases hf2 : fields2.lookup f with
            | none => exact absurd hf2 hf2_ne
            | some fv2 =>
              simp only []
              exact ih fv1 fv2 bt_f (htyped1 f bt_f fv1 hfe hf1) (htyped2 f bt_f fv2 hfe hf2) hread
    | variant _ _ fields1 fentries1 hlookup1 hdom1 hrev1 htyped1 _ =>
      cases h2 with
      | variant _ _ fields2 fentries2 hlookup2 hdom2 hrev2 htyped2 _ =>
        -- Flat encoding: fentries1 = fentries2 (both from allEnumQualifiedFieldTypes ename)
        have hfe_eq : fentries1 = fentries2 := Option.some.inj (hlookup1.symm.trans hlookup2)
        subst hfe_eq
        simp only [readPath] at hread ⊢
        cases hf1 : fields1.lookup f with
        | none => simp [hf1] at hread
        | some fv1 =>
          simp only [hf1] at hread
          have hfe_ne := hrev1 f (by rw [hf1]; exact Option.some_ne_none _)
          cases hfe : lookup fentries1 f with
          | none => exact absurd hfe hfe_ne
          | some bt_f =>
            have hf2_ne := hdom2 f (by rw [hfe]; exact Option.some_ne_none _)
            cases hf2 : fields2.lookup f with
            | none => exact absurd hf2 hf2_ne
            | some fv2 =>
              exact ih fv1 fv2 bt_f (htyped1 f bt_f fv1 hfe hf1) (htyped2 f bt_f fv2 hfe hf2) hread

/-- typeAtPathV is determined by the type for values of the same type:
    if both v1 and v2 have HasType bt, then typeAtPathV v1 bt path = typeAtPathV v2 bt path.
    Dual of readPath_HasType_transfer — ensures hcompat for writePath_preserves_readPath_HasType. -/
theorem typeAtPathV_HasType_determined {enumEnv : EnumEnv}
    (v1 v2 : Value) (bt : BasicMoveType) (path : List Field)
    (h1 : HasType enumEnv v1 bt) (h2 : HasType enumEnv v2 bt) :
    typeAtPathV enumEnv v1 bt path = typeAtPathV enumEnv v2 bt path := by
  induction path generalizing v1 v2 bt with
  | nil => simp [typeAtPathV]
  | cons f rest ih =>
    cases h1 with
    | int => cases h2 with | int => simp [typeAtPathV]
    | int_u8 => cases h2 with | int_u8 => simp [typeAtPathV]
    | bool => cases h2 with | bool => simp [typeAtPathV]
    | unit => cases h2 with | unit => simp [typeAtPathV]
    | vec _ _ _ => cases h2 with | vec => simp [typeAtPathV]
    | record fields1 fentries hdom1 hrev1 htyped1 =>
      cases h2 with
      | record fields2 _ hdom2 hrev2 htyped2 =>
        simp only [typeAtPathV]
        cases hf1 : fields1.lookup f with
        | none =>
          cases hfe : lookup fentries f with
          | none =>
            cases hf2 : fields2.lookup f with
            | none => rfl
            | some fv2 =>
              have := hrev2 f (by rw [hf2]; exact Option.some_ne_none _)
              exact absurd hfe this
          | some bt_f =>
            have := hdom1 f (by rw [hfe]; exact Option.some_ne_none _)
            exact absurd hf1 this
        | some fv1 =>
          have hfe_ne := hrev1 f (by rw [hf1]; exact Option.some_ne_none _)
          cases hfe : lookup fentries f with
          | none => exact absurd hfe hfe_ne
          | some bt_f =>
            have hf2_ne := hdom2 f (by rw [hfe]; exact Option.some_ne_none _)
            cases hf2 : fields2.lookup f with
            | none => exact absurd hf2 hf2_ne
            | some fv2 =>
              simp only []
              exact ih fv1 fv2 bt_f (htyped1 f bt_f fv1 hfe hf1) (htyped2 f bt_f fv2 hfe hf2)
    | variant _ _ fields1 fentries1 hlookup1 hdom1 hrev1 htyped1 _ =>
      cases h2 with
      | variant _ _ fields2 fentries2 hlookup2 hdom2 hrev2 htyped2 _ =>
        -- Flat encoding: fentries1 = fentries2
        have hfe_eq : fentries1 = fentries2 := Option.some.inj (hlookup1.symm.trans hlookup2)
        subst hfe_eq
        simp only [typeAtPathV, hlookup1]
        cases hf1 : fields1.lookup f with
        | none =>
          cases hfe : lookup fentries1 f with
          | none =>
            cases hf2 : fields2.lookup f with
            | none => rfl
            | some fv2 =>
              have := hrev2 f (by rw [hf2]; exact Option.some_ne_none _)
              exact absurd hfe this
          | some bt_f =>
            have := hdom1 f (by rw [hfe]; exact Option.some_ne_none _)
            exact absurd hf1 this
        | some fv1 =>
          have hfe_ne := hrev1 f (by rw [hf1]; exact Option.some_ne_none _)
          cases hfe : lookup fentries1 f with
          | none => exact absurd hfe hfe_ne
          | some bt_f =>
            have hf2_ne := hdom2 f (by rw [hfe]; exact Option.some_ne_none _)
            cases hf2 : fields2.lookup f with
            | none => exact absurd hf2 hf2_ne
            | some fv2 =>
              simp
              exact ih fv1 fv2 bt_f (htyped1 f bt_f fv1 hfe hf1) (htyped2 f bt_f fv2 hfe hf2)

/-- If containsEnumEntries is false and a field looks up to bt_f, then containsEnum bt_f = false. -/
private theorem containsEnumEntries_false_lookup
    (entries : List (Field × BasicMoveType)) (f : Field) (bt_f : BasicMoveType)
    (hne : BasicMoveType.containsEnumEntries entries = false)
    (hlookup : List.lookup f entries = some bt_f) :
    bt_f.containsEnum = false := by
  induction entries with
  | nil => simp [List.lookup] at hlookup
  | cons hd tl ih =>
    obtain ⟨k, v⟩ := hd
    simp only [BasicMoveType.containsEnumEntries, Bool.or_eq_false_iff] at hne
    simp only [List.lookup] at hlookup
    cases h : (f == k) with
    | true =>
      simp [h] at hlookup; subst hlookup
      exact hne.1
    | false =>
      simp [h] at hlookup
      exact ih hne.2 hlookup

/-- HasType with containsEnum bt = false implies value is not a variant. -/
private theorem HasType_no_enum_not_variant {enumEnv : EnumEnv} {v : Value} {bt : BasicMoveType}
    (h : HasType enumEnv v bt) (hne : bt.containsEnum = false) :
    ∀ vn en fields, v ≠ .variant vn en fields := by
  cases h with
  | int => intro _ _ _ h; cases h
  | int_u8 => intro _ _ _ h; cases h
  | bool => intro _ _ _ h; cases h
  | unit => intro _ _ _ h; cases h
  | record => intro _ _ _ h; cases h
  | vec => intro _ _ _ h; cases h
  | variant _ _ _ _ _ _ _ _ _ => rw [BasicMoveType.containsEnum_tenum] at hne; cases hne

/-- readPath_HasType_transfer for non-enum types: no variantCompatible hypothesis needed. -/
theorem readPath_HasType_transfer_no_enum {enumEnv : EnumEnv}
    (v1 v2 : Value) (bt : BasicMoveType) (path : List Field)
    (hne : bt.containsEnum = false)
    (h1 : HasType enumEnv v1 bt) (h2 : HasType enumEnv v2 bt)
    (hread : readPath v1 path ≠ none) :
    readPath v2 path ≠ none := by
  induction path generalizing v1 v2 bt with
  | nil => simp [readPath]
  | cons f rest ih =>
    cases h1 with
    | int => simp [readPath] at hread
    | int_u8 => simp [readPath] at hread
    | bool => simp [readPath] at hread
    | unit => simp [readPath] at hread
    | vec => simp [readPath] at hread
    | record fields1 fentries hdom1 hrev1 htyped1 =>
      cases h2 with
      | record fields2 _ hdom2 hrev2 htyped2 =>
        simp only [readPath] at hread ⊢
        cases hf1 : fields1.lookup f with
        | none => simp [hf1] at hread
        | some fv1 =>
          simp only [hf1] at hread
          have hfe_ne := hrev1 f (by rw [hf1]; exact Option.some_ne_none _)
          cases hfe : lookup fentries f with
          | none => exact absurd hfe hfe_ne
          | some bt_f =>
            have hf2_ne := hdom2 f (by rw [hfe]; exact Option.some_ne_none _)
            cases hf2 : fields2.lookup f with
            | none => exact absurd hf2 hf2_ne
            | some fv2 =>
              simp only []
              have hne_f : bt_f.containsEnum = false :=
                containsEnumEntries_false_lookup fentries.entries f bt_f
                  (by rw [BasicMoveType.containsEnum_trecord] at hne; exact hne) (by unfold AssocMap.lookup at hfe; exact hfe)
              exact ih fv1 fv2 bt_f hne_f (htyped1 f bt_f fv1 hfe hf1) (htyped2 f bt_f fv2 hfe hf2) hread
    | variant _ _ _ _ _ _ _ _ _ => rw [BasicMoveType.containsEnum_tenum] at hne; cases hne

/-- typeAtPathV_HasType_determined for non-enum types: no variantCompatible hypothesis needed. -/
theorem typeAtPathV_HasType_determined_no_enum {enumEnv : EnumEnv}
    (v1 v2 : Value) (bt : BasicMoveType) (path : List Field)
    (hne : bt.containsEnum = false)
    (h1 : HasType enumEnv v1 bt) (h2 : HasType enumEnv v2 bt) :
    typeAtPathV enumEnv v1 bt path = typeAtPathV enumEnv v2 bt path := by
  induction path generalizing v1 v2 bt with
  | nil => simp [typeAtPathV]
  | cons f rest ih =>
    cases h1 with
    | int => cases h2 with | int => simp [typeAtPathV]
    | int_u8 => cases h2 with | int_u8 => simp [typeAtPathV]
    | bool => cases h2 with | bool => simp [typeAtPathV]
    | unit => cases h2 with | unit => simp [typeAtPathV]
    | vec _ _ _ => cases h2 with | vec => simp [typeAtPathV]
    | record fields1 fentries hdom1 hrev1 htyped1 =>
      cases h2 with
      | record fields2 _ hdom2 hrev2 htyped2 =>
        simp only [typeAtPathV]
        cases hf1 : fields1.lookup f with
        | none =>
          cases hfe : lookup fentries f with
          | none =>
            cases hf2 : fields2.lookup f with
            | none => rfl
            | some fv2 =>
              have := hrev2 f (by rw [hf2]; exact Option.some_ne_none _)
              exact absurd hfe this
          | some bt_f =>
            have := hdom1 f (by rw [hfe]; exact Option.some_ne_none _)
            exact absurd hf1 this
        | some fv1 =>
          have hfe_ne := hrev1 f (by rw [hf1]; exact Option.some_ne_none _)
          cases hfe : lookup fentries f with
          | none => exact absurd hfe hfe_ne
          | some bt_f =>
            have hf2_ne := hdom2 f (by rw [hfe]; exact Option.some_ne_none _)
            cases hf2 : fields2.lookup f with
            | none => exact absurd hf2 hf2_ne
            | some fv2 =>
              simp only []
              have hne_f : bt_f.containsEnum = false :=
                containsEnumEntries_false_lookup fentries.entries f bt_f
                  (by rw [BasicMoveType.containsEnum_trecord] at hne; exact hne) (by unfold AssocMap.lookup at hfe; exact hfe)
              exact ih fv1 fv2 bt_f hne_f (htyped1 f bt_f fv1 hfe hf1) (htyped2 f bt_f fv2 hfe hf2)
    | variant _ _ _ _ _ _ _ _ _ => rw [BasicMoveType.containsEnum_tenum] at hne; cases hne

/-- Type transfer: if v1 has both bt1 and bt2, and v2 has bt2, then v2 has bt1.
    This is the key lemma for writeRef preservation: the written value `vval`
    has the ref's content type τ, and we need to show it also has bt1 (the type
    expected by some other ref or variable sharing the same heap location).
    Proof by induction on h1 : HasType v1 bt1. -/
theorem HasType_transfer {enumEnv : EnumEnv} {v1 v2 : Value} {bt1 bt2 : BasicMoveType}
    (h1 : HasType enumEnv v1 bt1) (h2 : HasType enumEnv v1 bt2) (h3 : HasType enumEnv v2 bt2) : HasType enumEnv v2 bt1 := by
  induction h1 generalizing v2 bt2 with
  | int => cases h2 with
    | int => exact h3
    | int_u8 => cases h3 with | int_u8 => exact HasType.int _
  | int_u8 => cases h2 with
    | int => cases h3 with | int => exact HasType.int_u8 _
    | int_u8 => exact h3
  | bool => cases h2 with | bool => exact h3
  | unit => cases h2 with | unit => exact h3
  | record fields e1 hdom1 hdom_rev1 htyped1 ih =>
    cases h2 with
    | record _ e2 hdom2 hdom_rev2 htyped2 =>
      cases h3 with
      | record fields2 _ hdom3 hdom_rev3 htyped3 =>
        apply HasType.record
        · -- Forward domain: lookup e1 f ≠ none → fields2.lookup f ≠ none
          intro f hne
          exact hdom3 f (hdom_rev2 f (hdom1 f hne))
        · -- Reverse domain: fields2.lookup f ≠ none → lookup e1 f ≠ none
          intro f hne
          exact hdom_rev1 f (hdom2 f (hdom_rev3 f hne))
        · -- Field typing: lookup e1 f = some bt → fields2.lookup f = some v → HasType v bt
          intro f bt v he1_f hf2_v
          -- Get the intermediate type from e2
          have he2_ne : lookup e2 f ≠ none :=
            hdom_rev2 f (hdom1 f (by rw [he1_f]; exact Option.some_ne_none _))
          cases he2_f : lookup e2 f with
          | none => exact absurd he2_f he2_ne
          | some bt2_f =>
            -- v (from fields2) has type bt2_f
            have hv_bt2f := htyped3 f bt2_f v he2_f hf2_v
            -- Get the bridge value v1_f from fields
            have hf_ne : fields.lookup f ≠ none :=
              hdom1 f (by rw [he1_f]; exact Option.some_ne_none _)
            cases hf_v1f : fields.lookup f with
            | none => exact absurd hf_v1f hf_ne
            | some v1_f =>
              -- By IH on v1_f: HasType v1_f bt2_f → HasType v bt2_f → HasType v bt
              exact ih f bt v1_f he1_f hf_v1f (htyped2 f bt2_f v1_f he2_f hf_v1f) hv_bt2f
  | vec elems elemTy htyped_elems ih =>
    -- Value.vec carries elemTy, so cases on h2 forces bt2 = .tvec elemTy = bt1
    cases h2 with
    | vec _ _ _ => exact h3
  | variant _ _ _ _ _ _ _ _ _ =>
    -- With BasicMoveType embedded in Value.variant, HasType forces bt2 = bt1
    cases h2 with
    | variant _ _ _ _ _ _ _ _ _ => exact h3

/-- Value-guided writePath_preserves_HasType: uses typeAtPathV for constructor-qualified lookup.
    Works for both records and enum variants. -/
theorem writePath_preserves_HasType_generalV {enumEnv : EnumEnv}
    (v : Value) (path : List Field) (w v' : Value) (bt : BasicMoveType) :
    HasType enumEnv v bt →
    writePath v path w = some v' →
    (∀ bt_leaf, typeAtPathV enumEnv v bt path = some bt_leaf → HasType enumEnv w bt_leaf) →
    HasType enumEnv v' bt := by
  induction path generalizing v v' bt with
  | nil =>
    intro hht hwrite hcompat
    simp [writePath] at hwrite; subst hwrite
    exact hcompat bt (by simp [typeAtPathV])
  | cons f rest ih =>
    intro hht hwrite hcompat
    cases v with
    | record fields =>
      cases hht with
      | record _ fentries hdom hdom_rev htyped =>
        simp only [writePath] at hwrite
        cases hfl : fields.lookup f with
        | none => simp [hfl] at hwrite
        | some fieldVal =>
          simp [hfl] at hwrite
          cases hwp : writePath fieldVal rest w with
          | none => simp [hwp] at hwrite
          | some updatedFieldVal =>
            simp [hwp] at hwrite; subst hwrite
            apply HasType.record
            · intro f' hne_none
              by_cases hf'f : f' = f
              · subst hf'f
                rw [writePath_map_lookup_eq fields f' updatedFieldVal (by rw [hfl]; simp)]; simp
              · rw [writePath_map_lookup_ne fields f f' updatedFieldVal hf'f]; exact hdom f' hne_none
            · intro f' hne_none
              by_cases hf'f : f' = f
              · subst hf'f; exact hdom_rev f' (by rw [hfl]; simp)
              · rw [writePath_map_lookup_ne fields f f' updatedFieldVal hf'f] at hne_none
                exact hdom_rev f' hne_none
            · intro f' bt' val hlookup hfield
              by_cases hf'f : f' = f
              · subst hf'f
                rw [writePath_map_lookup_eq fields f' updatedFieldVal (by rw [hfl]; simp)] at hfield
                simp only [Option.some.injEq] at hfield; subst hfield
                have hfentr : typeAtPathV enumEnv (.record fields) (.trecord fentries) (f' :: rest) = typeAtPathV enumEnv fieldVal bt' rest := by
                  show (match fields.lookup f', lookup fentries f' with | some v', some bt'' => typeAtPathV enumEnv v' bt'' rest | _, _ => none) = _
                  rw [hfl, hlookup]
                exact ih fieldVal updatedFieldVal bt'
                  (htyped f' bt' fieldVal hlookup hfl) hwp
                  (fun bt_leaf htap => hcompat bt_leaf (by rw [hfentr]; exact htap))
              · rw [writePath_map_lookup_ne fields f f' updatedFieldVal hf'f] at hfield
                exact htyped f' bt' val hlookup hfield
    | int n => simp [writePath] at hwrite
    | bool b => simp [writePath] at hwrite
    | unit => simp [writePath] at hwrite
    | ref l p => simp [writePath] at hwrite
    | vec _ _ => simp [writePath] at hwrite
    | variant vname ename fields =>
      cases hht with
      | variant _ _ _ fentries hlookup_var hdom hdom_rev htyped hvv =>
        simp only [writePath] at hwrite
        cases hfl : fields.lookup f with
        | none => simp [hfl] at hwrite
        | some fieldVal =>
          simp [hfl] at hwrite
          cases hwp : writePath fieldVal rest w with
          | none => simp [hwp] at hwrite
          | some updatedFieldVal =>
            simp [hwp] at hwrite; subst hwrite
            -- Need to find field type from fentries
            have hfent := hdom_rev f (by rw [hfl]; simp)
            cases hfe : lookup fentries f with
            | none => exact absurd hfe hfent
            | some bt_f =>
              apply HasType.variant <;> try assumption
              · intro f' hne_none
                by_cases hf'f : f' = f
                · subst hf'f
                  rw [writePath_map_lookup_eq fields f' updatedFieldVal (by rw [hfl]; simp)]; simp
                · rw [writePath_map_lookup_ne fields f f' updatedFieldVal hf'f]; exact hdom f' hne_none
              · intro f' hne_none
                by_cases hf'f : f' = f
                · subst hf'f; exact hdom_rev f' (by rw [hfl]; simp)
                · rw [writePath_map_lookup_ne fields f f' updatedFieldVal hf'f] at hne_none
                  exact hdom_rev f' hne_none
              · intro f' bt' val hlookup hfield
                by_cases hf'f : f' = f
                · subst hf'f
                  rw [writePath_map_lookup_eq fields f' updatedFieldVal (by rw [hfl]; simp)] at hfield
                  simp only [Option.some.injEq] at hfield; subst hfield
                  have hbt_eq : bt_f = bt' := Option.some.inj (hfe.symm.trans hlookup)
                  subst hbt_eq
                  have hfentr : typeAtPathV enumEnv (.variant vname ename fields) (.tenum ename) (f' :: rest) = typeAtPathV enumEnv fieldVal bt_f rest := by
                    simp only [typeAtPathV, hlookup_var, hfl, hfe]
                  exact ih fieldVal updatedFieldVal bt_f
                    (htyped f' bt_f fieldVal hfe hfl) hwp
                    (fun bt_leaf htap => hcompat bt_leaf (by rw [hfentr]; exact htap))
                · rw [writePath_map_lookup_ne fields f f' updatedFieldVal hf'f] at hfield
                  exact htyped f' bt' val hlookup hfield

/-- writeRef preserves HasType for heap values at the same location,
    using the value-guided typeAtPathV condition at the write path. -/
theorem heap_writeRef_preserves_HasType_same_loc
    {enumEnv : EnumEnv}
    (heap : Heap) (loc : Loc) (wpath : List Field) (w : Value) (heap' : Heap) (bt : BasicMoveType) :
    heap.writeRef loc wpath w = some heap' →
    (∃ v, heap.read loc = some v ∧ HasType enumEnv v bt) →
    (∀ v, heap.read loc = some v → HasType enumEnv v bt →
      ∀ bt_leaf, typeAtPathV enumEnv v bt wpath = some bt_leaf → HasType enumEnv w bt_leaf) →
    ∃ v', heap'.read loc = some v' ∧ HasType enumEnv v' bt := by
  intro hwrite ⟨rootVal, hread, hht⟩ hcompat
  simp only [Heap.writeRef, bind, Option.bind] at hwrite
  rw [hread] at hwrite
  simp only at hwrite
  cases hwp : writePath rootVal wpath w with
  | none => simp [hwp] at hwrite
  | some newVal =>
    simp [hwp] at hwrite; rw [← hwrite]
    exact ⟨newVal, by simp [Heap.write, Heap.read, lookup_insert_same],
           writePath_preserves_HasType_generalV rootVal wpath w newVal bt hht hwp
             (hcompat rootVal hread hht)⟩

/-- After writePath at wpath, readPath at rpath still succeeds with a well-typed value.
    Key lemma for writeRef rmap_has_type preservation at the same heap location.
    The hcompat hypothesis ensures that root-level replacement (wpath=[]) preserves
    the value structure along rpath. For record-only paths this is automatic;
    for paths through enums, callers prove it's vacuously true (the borrow checker
    prevents field borrows coexisting with root-level mutable refs on enums). -/
theorem writePath_preserves_readPath_HasType
    {enumEnv : EnumEnv}
    (v : Value) (wpath rpath : List Field) (w newRoot wleaf vold : Value)
    (τ bt : BasicMoveType)
    (hwp : writePath v wpath w = some newRoot)
    (hread_r : readPath v rpath = some vold) (hht_r : HasType enumEnv vold bt)
    (hread_w : readPath v wpath = some wleaf) (hht_w : HasType enumEnv wleaf τ)
    (hht_new : HasType enumEnv w τ)
    (hcompat : ∀ suffix, suffix ≠ [] → typeAtPathV enumEnv w τ suffix = typeAtPathV enumEnv wleaf τ suffix) :
    ∃ vnew, readPath newRoot rpath = some vnew ∧ HasType enumEnv vnew bt := by
  induction wpath generalizing v newRoot rpath wleaf vold bt with
  | nil =>
    simp [writePath] at hwp; subst hwp
    simp [readPath] at hread_w; subst hread_w
    -- newRoot = w, wleaf = v, hht_w : HasType v τ, hht_new : HasType w τ
    cases rpath with
    | nil =>
      simp [readPath] at hread_r; subst hread_r
      exact ⟨w, rfl, HasType_transfer hht_r hht_w hht_new⟩
    | cons g grest =>
      -- Use hcompat to transfer typeAtPathV from old value to new value
      have hne : readPath v (g :: grest) ≠ none := by rw [hread_r]; exact Option.some_ne_none _
      obtain ⟨bt_at, htapV_old⟩ := readPath_ne_none_implies_typeAtPathV v τ (g :: grest) hht_w hne
      have htapV_new : typeAtPathV enumEnv w τ (g :: grest) = some bt_at := by
        rw [hcompat (g :: grest) (List.cons_ne_nil g grest)]; exact htapV_old
      obtain ⟨vnew, hread_vnew, hht_vnew⟩ := HasType_typeAtPathV w τ (g :: grest) bt_at hht_new htapV_new
      obtain ⟨vold', hread_vold', hht_vold'⟩ := HasType_typeAtPathV v τ (g :: grest) bt_at hht_w htapV_old
      rw [hread_r] at hread_vold'; simp only [Option.some.injEq] at hread_vold'; subst hread_vold'
      exact ⟨vnew, hread_vnew, HasType_transfer hht_r hht_vold' hht_vnew⟩
  | cons f wrest ih =>
    cases v with
    | record fields =>
      simp only [writePath] at hwp
      cases hf : fields.lookup f with
      | none => simp [hf] at hwp
      | some fieldVal =>
        simp [hf] at hwp
        cases hwpf : writePath fieldVal wrest w with
        | none => simp [hwpf] at hwp
        | some updatedField =>
          simp only [hwpf, Option.some.injEq] at hwp
          subst hwp
          simp only [readPath, hf] at hread_w
          cases rpath with
          | nil =>
            simp [readPath] at hread_r; subst hread_r
            refine ⟨_, rfl, ?_⟩
            have hwp_full : writePath (.record fields) (f :: wrest) w =
                some (.record (fields.map fun x => if x.1 = f then (x.1, updatedField) else x)) := by
              simp [writePath, hf, hwpf]
            exact writePath_preserves_HasType_generalV (.record fields) (f :: wrest) w _ bt hht_r hwp_full (by
              intro bt_leaf htapV
              obtain ⟨u, hru, hhu⟩ := HasType_typeAtPathV (.record fields) bt (f :: wrest) bt_leaf hht_r htapV
              simp [readPath, hf] at hru
              rw [hread_w] at hru; simp only [Option.some.injEq] at hru; subst hru
              exact HasType_transfer hhu hht_w hht_new)
          | cons g rrest =>
            simp only [readPath] at hread_r ⊢
            by_cases hfg : f = g
            · subst hfg
              simp only [hf] at hread_r
              rw [writePath_map_lookup_eq fields f updatedField (by rw [hf]; simp)]
              exact ih fieldVal rrest updatedField wleaf vold bt hwpf hread_r hht_r hread_w hht_w hcompat
            · rw [writePath_map_lookup_ne fields f g updatedField (Ne.symm hfg)]
              cases hg : fields.lookup g with
              | none => simp [hg] at hread_r
              | some gVal =>
                simp only [hg] at hread_r
                exact ⟨vold, hread_r, hht_r⟩
    | int n => simp [writePath] at hwp
    | bool b => simp [writePath] at hwp
    | unit => simp [writePath] at hwp
    | ref l p => simp [writePath] at hwp
    | vec _ _ => simp [writePath] at hwp
    | variant tag enumTy fields =>
      simp only [writePath] at hwp
      cases hf : fields.lookup f with
      | none => simp [hf] at hwp
      | some fieldVal =>
        simp [hf] at hwp
        cases hwpf : writePath fieldVal wrest w with
        | none => simp [hwpf] at hwp
        | some updatedField =>
          simp only [hwpf, Option.some.injEq] at hwp
          subst hwp
          simp only [readPath, hf] at hread_w
          cases rpath with
          | nil =>
            simp [readPath] at hread_r; subst hread_r
            refine ⟨_, rfl, ?_⟩
            exact writePath_preserves_HasType_generalV (.variant tag enumTy fields) (f :: wrest) w _ bt hht_r
              (by simp [writePath, hf, hwpf]) (by
              intro bt_leaf htapV
              obtain ⟨u, hru, hhu⟩ := HasType_typeAtPathV (.variant tag enumTy fields) bt (f :: wrest) bt_leaf hht_r htapV
              simp [readPath, hf] at hru
              rw [hread_w] at hru; simp only [Option.some.injEq] at hru; subst hru
              exact HasType_transfer hhu hht_w hht_new)
          | cons g grest =>
            simp only [readPath] at hread_r ⊢
            by_cases hfg : f = g
            · subst hfg
              simp only [hf] at hread_r
              rw [writePath_map_lookup_eq fields f updatedField (by rw [hf]; simp)]
              exact ih fieldVal grest updatedField wleaf vold bt hwpf hread_r hht_r hread_w hht_w hcompat
            · rw [writePath_map_lookup_ne fields f g updatedField (Ne.symm hfg)]
              cases hg : fields.lookup g with
              | none => simp [hg] at hread_r
              | some gVal =>
                simp only [hg] at hread_r
                exact ⟨vold, hread_r, hht_r⟩

/-- writePath_preserves_readPath_HasType when rpath is NOT an extension of wpath.
    No `hcompat` (typeAtPathV compatibility) needed because the extension case is impossible. -/
theorem writePath_preserves_readPath_HasType_no_ext
    {enumEnv : EnumEnv}
    (v : Value) (wpath rpath : List Field) (w newRoot wleaf vold : Value)
    (τ bt : BasicMoveType)
    (hwp : writePath v wpath w = some newRoot)
    (hread_r : readPath v rpath = some vold) (hht_r : HasType enumEnv vold bt)
    (hread_w : readPath v wpath = some wleaf) (hht_w : HasType enumEnv wleaf τ)
    (hht_new : HasType enumEnv w τ)
    (hno_ext : ∀ suffix, suffix ≠ [] → rpath ≠ wpath ++ suffix) :
    ∃ vnew, readPath newRoot rpath = some vnew ∧ HasType enumEnv vnew bt := by
  induction wpath generalizing v newRoot rpath wleaf vold bt with
  | nil =>
    simp [writePath] at hwp; subst hwp
    simp [readPath] at hread_w; subst hread_w
    cases rpath with
    | nil =>
      simp [readPath] at hread_r; subst hread_r
      exact ⟨w, rfl, HasType_transfer hht_r hht_w hht_new⟩
    | cons g grest =>
      -- rpath = g :: grest, wpath = []. hno_ext says rpath ≠ [] ++ (g :: grest) = (g :: grest).
      -- But rpath = g :: grest. Contradiction.
      exact absurd rfl (hno_ext (g :: grest) (List.cons_ne_nil g grest))
  | cons f wrest ih =>
    cases v with
    | record fields =>
      simp only [writePath] at hwp
      cases hf : fields.lookup f with
      | none => simp [hf] at hwp
      | some fieldVal =>
        simp [hf] at hwp
        cases hwpf : writePath fieldVal wrest w with
        | none => simp [hwpf] at hwp
        | some updatedField =>
          simp only [hwpf, Option.some.injEq] at hwp; subst hwp
          simp only [readPath, hf] at hread_w
          cases rpath with
          | nil =>
            simp [readPath] at hread_r; subst hread_r
            refine ⟨_, rfl, ?_⟩
            exact writePath_preserves_HasType_generalV (.record fields) (f :: wrest) w _ bt hht_r
              (by simp [writePath, hf, hwpf]) (by
              intro bt_leaf htapV
              obtain ⟨u, hru, hhu⟩ := HasType_typeAtPathV (.record fields) bt (f :: wrest) bt_leaf hht_r htapV
              simp [readPath, hf] at hru
              rw [hread_w] at hru; simp only [Option.some.injEq] at hru; subst hru
              exact HasType_transfer hhu hht_w hht_new)
          | cons g rrest =>
            simp only [readPath] at hread_r ⊢
            by_cases hfg : f = g
            · subst hfg
              simp only [hf] at hread_r
              rw [writePath_map_lookup_eq fields f updatedField (by rw [hf]; simp)]
              exact ih fieldVal rrest updatedField wleaf vold bt hwpf hread_r hht_r hread_w hht_w
                (fun suffix hsne heq => hno_ext suffix hsne (by simp [List.cons_append, heq]))
            · rw [writePath_map_lookup_ne fields f g updatedField (Ne.symm hfg)]
              cases hg : fields.lookup g with
              | none => simp [hg] at hread_r
              | some gVal =>
                simp only [hg] at hread_r
                exact ⟨vold, hread_r, hht_r⟩
    | int n => simp [writePath] at hwp
    | bool b => simp [writePath] at hwp
    | unit => simp [writePath] at hwp
    | ref l p => simp [writePath] at hwp
    | vec _ _ => simp [writePath] at hwp
    | variant tag enumTy fields =>
      simp only [writePath] at hwp
      cases hf : fields.lookup f with
      | none => simp [hf] at hwp
      | some fieldVal =>
        simp [hf] at hwp
        cases hwpf : writePath fieldVal wrest w with
        | none => simp [hwpf] at hwp
        | some updatedField =>
          simp only [hwpf, Option.some.injEq] at hwp; subst hwp
          simp only [readPath, hf] at hread_w
          cases rpath with
          | nil =>
            simp [readPath] at hread_r; subst hread_r
            refine ⟨_, rfl, ?_⟩
            exact writePath_preserves_HasType_generalV (.variant tag enumTy fields) (f :: wrest) w _ bt hht_r
              (by simp [writePath, hf, hwpf]) (by
              intro bt_leaf htapV
              obtain ⟨u, hru, hhu⟩ := HasType_typeAtPathV (.variant tag enumTy fields) bt (f :: wrest) bt_leaf hht_r htapV
              simp [readPath, hf] at hru
              rw [hread_w] at hru; simp only [Option.some.injEq] at hru; subst hru
              exact HasType_transfer hhu hht_w hht_new)
          | cons g grest =>
            simp only [readPath] at hread_r ⊢
            by_cases hfg : f = g
            · subst hfg
              simp only [hf] at hread_r
              rw [writePath_map_lookup_eq fields f updatedField (by rw [hf]; simp)]
              exact ih fieldVal grest updatedField wleaf vold bt hwpf hread_r hht_r hread_w hht_w
                (fun suffix hsne heq => hno_ext suffix hsne (by simp [List.cons_append, heq]))
            · rw [writePath_map_lookup_ne fields f g updatedField (Ne.symm hfg)]
              cases hg : fields.lookup g with
              | none => simp [hg] at hread_r
              | some gVal =>
                simp only [hg] at hread_r
                exact ⟨vold, hread_r, hht_r⟩

end LeanMove.Typing.TypeSoundness
