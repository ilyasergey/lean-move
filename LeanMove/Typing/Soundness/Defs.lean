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
    Split into two hypotheses to avoid nested inductive issues with ∃. -/
inductive HasType : Value → BasicMoveType → Prop where
  | int : ∀ n, HasType (.int n) .u64
  | bool : ∀ b, HasType (.bool b) .tbool
  | unit : HasType .unit .tunit
  | record : ∀ fields fentries,
      (∀ f, lookup fentries f ≠ none → fields.lookup f ≠ none) →
      (∀ f, fields.lookup f ≠ none → lookup fentries f ≠ none) →
      (∀ f bt v, lookup fentries f = some bt → fields.lookup f = some v → HasType v bt) →
      HasType (.record fields) (.trecord fentries)

/-- If a value has record type, it must be a record. -/
theorem HasType.record_fields {v : Value} {fentries : AssocMap Field BasicMoveType} :
    HasType v (.trecord fentries) → ∃ fields, v = .record fields := by
  intro h; cases h with
  | record fields _ _ _ _ => exact ⟨fields, rfl⟩

/-- readPath at a typed field succeeds and the sub-value has the field type. -/
theorem HasType.readPath_field {fields : List (Field × Value)}
    {fentries : AssocMap Field BasicMoveType} {f : Field} {bt : BasicMoveType} :
    HasType (.record fields) (.trecord fentries) →
    lookup fentries f = some bt →
    ∃ vf, readPath (.record fields) [f] = some vf ∧ HasType vf bt := by
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
def ValueMatchesType (v : Value) (τ : MoveType) (rmap : RefMap) : Prop :=
  match τ with
  | .basic bt => HasType v bt
  | .ref _bt r _bk =>
    ∃ loc path, v = .ref loc path ∧ rmap.map r = some (loc, path)

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
theorem HasType.readRef_field_ne_none {fentries : AssocMap Field BasicMoveType}
    {bt : BasicMoveType} (heap : Heap) (loc : Loc) (path : List Field) (f : Field) :
    (∃ v, heap.readRef loc path = some v ∧ HasType v (.trecord fentries)) →
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
-- Part 5: Well-Typed State (Central Invariant)
-- ============================================================

/-- The central invariant: a running machine state is well-typed with respect to
    a type environment, label environment, return type, and reference map. -/
structure WellTypedState (m : Machine) (env : TypeEnv) (lenv : LabelEnv)
    (retType : MoveType) (rmap : RefMap) : Prop where
  -- 1. TypeEnv is well-formed
  env_wf : TypeEnv.WellFormed env

  -- 2. Current statement type-checks in the given environment
  stmt_typed : typecheck_stmt lenv env m.frame.stmt retType

  -- 3. Variable consistency: VarEnv tracks what VarStore has
  --    For valid vars, also tracks that the heap value matches the type via rmap
  var_consistent : ∀ x isv τ ms,
    lookup env.varEnv x = some (isv, τ, ms) →
    match isv with
    | .validVar =>
      ∃ loc v, lookup m.frame.varStore x = some (some loc) ∧
               m.heap.read loc = some v ∧ ValueMatchesType v τ rmap
    | .invalidVar =>
      lookup m.frame.varStore x = some none ∨
      ∃ loc, lookup m.frame.varStore x = some (some loc)

  -- 4. Site consistency: SiteEnv tracks what SiteStore has
  site_consistent : ∀ s τ,
    lookup env.siteEnv s = some τ →
    ∃ v, lookup m.frame.siteStore s = some v ∧ ValueMatchesType v τ rmap

  -- 5. Heap consistency via rmap:
  --    Every mapped abstract reference points to a valid concrete heap location
  rmap_live : ∀ r loc path,
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
    typecheck_stmt lenv blockEnv b.body retType

  -- 9. lenv entries have empty siteEnv (sites are block-local, reset on jump)
  lenv_empty_siteEnv : ∀ L envL, lookup lenv L = some envL →
    ∀ s, lookup envL.siteEnv s = none

  -- 9b. lenv entries are well-formed (needed for weakening in preservation_jump/branch)
  lenv_wf : ∀ L envL, lookup lenv L = some envL → TypeEnv.WellFormed envL

  -- 10. All functions in funEnv are well-typed
  funEnv_typed : ∀ fname fdef,
    lookup m.frame.funEnv fname = some fdef →
    ∃ lenv', typecheck_fun fdef lenv'

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
    ∃ v, m.heap.readRef loc path = some v ∧ HasType v bt

/-- Stack safety: each frame on the stack can be safely restored after ret.
    Defined by structural recursion on the stack. -/
def StackSafe : List Frame → Option ReturnInfo → Heap → Prop
  | [], _, _ => True
  | _, none, _ => True
  | callerFrame :: rest, some ri, heap =>
    (∀ vals newSiteStore,
      bindReturnValues callerFrame.siteStore ri.resultSites vals = some newSiteStore →
      ∃ env' lenv' retType' rmap',
        WellTypedState
          ⟨{callerFrame with siteStore := newSiteStore, stmt := ri.callerStmt}, rest, heap⟩
          env' lenv' retType' rmap' ∧
        StackSafe rest callerFrame.returnInfo heap) ∧
    StackSafe rest callerFrame.returnInfo heap

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

/-- writePath preserves HasType when the new value has all types the old value had at path.
    This is the key lemma for writeRef preservation: writing a type-preserving value
    at a subpath maintains the type of the whole value. -/
theorem writePath_preserves_HasType
    (v : Value) (path : List Field) (w v' : Value) (bt : BasicMoveType) :
    HasType v bt →
    writePath v path w = some v' →
    (∀ u bt_sub, readPath v path = some u → HasType u bt_sub → HasType w bt_sub) →
    HasType v' bt := by
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

/-- If HasType v bt and typeAtPath bt path = some bt_leaf, then readPath v path succeeds
    and the sub-value has type bt_leaf. -/
theorem HasType_typeAtPath (v : Value) (bt : BasicMoveType) (path : List Field) (bt_leaf : BasicMoveType) :
    HasType v bt →
    typeAtPath bt path = some bt_leaf →
    ∃ u, readPath v path = some u ∧ HasType u bt_leaf := by
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
    | int n => cases hht with | int => simp [typeAtPath] at htap
    | bool b => cases hht with | bool => simp [typeAtPath] at htap
    | unit => cases hht with | unit => simp [typeAtPath] at htap
    | ref l p => cases hht

/-- writePath preserves HasType using typeAtPath to determine the leaf type.
    This avoids the universal quantification over bt_sub in the compat condition. -/
theorem writePath_preserves_HasType_typed
    (v : Value) (path : List Field) (w v' : Value) (bt bt_leaf : BasicMoveType) :
    HasType v bt →
    writePath v path w = some v' →
    typeAtPath bt path = some bt_leaf →
    HasType w bt_leaf →
    HasType v' bt := by
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

-- ============================================================
-- Part 10: Additional HasType lemmas for writeRef preservation
-- ============================================================

/-- HasType has no constructor for `.ref` values -/
theorem HasType_not_ref (loc : Loc) (path : List Field) (bt : BasicMoveType) :
    ¬HasType (.ref loc path) bt := by
  intro h; cases h

/-- If HasType v bt and readPath v path succeeds, then typeAtPath bt path also succeeds.
    This is the key bridge theorem enabled by the strengthened HasType.record
    (bidirectional domain check: value fields ↔ type fields). -/
theorem readPath_ne_none_implies_typeAtPath
    (v : Value) (bt : BasicMoveType) (path : List Field) :
    HasType v bt → readPath v path ≠ none → ∃ bt', typeAtPath bt path = some bt' := by
  induction path generalizing v bt with
  | nil => intro _ _; exact ⟨bt, by simp [typeAtPath]⟩
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
            obtain ⟨bt', htap⟩ := ih fieldVal bt_f hht_f hread
            exact ⟨bt', by simp [typeAtPath, hfe, htap]⟩
    | int n => cases hht with | int => simp [readPath] at hread
    | bool b => cases hht with | bool => simp [readPath] at hread
    | unit => cases hht with | unit => simp [readPath] at hread
    | ref l p => cases hht

/-- If two values both have HasType bt, and readPath succeeds on the first,
    then readPath also succeeds on the second (at the same path).
    This uses readPath_ne_none_implies_typeAtPath + HasType_typeAtPath. -/
theorem HasType_transfer_readPath_ne_none
    (v1 v2 : Value) (bt : BasicMoveType) (path : List Field) :
    HasType v1 bt → HasType v2 bt → readPath v1 path ≠ none → readPath v2 path ≠ none := by
  intro hht1 hht2 hread
  obtain ⟨bt', htap⟩ := readPath_ne_none_implies_typeAtPath v1 bt path hht1 hread
  obtain ⟨u, hread2, _⟩ := HasType_typeAtPath v2 bt path bt' hht2 htap
  rw [hread2]; exact Option.some_ne_none _

/-- Type transfer: if v1 has both bt1 and bt2, and v2 has bt2, then v2 has bt1.
    This is the key lemma for writeRef preservation: the written value `vval`
    has the ref's content type τ, and we need to show it also has bt1 (the type
    expected by some other ref or variable sharing the same heap location).
    Proof by induction on h1 : HasType v1 bt1. -/
theorem HasType_transfer {v1 v2 : Value} {bt1 bt2 : BasicMoveType}
    (h1 : HasType v1 bt1) (h2 : HasType v1 bt2) (h3 : HasType v2 bt2) : HasType v2 bt1 := by
  induction h1 generalizing v2 bt2 with
  | int => cases h2 with | int => exact h3
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

/-- writePath preserves HasType when the condition at the leaf is satisfied
    according to typeAtPath. When typeAtPath returns none (the path goes through
    an undeclared field), HasType is trivially preserved since the type doesn't
    track that branch. When typeAtPath returns some bt_leaf, we need HasType w bt_leaf. -/
theorem writePath_preserves_HasType_general
    (v : Value) (path : List Field) (w v' : Value) (bt : BasicMoveType) :
    HasType v bt →
    writePath v path w = some v' →
    (∀ bt_leaf, typeAtPath bt path = some bt_leaf → HasType w bt_leaf) →
    HasType v' bt := by
  induction path generalizing v v' bt with
  | nil =>
    intro hht hwrite hcompat
    simp [writePath] at hwrite; subst hwrite
    exact hcompat bt (by simp [typeAtPath])
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
                -- f' is declared in fentries: use IH
                have hfentr : typeAtPath (.trecord fentries) (f' :: rest) = typeAtPath bt' rest := by
                  show (match lookup fentries f' with | some bt'' => typeAtPath bt'' rest | none => none) = _
                  rw [hlookup]
                exact ih fieldVal updatedFieldVal bt'
                  (htyped f' bt' fieldVal hlookup hfl) hwp
                  (fun bt_leaf htap => hcompat bt_leaf (by rw [hfentr]; exact htap))
              · rw [writePath_map_lookup_ne fields f f' updatedFieldVal hf'f] at hfield
                exact htyped f' bt' val hlookup hfield
    | int n => simp [writePath] at hwrite
    | bool b => simp [writePath] at hwrite
    | unit => simp [writePath] at hwrite
    | ref l p => simp [writePath] at hwrite

/-- writeRef preserves HasType for heap values at the same location,
    given the typeAtPath condition at the write path. -/
theorem heap_writeRef_preserves_HasType_same_loc
    (heap : Heap) (loc : Loc) (wpath : List Field) (w : Value) (heap' : Heap) (bt : BasicMoveType) :
    heap.writeRef loc wpath w = some heap' →
    (∃ v, heap.read loc = some v ∧ HasType v bt) →
    (∀ bt_leaf, typeAtPath bt wpath = some bt_leaf → HasType w bt_leaf) →
    ∃ v', heap'.read loc = some v' ∧ HasType v' bt := by
  intro hwrite ⟨rootVal, hread, hht⟩ hcompat
  simp only [Heap.writeRef, bind, Option.bind] at hwrite
  rw [hread] at hwrite
  simp only at hwrite
  cases hwp : writePath rootVal wpath w with
  | none => simp [hwp] at hwrite
  | some newVal =>
    simp [hwp] at hwrite; rw [← hwrite]
    exact ⟨newVal, by simp [Heap.write, Heap.read, lookup_insert_same],
           writePath_preserves_HasType_general rootVal wpath w newVal bt hht hwp hcompat⟩

/-- After writePath at wpath, readPath at rpath still succeeds with a well-typed value.
    Key lemma for writeRef rmap_has_type preservation at the same heap location.
    By induction on wpath: nil uses HasType_transfer + typeAtPath chaining;
    cons splits on rpath (nil uses writePath_preserves_HasType_general,
    cons/same recurses via IH, cons/diff is unchanged). -/
theorem writePath_preserves_readPath_HasType
    (v : Value) (wpath rpath : List Field) (w newRoot wleaf vold : Value)
    (τ bt : BasicMoveType)
    (hwp : writePath v wpath w = some newRoot)
    (hread_r : readPath v rpath = some vold) (hht_r : HasType vold bt)
    (hread_w : readPath v wpath = some wleaf) (hht_w : HasType wleaf τ)
    (hht_new : HasType w τ) :
    ∃ vnew, readPath newRoot rpath = some vnew ∧ HasType vnew bt := by
  induction wpath generalizing v newRoot rpath wleaf vold bt with
  | nil =>
    simp [writePath] at hwp; subst hwp
    simp [readPath] at hread_w; subst hread_w
    have hne : readPath v rpath ≠ none := by rw [hread_r]; exact Option.some_ne_none _
    obtain ⟨bt', htap⟩ := readPath_ne_none_implies_typeAtPath v τ rpath hht_w hne
    obtain ⟨vnew, hread_vnew, hht_vnew⟩ := HasType_typeAtPath w τ rpath bt' hht_new htap
    obtain ⟨u, hread_u, hht_u⟩ := HasType_typeAtPath v τ rpath bt' hht_w htap
    rw [hread_r] at hread_u; simp only [Option.some.injEq] at hread_u; subst hread_u
    exact ⟨vnew, hread_vnew, HasType_transfer hht_r hht_u hht_vnew⟩
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
          subst hwp  -- eliminates newRoot
          simp only [readPath, hf] at hread_w
          cases rpath with
          | nil =>
            simp [readPath] at hread_r; subst hread_r
            refine ⟨_, rfl, ?_⟩
            have hwp_full : writePath (.record fields) (f :: wrest) w =
                some (.record (fields.map fun x => if x.1 = f then (x.1, updatedField) else x)) := by
              simp [writePath, hf, hwpf]
            exact writePath_preserves_HasType_general (.record fields) (f :: wrest) w _ bt hht_r hwp_full (by
              intro bt_leaf htap
              have hne : readPath (.record fields) (f :: wrest) ≠ none := by
                simp [readPath, hf, hread_w]
              obtain ⟨bt_w, htap_w⟩ :=
                readPath_ne_none_implies_typeAtPath (.record fields) bt (f :: wrest) hht_r hne
              rw [htap_w] at htap; simp only [Option.some.injEq] at htap; subst htap
              obtain ⟨u, hread_u, hht_u⟩ :=
                HasType_typeAtPath (.record fields) bt (f :: wrest) bt_w hht_r htap_w
              simp [readPath, hf] at hread_u
              rw [hread_w] at hread_u; simp only [Option.some.injEq] at hread_u; subst hread_u
              exact HasType_transfer hht_u hht_w hht_new)
          | cons g rrest =>
            simp only [readPath] at hread_r ⊢
            by_cases hfg : f = g
            · subst hfg
              simp only [hf] at hread_r
              rw [writePath_map_lookup_eq fields f updatedField (by rw [hf]; simp)]
              exact ih fieldVal rrest updatedField wleaf vold bt hwpf hread_r hht_r hread_w hht_w
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

end LeanMove.Typing.TypeSoundness
