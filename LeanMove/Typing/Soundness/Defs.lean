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
    For the danglingRef proof we only need structural compatibility
    (correct variant + record fields exist), not full recursive typing. -/
def HasType : Value → BasicMoveType → Prop
  | .int _, .u64 => True
  | .bool _, .tbool => True
  | .unit, .tunit => True
  | .record fields, .trecord fentries =>
      -- Every field in the type has a corresponding value field
      (∀ f, lookup fentries f ≠ none → fields.lookup f ≠ none)
  | _, _ => False

-- ============================================================
-- Part 2: Reference Map
-- ============================================================

/-- Maps abstract references (Aref) to concrete heap locations with field paths.
    This is the key bridge between the static type system and runtime state. -/
structure RefMap where
  map : Aref → Option (Loc × List Field)

/-- A value matches a MoveType, given a reference map for resolving abstract refs.
    For basic types, we use True since danglingRef safety only requires ref tracking.
    For ref types, we track the concrete location via the rmap. -/
def ValueMatchesType (v : Value) (τ : MoveType) (rmap : RefMap) : Prop :=
  match τ with
  | .basic _bt => True
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

end LeanMove.Typing.TypeSoundness
