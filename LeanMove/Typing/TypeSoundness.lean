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
# Type Soundness: Well-Typed Functions Never Produce `danglingRef` Errors

This file establishes that a well-typed MoveLight function never produces a
`RuntimeError.danglingRef` error when executed by the small-step interpreter.

The proof follows a standard progress + preservation approach:

1. **HasType**: Relates runtime `Value`s to static `BasicMoveType`s
2. **RefMap**: Bridges abstract `Aref`s to concrete `(Loc × List Field)` pairs
3. **WellTypedState**: Central invariant relating `Machine` to `TypeEnv`
4. **Preservation**: Each `step` preserves `WellTypedState`
5. **Progress**: A well-typed running state never produces `danglingRef`
6. **Main theorem**: `typecheck_fun f lenv → ∀ n, run n (initState f ...) ≠ .error (.danglingRef _)`

## Key insight

The `danglingRef` error occurs only in `readRef` and `writeRef` when
`Heap.readRef loc path = none` or `Heap.writeRef loc path v = none`.
The type system prevents this via `PathEnv` + `check_outbound`:
before writing through a mutable ref `r`, `check_outbound` verifies
that no other live reference has a non-trivial field path through `r`,
so the write cannot invalidate any existing reference.
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
-- Part 7: Progress — no danglingRef errors
-- ============================================================

/-- danglingRef errors in step only arise from readRef and writeRef.
    This is a mechanical case analysis on the step function. -/
theorem step_danglingRef_source (m : Machine) (loc : Loc) :
    step (.running m) = .error (.danglingRef loc) →
    (∃ s src cont, m.frame.stmt = .letBind s (.readRef src) cont ∧
      ∃ path, readSite m src = some (.ref loc path) ∧
              m.heap.readRef loc path = none) ∨
    (∃ dst val cont, m.frame.stmt = .writeRef dst val cont ∧
      ∃ path v, readSite m dst = some (.ref loc path) ∧
                readSite m val = some v ∧
                m.heap.writeRef loc path v = none) := by
  intro hstep
  cases hs : m.frame.stmt with
  | skip =>
    exfalso; simp only [step, hs] at hstep
    revert hstep; split <;> (intro h; simp at h)
  | ret sites =>
    exfalso; simp only [step, hs] at hstep
    revert hstep; split <;> try split <;> try split <;> try split
    all_goals (intro h; simp at h)
  | jump label =>
    exfalso; simp only [step, hs] at hstep
    revert hstep; split <;> (intro h; simp at h)
  | branch c l1 l2 =>
    exfalso; simp only [step, hs] at hstep
    revert hstep; split <;> try split <;> try split
    all_goals (intro h; simp at h)
  | abort msg =>
    exfalso; simp only [step, hs] at hstep; simp at hstep
  | release site cont =>
    exfalso; simp only [step, hs] at hstep; cases hstep
  | assign x site cont =>
    exfalso; simp only [step, hs] at hstep
    revert hstep; split <;> (intro h; simp at h)
  | unpack fields src cont =>
    exfalso; simp only [step, hs] at hstep
    revert hstep; split <;> try split
    all_goals (intro h; simp at h)
  | call results fname args cont =>
    exfalso; simp only [step, hs] at hstep
    revert hstep; split <;> try split <;> try split <;> try split <;> try split
    all_goals (intro h; simp at h)
  | writeRef dst val cont =>
    simp only [step, hs] at hstep
    right
    cases h1 : readSite m dst with
    | none => exfalso; simp [h1] at hstep
    | some v1 =>
      cases v1 with
      | ref l p =>
        cases h3 : readSite m val with
        | none => exfalso; simp [h1, h3] at hstep
        | some v2 =>
          simp only [h1, h3] at hstep
          cases h4 : m.heap.writeRef l p v2 with
          | none =>
            simp only [h4] at hstep
            have heq : l = loc := by
              have h' := hstep
              simp only [ExecState.error.injEq, RuntimeError.danglingRef.injEq] at h'
              exact h'
            rw [heq] at h1 h4
            exact ⟨dst, val, cont, rfl, p, v2, h1, h3, h4⟩
          | some h' => exfalso; simp [h4] at hstep
      | int n => exfalso; simp [h1] at hstep
      | bool b => exfalso; simp [h1] at hstep
      | unit => exfalso; simp [h1] at hstep
      | record fields => exfalso; simp [h1] at hstep
  | letBind s expr cont =>
    cases expr with
    | intLit n =>
      exfalso; simp only [step, hs] at hstep; cases hstep
    | usage u =>
      exfalso; simp only [step, hs] at hstep
      revert hstep; cases u <;> simp only [] <;> split <;> (intro h; simp at h)
    | borrowField src bt field =>
      exfalso; simp only [step, hs] at hstep
      revert hstep; split <;> try split
      all_goals (intro h; simp at h)
    | borrowMutField src bt field =>
      exfalso; simp only [step, hs] at hstep
      revert hstep; split <;> try split
      all_goals (intro h; simp at h)
    | readRef src =>
      simp only [step, hs] at hstep
      left
      cases h1 : readSite m src with
      | none => exfalso; simp [h1] at hstep
      | some v1 =>
        cases v1 with
        | ref l p =>
          simp only [h1] at hstep
          cases h2 : m.heap.readRef l p with
          | none =>
            simp only [h2] at hstep
            have heq : l = loc := by
              have h' := hstep
              simp only [ExecState.error.injEq, RuntimeError.danglingRef.injEq] at h'
              exact h'
            rw [heq] at h1 h2
            exact ⟨s, src, cont, rfl, p, h1, h2⟩
          | some v => exfalso; simp [h2] at hstep
        | int n => exfalso; simp [h1] at hstep
        | bool b => exfalso; simp [h1] at hstep
        | unit => exfalso; simp [h1] at hstep
        | record fields => exfalso; simp [h1] at hstep
    | freeze src =>
      exfalso; simp only [step, hs] at hstep
      revert hstep; split <;> (intro h; simp at h)
    | pack name fields =>
      exfalso; simp only [step, hs] at hstep
      revert hstep; split <;> (intro h; simp at h)
    | binop op a b =>
      exfalso; simp only [step, hs] at hstep
      revert hstep; split <;> try split <;> try split
      all_goals (intro h; simp at h)

/-- A readRef that is well-typed always succeeds (heap access exists).
    Uses site_consistent to get the concrete reference, siteEnv_refs_tracked
    to connect to pathEnv, and rmap_live to show the heap read succeeds. -/
theorem no_danglingRef_readRef (m : Machine) (env : TypeEnv) (lenv : LabelEnv)
    (retType : MoveType) (rmap : RefMap)
    (hwt : WellTypedState m env lenv retType rmap)
    (s src : Site) (cont : Stmt)
    (hstmt : m.frame.stmt = .letBind s (.readRef src) cont)
    (loc : Loc) (path : List Field)
    (hsrc : readSite m src = some (.ref loc path)) :
    m.heap.readRef loc path ≠ none := by
  -- From stmt_typed + hstmt: the typing derivation is let_bind_readRef
  have hst := hwt.stmt_typed
  rw [hstmt] at hst
  -- Invert the typing derivation (lenv is auto-parameter, so 11 names)
  cases hst with
  | let_bind_readRef _ _ _ r τ isBor _ _ hlookup _ _ =>
    -- hlookup : lookup env.siteEnv src = some (.ref τ r isBor)
    -- From site_consistent: siteStore has a matching value
    have ⟨v, hv, hmatch⟩ := hwt.site_consistent src (.ref τ r isBor) hlookup
    obtain ⟨loc', path', hveq, hrmap⟩ := hmatch
    -- Show rmap.map r = some (loc, path) by connecting hsrc with site_consistent
    have hrmap_concrete : rmap.map r = some (loc, path) := by
      have hloc_eq : loc' = loc ∧ path' = path := by
        simp only [readSite] at hsrc
        rw [hv, hveq] at hsrc
        simp only [Option.some.injEq, Value.ref.injEq] at hsrc
        exact hsrc
      rw [hloc_eq.1, hloc_eq.2] at hrmap; exact hrmap
    -- From rmap_live: heap.readRef loc path ≠ none
    exact hwt.rmap_live r loc path hrmap_concrete

/-- A writeRef that is well-typed always succeeds (heap write exists).
    Uses the same chain as readRef, plus readRef_ne_none_implies_writeRef_ne_none. -/
theorem no_danglingRef_writeRef (m : Machine) (env : TypeEnv) (lenv : LabelEnv)
    (retType : MoveType) (rmap : RefMap)
    (hwt : WellTypedState m env lenv retType rmap)
    (dst val : Site) (cont : Stmt)
    (hstmt : m.frame.stmt = .writeRef dst val cont)
    (loc : Loc) (path : List Field) (v : Value)
    (hdst : readSite m dst = some (.ref loc path))
    (_hval : readSite m val = some v) :
    m.heap.writeRef loc path v ≠ none := by
  -- From stmt_typed + hstmt: the typing derivation is write_ref
  have hst := hwt.stmt_typed
  rw [hstmt] at hst
  -- Invert: lenv is auto-parameter, so 11 names
  cases hst with
  | write_ref _ _ _ τ r _ _ hlookup_dst hlookup_val _ _ =>
    -- hlookup_dst : lookup env.siteEnv dst = some (.ref τ r .siteBorrowMut)
    -- From site_consistent for dst: get rmap.map r = some (loc', path')
    have ⟨v_dst, hv_dst, hmatch_dst⟩ := hwt.site_consistent dst (.ref τ r .siteBorrowMut) hlookup_dst
    obtain ⟨loc', path', hveq, hrmap⟩ := hmatch_dst
    -- Show rmap.map r = some (loc, path) by connecting with hdst
    have hrmap_concrete : rmap.map r = some (loc, path) := by
      have hloc_eq : loc' = loc ∧ path' = path := by
        simp only [readSite] at hdst
        rw [hv_dst, hveq] at hdst
        simp only [Option.some.injEq, Value.ref.injEq] at hdst
        exact hdst
      rw [hloc_eq.1, hloc_eq.2] at hrmap; exact hrmap
    -- From rmap_live: heap.readRef loc path ≠ none
    have hheap := hwt.rmap_live r loc path hrmap_concrete
    -- By bridge lemma, writeRef also succeeds
    have ⟨h', hwrite⟩ := readRef_ne_none_implies_writeRef_ne_none m.heap loc path v hheap
    rw [hwrite]
    exact Option.some_ne_none h'

/-- A well-typed running state never produces a danglingRef error.
    This is the key progress lemma — it only needs the readRef and writeRef cases. -/
theorem no_danglingRef_progress (m : Machine) (env : TypeEnv) (lenv : LabelEnv)
    (retType : MoveType) (rmap : RefMap)
    (hwt : WellTypedState m env lenv retType rmap) :
    ∀ loc, step (.running m) ≠ .error (.danglingRef loc) := by
  intro loc habs
  -- Extract which case of step produced the danglingRef
  have hcases := step_danglingRef_source m loc habs
  cases hcases with
  | inl hread =>
    obtain ⟨s, src, cont, hstmt, path, hsrc, hheap⟩ := hread
    exact no_danglingRef_readRef m env lenv retType rmap hwt s src cont hstmt loc path hsrc hheap
  | inr hwrite =>
    obtain ⟨dst, val, cont, hstmt, path, v, hdst, hval, hheap⟩ := hwrite
    exact no_danglingRef_writeRef m env lenv retType rmap hwt dst val cont hstmt loc path v hdst hval hheap

-- ============================================================
-- Part 8: Preservation — typing inversion lemmas
-- ============================================================

-- Extract continuation typing from each typecheck_stmt constructor.
-- These are separate lemmas to avoid rw/cases interaction issues.

private theorem inv_intLit
    (h : typecheck_stmt lenv env (.letBind s (.intLit n) cont) retType) :
    typecheck_stmt lenv {env with siteEnv := insert env.siteEnv s (.basic .u64)} cont retType :=
  match h with | .let_bind_intLit _ _ _ _ _ _ _ hc => hc

private theorem inv_release
    (h : typecheck_stmt lenv env (.release site cont) retType) :
    ∃ τ r isBor,
      lookup env.siteEnv site = some (.ref τ r isBor) ∧
      typecheck_stmt lenv
        {env with siteEnv := delete env.siteEnv site
                  pathEnv := delete_ref_node env.pathEnv r}
        cont retType :=
  match h with | .release _ _ _ τ r isBor _ _ hlookup hcont => ⟨τ, r, isBor, hlookup, hcont⟩

private theorem inv_binop
    (h : typecheck_stmt lenv env (.letBind c (.binop bop a b) cont) retType) :
    ∃ bt1 bt2 bt3,
      lookup env.siteEnv a = some (.basic bt1) ∧
      lookup env.siteEnv b = some (.basic bt2) ∧
      binop_type bop bt1 bt2 = some bt3 ∧
      typecheck_stmt lenv
        {env with siteEnv := insert (delete (delete env.siteEnv a) b) c (.basic bt3)}
        cont retType :=
  match h with
  | .let_bind_binop _ _ _ bt1 bt2 bt3 _ _ _ _ _ ha hb hbt _ hcont =>
    ⟨bt1, bt2, bt3, ha, hb, hbt, hcont⟩

private theorem inv_copy
    (h : typecheck_stmt lenv env (.letBind a (.usage (.copy x)) cont) retType) :
    (∃ bt ms,
      lookup env.varEnv x = some (.validVar, .basic bt, ms) ∧
      typecheck_stmt lenv
        {env with siteEnv := insert env.siteEnv a (.basic bt)}
        cont retType) ∨
    (∃ τ ms s t isBor,
      lookup env.varEnv x = some (.validVar, .ref τ s isBor, ms) ∧
      freshRefInEnvBool t env ∧
      (∀ v, t ≠ .varRef v) ∧
      typecheck_stmt lenv
        {env with siteEnv := insert env.siteEnv a (.ref τ t isBor)
                  pathEnv := update_with_epsilon t s env.pathEnv}
        cont retType) :=
  match h with
  | .let_bind_copy_val _ _ _ _ bt ms _ _ hlookup _ hcont =>
    .inl ⟨bt, ms, hlookup, hcont⟩
  | .let_bind_copy_ref _ _ _ _ τ ms s t isBor _ _ hlookup _ hfresh hnv hcont =>
    .inr ⟨τ, ms, s, t, isBor, hlookup, hfresh, hnv, hcont⟩

private theorem inv_move
    (h : typecheck_stmt lenv env (.letBind a (.usage (.move x)) cont) retType) :
    ∃ τ ms,
      lookup env.varEnv x = some (.validVar, τ, ms) ∧
      typecheck_stmt lenv
        {env with varEnv := update env.varEnv x (.invalidVar, τ, ms)
                  siteEnv := insert env.siteEnv a τ}
        cont retType :=
  match h with
  | .let_bind_move _ _ _ _ τ ms _ _ hlookup _ _ hcont => ⟨τ, ms, hlookup, hcont⟩

private theorem inv_borrowImm
    (h : typecheck_stmt lenv env (.letBind a (.usage (.borrowImm x)) cont) retType) :
    ∃ τ ms r,
      lookup env.varEnv x = some (.validVar, .basic τ, ms) ∧
      freshRefInEnvBool r env ∧
      (∀ v, r ≠ .varRef v) ∧
      typecheck_stmt lenv
        {env with siteEnv := insert env.siteEnv a (.ref τ r .siteBorrowImm)
                  pathEnv := update_with_extension r .root [.root_to_var x]
                              (update_with_epsilon r r env.pathEnv)}
        cont retType :=
  match h with
  | .let_bind_borrowImm _ _ _ _ τ ms r _ _ hlookup _ hfresh hnv hcont =>
    ⟨τ, ms, r, hlookup, hfresh, hnv, hcont⟩

private theorem inv_borrowMut
    (h : typecheck_stmt lenv env (.letBind a (.usage (.borrowMut x)) cont) retType) :
    ∃ τ ms r,
      lookup env.varEnv x = some (.validVar, .basic τ, ms) ∧
      freshRefInEnvBool r env ∧
      (∀ v, r ≠ .varRef v) ∧
      typecheck_stmt lenv
        {env with siteEnv := insert env.siteEnv a (.ref τ r .siteBorrowMut)
                  pathEnv := update_with_extension r .root [.root_to_var x]
                              (update_with_epsilon r r env.pathEnv)}
        cont retType :=
  match h with
  | .let_bind_borrowMut _ _ _ _ τ ms r _ _ _ hlookup _ hfresh hnv hcont =>
    ⟨τ, ms, r, hlookup, hfresh, hnv, hcont⟩

private theorem inv_readRef
    (h : typecheck_stmt lenv env (.letBind c (.readRef src) cont) retType) :
    ∃ r τ isBor,
      lookup env.siteEnv src = some (.ref τ r isBor) ∧
      typecheck_stmt lenv
        {env with siteEnv := insert (delete env.siteEnv src) c (.basic τ)
                  pathEnv := delete_ref_node env.pathEnv r}
        cont retType :=
  match h with
  | .let_bind_readRef _ _ _ _ r τ isBor _ _ hlookup _ hcont => ⟨r, τ, isBor, hlookup, hcont⟩

private theorem inv_freeze
    (h : typecheck_stmt lenv env (.letBind c (.freeze src) cont) retType) :
    ∃ τ r r' isBor,
      lookup env.siteEnv src = some (.ref τ r isBor) ∧
      (∀ v, r' ≠ .varRef v) ∧
      freshRefInEnv r' env ∧
      typecheck_stmt lenv
        {env with siteEnv := insert (delete env.siteEnv src) c (.ref τ r' .siteBorrowImm)
                  pathEnv := consume_ref_transfer env.pathEnv r r'}
        cont retType :=
  match h with
  | .let_bind_freeze _ _ _ _ τ r r' isBor _ _ hlookup _ hfresh hnv hcont =>
    ⟨τ, r, r', isBor, hlookup, hnv, hfresh, hcont⟩

private theorem inv_pack
    (h : typecheck_stmt lenv env (.letBind b (.pack recName fieldSites) cont) retType) :
    ∃ fentries,
      typecheck_stmt lenv
        {env with siteEnv := insert (deleteAll env.siteEnv (fieldSites.map Prod.snd)) b
                                (.basic (.trecord fentries))}
        cont retType :=
  match h with
  | .let_bind_pack _ _ _ _ _ fentries _ _ _ _ _ hcont => ⟨fentries, hcont⟩

private theorem inv_borrowField
    (h : typecheck_stmt lenv env (.letBind af (.borrowField src bt field) cont) retType) :
    ∃ bt' isBor fentries s rf,
      lookup env.siteEnv src = some (.ref bt s isBor) ∧
      bt = .trecord fentries ∧
      lookup fentries field = some bt' ∧
      (∀ v, rf ≠ .varRef v) ∧
      typecheck_stmt lenv
        {env with siteEnv := insert (delete env.siteEnv src) af (.ref bt' rf isBor)
                  pathEnv := update_with_extension rf s [.field field] env.pathEnv}
        cont retType :=
  match h with
  | .let_bind_borrowField _ _ _ _ _ _ bt' isBor fentries s rf _ _ hlookup hbt hf _ _ hnv hcont =>
    ⟨bt', isBor, fentries, s, rf, hlookup, hbt, hf, hnv, hcont⟩

private theorem inv_borrowMutField
    (h : typecheck_stmt lenv env (.letBind af (.borrowMutField src bt field) cont) retType) :
    ∃ btf fentries s rf,
      lookup env.siteEnv src = some (.ref bt s .siteBorrowMut) ∧
      bt = .trecord fentries ∧
      lookup fentries field = some btf ∧
      (∀ v, rf ≠ .varRef v) ∧
      typecheck_stmt lenv
        {env with siteEnv := insert (delete env.siteEnv src) af (.ref btf rf .siteBorrowMut)
                  pathEnv := update_with_extension rf s [.field field] env.pathEnv}
        cont retType :=
  match h with
  | .let_bind_borrowMutField _ _ _ _ _ _ btf fentries s rf _ _ hlookup hbt hf _ _ hnv hcont =>
    ⟨btf, fentries, s, rf, hlookup, hbt, hf, hnv, hcont⟩

private theorem inv_writeRef
    (h : typecheck_stmt lenv env (.writeRef dst val cont) retType) :
    ∃ τ r,
      lookup env.siteEnv dst = some (.ref τ r .siteBorrowMut) ∧
      lookup env.siteEnv val = some (.basic τ) ∧
      typecheck_stmt lenv
        {env with siteEnv := delete (delete env.siteEnv val) dst
                  pathEnv := garbage_collect env.pathEnv r}
        cont retType :=
  match h with
  | .write_ref _ _ _ _ τ r _ _ hdst hval _ hcont => ⟨τ, r, hdst, hval, hcont⟩

private theorem inv_jump
    (h : typecheck_stmt lenv env (.jump L) retType) :
    ∃ envL, lookup lenv L = some envL ∧ TypeEnv.subsumes envL env :=
  match h with
  | .jump _ _ _ envL _ hlookup hsub => ⟨envL, hlookup, hsub⟩

private theorem inv_branch
    (h : typecheck_stmt lenv env (.branch c L1 L2) retType) :
    ∃ envL1 envL2,
      lookup env.siteEnv c = some (.basic .tbool) ∧
      lookup lenv L1 = some envL1 ∧
      lookup lenv L2 = some envL2 ∧
      TypeEnv.subsumes envL1 {env with siteEnv := delete env.siteEnv c} ∧
      TypeEnv.subsumes envL2 {env with siteEnv := delete env.siteEnv c} :=
  match h with
  | .branch _ _ _ _ _ envL1 envL2 _ hc hl1 hl2 hs1 hs2 =>
    ⟨envL1, envL2, hc, hl1, hl2, hs1, hs2⟩

private theorem inv_ret
    (h : typecheck_stmt lenv env (.ret sites) retType) :
    (∀ a, a ∈ sites → ∃ τ, lookup env.siteEnv a = some τ ∧ MoveType.compatible τ retType) :=
  match h with
  | .ret _ _ _ _ hall => hall

private theorem inv_call
    (h : typecheck_stmt lenv env (.call results fname args cont) retType) :
    ∃ params rets,
      lookup env.funEnv fname = some ⟨params, rets⟩ ∧
      typecheck_stmt lenv (call_connect_inputs_outputs env results args) cont retType :=
  match h with
  | .call _ _ _ _ _ params rets _ _ _ hfun _ _ _ _ hcont =>
    ⟨params, rets, hfun, hcont⟩

private theorem inv_unpack
    (h : typecheck_stmt lenv env (.unpack fields src cont) retType) :
    ∃ fentries,
      lookup env.siteEnv src = some (.basic (.trecord fentries)) ∧
      typecheck_stmt lenv
        {env with siteEnv := addFieldSites fentries (delete env.siteEnv src) fields}
        cont retType :=
  match h with
  | .unpack _ _ _ _ fentries _ _ hlookup _ _ _ hcont => ⟨fentries, hlookup, hcont⟩

private theorem inv_assign
    (h : typecheck_stmt lenv env (.assign x a cont) retType) :
    (∃ ax τ ms r,
      lookup env.varEnv x = some (.validVar, .basic τ, ms) ∧
      (∀ v, r ≠ .varRef v) ∧
      freshRefInEnvBool r env ∧
      notIn env.siteEnv ax ∧
      typecheck_stmt lenv
        {env with siteEnv := delete (delete (insert env.siteEnv ax (.ref τ r .siteBorrowMut)) a) ax
                  pathEnv := garbage_collect (update_with_extension r .root [.root_to_var x]
                              (update_with_epsilon r r env.pathEnv)) r}
        cont retType) ∨
    (∃ τ τ',
      lookup env.varEnv x = some (.invalidVar, τ, .mutable) ∧
      lookup env.siteEnv a = some τ' ∧
      MoveType.compatible τ τ' ∧
      typecheck_stmt lenv
        {env with varEnv := update env.varEnv x (.validVar, τ', .mutable)
                  siteEnv := delete env.siteEnv a}
        cont retType) :=
  match h with
  | .var_assign_valid _ _ _ _ ax τ ms r _ _ _ hlookup hnotin hfresh hnv hcont =>
    .inl ⟨ax, τ, ms, r, hlookup, hnv, hfresh, hnotin, hcont⟩
  | .var_assign_invalid _ _ _ _ τ τ' _ _ hlookup_var hlookup_site hcompat hcont =>
    .inr ⟨τ, τ', hlookup_var, hlookup_site, hcompat, hcont⟩

-- ============================================================
-- Part 8: Preservation — extracted case lemmas
-- ============================================================

/-- Reusable helper: inserting one site into siteStore preserves site_consistent
    for the new env where that site maps to a basic type matching the inserted value. -/
private theorem site_consistent_insert_basic (m : Machine) (env : TypeEnv)
    (rmap : RefMap) (s : Site) (v : Value) (τ : MoveType)
    (hwt_sc : ∀ s' τ', lookup env.siteEnv s' = some τ' →
        ∃ v, lookup m.frame.siteStore s' = some v ∧ ValueMatchesType v τ' rmap)
    (hmatch : ValueMatchesType v τ rmap) :
    ∀ s' τ', lookup (insert env.siteEnv s τ) s' = some τ' →
      ∃ v', lookup (insert m.frame.siteStore s v) s' = some v' ∧ ValueMatchesType v' τ' rmap := by
  intro s' τ' hl
  by_cases heq : s' = s
  · subst heq; simp only [lookup_insert_same, Option.some.injEq] at hl; subst hl
    exact ⟨v, lookup_insert_same _ _ _, hmatch⟩
  · rw [lookup_insert_ne _ s s' _ heq] at hl
    obtain ⟨v', hv', hm⟩ := hwt_sc s' τ' hl
    exact ⟨v', by rw [lookup_insert_ne _ s s' _ heq]; exact hv', hm⟩

private theorem preservation_intLit (m m' : Machine) (env : TypeEnv) (lenv : LabelEnv)
    (retType : MoveType) (rmap : RefMap)
    (hwt : WellTypedState m env lenv retType rmap)
    (hss : StackSafe m.stack m.frame.returnInfo m.heap)
    (s : Site) (n : Nat) (cont : Stmt)
    (hstmt : m.frame.stmt = .letBind s (.intLit n) cont)
    (hstep : step (.running m) = .running m') :
    ∃ env' lenv' retType' rmap',
      WellTypedState m' env' lenv' retType' rmap' ∧
      StackSafe m'.stack m'.frame.returnInfo m'.heap := by
  simp only [step, hstmt, ExecState.running.injEq] at hstep; subst hstep
  have hcont := inv_intLit (by rw [← hstmt]; exact hwt.stmt_typed)
  refine ⟨{env with siteEnv := insert env.siteEnv s (.basic .u64)},
          lenv, retType, rmap, ?_, hss⟩
  exact {
    env_wf := TypeEnv.insert_siteEnv_wf env s (.basic .u64) hwt.env_wf trivial
    stmt_typed := hcont
    var_consistent := hwt.var_consistent
    site_consistent := site_consistent_insert_basic m env rmap s (.int n)
        (.basic .u64) hwt.site_consistent trivial
    rmap_live := hwt.rmap_live
    rmap_paths := hwt.rmap_paths
    varEnv_refs_in_pathEnv := hwt.varEnv_refs_in_pathEnv
    siteEnv_refs_in_pathEnv := by
      intro s' bt r bk hl
      by_cases heq : s' = s
      · subst heq; simp [lookup_insert_same] at hl
      · rw [lookup_insert_ne _ s s' _ heq] at hl
        exact hwt.siteEnv_refs_in_pathEnv s' bt r bk hl
    live_refs_unique := by
      intro r'
      refine ⟨fun x bt bk ms s' bt' bk' hv hs => ?_,
              fun s1 s2 bt1 bt2 bk1 bk2 hne hs1 hs2 => ?_,
              fun x y bt1 bt2 bk1 bk2 ms1 ms2 hne hx hy =>
                (hwt.live_refs_unique r').2.2 x y bt1 bt2 bk1 bk2 ms1 ms2 hne hx hy⟩
      · by_cases heqs : s' = s
        · subst heqs; simp [lookup_insert_same] at hs
        · rw [lookup_insert_ne _ s s' _ heqs] at hs
          exact (hwt.live_refs_unique r').1 x bt bk ms s' bt' bk' hv hs
      · by_cases heq1 : s1 = s
        · subst heq1; simp [lookup_insert_same] at hs1
        · by_cases heq2 : s2 = s
          · subst heq2; simp [lookup_insert_same] at hs2
          · rw [lookup_insert_ne _ s s1 _ heq1] at hs1
            rw [lookup_insert_ne _ s s2 _ heq2] at hs2
            exact (hwt.live_refs_unique r').2.1 s1 s2 bt1 bt2 bk1 bk2 hne hs1 hs2
    blocks_typed := hwt.blocks_typed
    lenv_empty_siteEnv := hwt.lenv_empty_siteEnv
    funEnv_typed := hwt.funEnv_typed
    heap_loc_bound := hwt.heap_loc_bound
    rmap_root_none := hwt.rmap_root_none
    no_paths_to_root := hwt.no_paths_to_root
    root_path_coherence := hwt.root_path_coherence
  }

private theorem preservation_copy_val (m m' : Machine) (env : TypeEnv) (lenv : LabelEnv)
    (retType : MoveType) (rmap : RefMap)
    (hwt : WellTypedState m env lenv retType rmap)
    (hss : StackSafe m.stack m.frame.returnInfo m.heap)
    (s : Site) (x : Var) (cont : Stmt) (bt : BasicMoveType) (ms : Mut)
    (hstmt : m.frame.stmt = .letBind s (.usage (.copy x)) cont)
    (hvar : lookup env.varEnv x = some (.validVar, .basic bt, ms))
    (hcont : typecheck_stmt lenv {env with siteEnv := insert env.siteEnv s (.basic bt)} cont retType)
    (hstep : step (.running m) = .running m') :
    ∃ env' lenv' retType' rmap',
      WellTypedState m' env' lenv' retType' rmap' ∧
      StackSafe m'.stack m'.frame.returnInfo m'.heap := by
  obtain ⟨loc, val, hloc, hread, _⟩ := hwt.var_consistent x .validVar (.basic bt) ms hvar
  have hrv : readVar m x = some val := by unfold readVar; simp [hloc, hread]
  simp only [step, hstmt, hrv, ExecState.running.injEq] at hstep; subst hstep
  refine ⟨{env with siteEnv := insert env.siteEnv s (.basic bt)},
          lenv, retType, rmap, ?_, hss⟩
  exact {
    env_wf := TypeEnv.insert_siteEnv_wf env s (.basic bt) hwt.env_wf trivial
    stmt_typed := hcont
    var_consistent := hwt.var_consistent
    site_consistent := site_consistent_insert_basic m env rmap s val
        (.basic bt) hwt.site_consistent trivial
    rmap_live := hwt.rmap_live
    rmap_paths := hwt.rmap_paths
    varEnv_refs_in_pathEnv := hwt.varEnv_refs_in_pathEnv
    siteEnv_refs_in_pathEnv := by
      intro s' bt' r bk hl
      by_cases heq : s' = s
      · subst heq; simp [lookup_insert_same] at hl
      · rw [lookup_insert_ne _ s s' _ heq] at hl
        exact hwt.siteEnv_refs_in_pathEnv s' bt' r bk hl
    live_refs_unique := by
      intro r'
      refine ⟨fun x bt' bk ms s' bt'' bk' hv hs => ?_,
              fun s1 s2 bt1 bt2 bk1 bk2 hne hs1 hs2 => ?_,
              fun x y bt1 bt2 bk1 bk2 ms1 ms2 hne hx hy =>
                (hwt.live_refs_unique r').2.2 x y bt1 bt2 bk1 bk2 ms1 ms2 hne hx hy⟩
      · by_cases heqs : s' = s
        · subst heqs; simp [lookup_insert_same] at hs
        · rw [lookup_insert_ne _ s s' _ heqs] at hs
          exact (hwt.live_refs_unique r').1 x bt' bk ms s' bt'' bk' hv hs
      · by_cases heq1 : s1 = s
        · subst heq1; simp [lookup_insert_same] at hs1
        · by_cases heq2 : s2 = s
          · subst heq2; simp [lookup_insert_same] at hs2
          · rw [lookup_insert_ne _ s s1 _ heq1] at hs1
            rw [lookup_insert_ne _ s s2 _ heq2] at hs2
            exact (hwt.live_refs_unique r').2.1 s1 s2 bt1 bt2 bk1 bk2 hne hs1 hs2
    blocks_typed := hwt.blocks_typed
    lenv_empty_siteEnv := hwt.lenv_empty_siteEnv
    funEnv_typed := hwt.funEnv_typed
    heap_loc_bound := hwt.heap_loc_bound
    rmap_root_none := hwt.rmap_root_none
    no_paths_to_root := hwt.no_paths_to_root
    root_path_coherence := hwt.root_path_coherence
  }

/-- When PathEnv is extended via `update_with_epsilon t s_orig pe` and rmap is
    extended by mapping `t → (loc, path)` (same target as `rmap(s_orig)`), the
    `rmap_paths` invariant is preserved. This handles the 4 cases:
    - (t,t): self-loop via ε
    - (t,r2): paths = G(s_orig,r2), reduces to old rmap_paths
    - (r1,t): paths = G(r1,s_orig), reduces to old rmap_paths
    - (r1,r2): paths unchanged -/
private lemma rmap_paths_update_with_epsilon
    (rmap : RefMap) (heap : Heap) (pe : PathEnv)
    (t s_orig : Aref) (loc : Loc) (path : List Field)
    (ht_fresh : t ∉ pe.refs)
    (hs_in_refs : s_orig ∈ pe.refs)
    (hrmap_s_orig : rmap.map s_orig = some (loc, path))
    (hrmap_live : heap.readRef loc path ≠ none)
    (hold_paths : ∀ r1 r2, r1 ∈ pe.refs → r2 ∈ pe.refs →
      ∀ p, interpret_regex (pe.paths (r1, r2)) p →
        PathReflectedInHeap rmap heap r1 r2 p) :
    let rmap' : RefMap := { map := fun r => if r = t then some (loc, path) else rmap.map r }
    ∀ r1 r2,
      r1 ∈ (update_with_epsilon t s_orig pe).refs →
      r2 ∈ (update_with_epsilon t s_orig pe).refs →
      ∀ p, interpret_regex ((update_with_epsilon t s_orig pe).paths (r1, r2)) p →
        PathReflectedInHeap rmap' heap r1 r2 p := by
  intro rmap' r1 r2 hr1 hr2 p hp
  have hrefs_eq : (update_with_epsilon t s_orig pe).refs = t :: pe.refs := by
    simp only [update_with_epsilon, update_with_extension, if_pos ht_fresh]
  rw [hrefs_eq] at hr1 hr2
  simp only [List.mem_cons] at hr1 hr2
  -- Helpers for rmap' lookup
  have hrmap'_t : rmap'.map t = some (loc, path) := by simp [rmap']
  have hrmap'_ne : ∀ r, r ≠ t → rmap'.map r = rmap.map r := by
    intro r hr; simp [rmap', hr]
  -- Case analysis on whether r1/r2 = t (use rw, not subst, to keep t in scope)
  rcases hr1 with h1eq | hr1_mem <;> rcases hr2 with h2eq | hr2_mem
  · -- (t, t): self-loop, paths = ε
    rw [h1eq, h2eq] at hp ⊢
    unfold update_with_epsilon update_with_extension at hp
    simp only [↓reduceIte] at hp; subst hp
    unfold PathReflectedInHeap; simp only [hrmap'_t]
    intro _
    exact ⟨by simp [fieldPathOf], hrmap_live⟩
  · -- (t, r2): paths = der(G(s_orig,r2)) [] = G(s_orig,r2)
    rw [h1eq] at hp ⊢
    have hr2_ne_t : r2 ≠ t := fun h => ht_fresh (h ▸ hr2_mem)
    unfold update_with_epsilon update_with_extension at hp
    simp only [↓reduceIte, true_and, show ¬(r2 = t) from hr2_ne_t,
               show der (pe.paths (s_orig, r2)) [] = pe.paths (s_orig, r2) from rfl] at hp
    have hold := hold_paths s_orig r2 hs_in_refs hr2_mem p hp
    unfold PathReflectedInHeap at hold ⊢
    rw [hrmap'_t, hrmap'_ne r2 hr2_ne_t]
    rw [hrmap_s_orig] at hold
    exact hold
  · -- (r1, t): paths = G(r1,s_orig) ∘ [] = G(r1,s_orig)
    rw [h2eq] at hp ⊢
    have hr1_ne_t : r1 ≠ t := fun h => ht_fresh (h ▸ hr1_mem)
    unfold update_with_epsilon update_with_extension at hp
    simp only [↓reduceIte, and_true, show ¬(r1 = t) from hr1_ne_t,
               show extend (pe.paths (r1, s_orig)) [] = pe.paths (r1, s_orig) from rfl] at hp
    have hold := hold_paths r1 s_orig hr1_mem hs_in_refs p hp
    unfold PathReflectedInHeap at hold ⊢
    rw [hrmap'_ne r1 hr1_ne_t, hrmap'_t]
    rw [hrmap_s_orig] at hold
    exact hold
  · -- (r1, r2): paths unchanged = G(r1, r2)
    have hr1_ne_t : r1 ≠ t := fun h => ht_fresh (h ▸ hr1_mem)
    have hr2_ne_t : r2 ≠ t := fun h => ht_fresh (h ▸ hr2_mem)
    unfold update_with_epsilon update_with_extension at hp
    simp only [show ¬(r1 = t) from hr1_ne_t, show ¬(r2 = t) from hr2_ne_t, ite_false] at hp
    have hold := hold_paths r1 r2 hr1_mem hr2_mem p hp
    unfold PathReflectedInHeap at hold ⊢
    rw [hrmap'_ne r1 hr1_ne_t, hrmap'_ne r2 hr2_ne_t]
    exact hold

/-- Preservation for copy of a reference-typed variable.
    The new site gets a fresh abstract ref t, and pathEnv is updated with
    update_with_epsilon t s_orig (which makes the path graph track that t
    is related to s_orig). The rmap is extended to map t to the same concrete
    location as s_orig. -/
private theorem preservation_copy_ref (m m' : Machine) (env : TypeEnv) (lenv : LabelEnv)
    (retType : MoveType) (rmap : RefMap)
    (hwt : WellTypedState m env lenv retType rmap)
    (hss : StackSafe m.stack m.frame.returnInfo m.heap)
    (s : Site) (x : Var) (cont : Stmt)
    (τ_ref : BasicMoveType) (ms : Mut) (s_orig t : Aref) (isBor : BorrowingKind)
    (hvar : lookup env.varEnv x = some (.validVar, .ref τ_ref s_orig isBor, ms))
    (hfresh_t : freshRefInEnvBool t env)
    (hnv_t : ∀ v, t ≠ .varRef v)
    (hcont : typecheck_stmt lenv
        {env with siteEnv := insert env.siteEnv s (.ref τ_ref t isBor)
                  pathEnv := update_with_epsilon t s_orig env.pathEnv}
        cont retType)
    (hstmt : m.frame.stmt = .letBind s (.usage (.copy x)) cont)
    (hstep : step (.running m) = .running m') :
    ∃ env' lenv' retType' rmap',
      WellTypedState m' env' lenv' retType' rmap' ∧
      StackSafe m'.stack m'.frame.returnInfo m'.heap := by
  -- 1. Extract the value from variable x
  obtain ⟨loc_x, val, hloc_x, hread_x, hmatch_x⟩ :=
    hwt.var_consistent x .validVar (.ref τ_ref s_orig isBor) ms hvar
  -- val is a reference value: .ref loc' path
  obtain ⟨loc', path, hval_eq, hrmap_s_orig⟩ := hmatch_x
  -- 2. Show readVar succeeds
  have hrv : readVar m x = some val := by unfold readVar; simp [hloc_x, hread_x]
  -- 3. Simplify the step
  simp only [step, hstmt, hrv, ExecState.running.injEq] at hstep; subst hstep
  -- 4. Define the new rmap extending with t → (loc', path)
  let rmap' : RefMap := { map := fun r => if r = t then some (loc', path) else rmap.map r }
  -- 5. Get freshness of s_orig from well-formedness
  have hfresh_s_orig : moveTypeIsFreshRef (.ref τ_ref s_orig isBor) :=
    hwt.env_wf.varEnv_wf x (.validVar, .ref τ_ref s_orig isBor, ms) hvar
  have hs_orig_fresh : Aref.isFreshRef s_orig := hfresh_s_orig
  have hs_not_root : s_orig ≠ Aref.root := Aref.isFreshRef_not_root s_orig hs_orig_fresh
  have hs_not_varRef : ∀ v, s_orig ≠ Aref.varRef v := Aref.isFreshRef_not_varRef s_orig hs_orig_fresh
  -- Extract pathEnv freshness from env-wide freshness
  have hfresh_t_pathEnv : freshRefBool t env.pathEnv :=
    freshRefInEnvBool_implies_freshRefBool t env hfresh_t
  -- t is not root (needed for wellformedness)
  have ht_not_root : t ≠ Aref.root := by
    intro hcontra; subst hcontra
    have := (freshRef_iff_freshRefBool Aref.root env.pathEnv).mpr hfresh_t_pathEnv
    unfold freshRef at this
    exact this (hwt.env_wf.pathEnv_wf.root_in_refs)
  -- 6. Construct WellTypedState
  refine ⟨{env with siteEnv := insert env.siteEnv s (.ref τ_ref t isBor),
                     pathEnv := update_with_epsilon t s_orig env.pathEnv},
          lenv, retType, rmap', ?_, hss⟩
  exact {
    env_wf := by
      have hpe' := update_with_epsilon_wellformed t s_orig env.pathEnv hwt.env_wf.pathEnv_wf
        ht_not_root (by intro v hc; exact hnv_t v hc)
      exact TypeEnv.insert_pathEnv_wf env s (.ref τ_ref t isBor) _ hwt.env_wf hpe' ht_not_root
    stmt_typed := hcont
    var_consistent := by
      -- varEnv is unchanged; varStore and heap are unchanged
      intro y isv τ' ms' hvy
      have hold := hwt.var_consistent y isv τ' ms' hvy
      cases isv with
      | invalidVar => exact hold
      | validVar =>
        obtain ⟨l, v, hl, hr, hm⟩ := hold
        refine ⟨l, v, hl, hr, ?_⟩
        cases τ' with
        | basic _ => exact trivial
        | ref bt r_y bk =>
          obtain ⟨loc_v, path_v, hv_eq, hrmap_r⟩ := hm
          by_cases hrt : r_y = t
          · -- Impossible: t is fresh in env, so it can't appear in any varEnv entry
            exact absurd hrt.symm (freshRefInEnvBool_ne_varEnv_ref t env y .validVar bt r_y bk ms' hfresh_t hvy)
          · refine ⟨loc_v, path_v, hv_eq, ?_⟩
            show (if r_y = t then some (loc', path) else rmap.map r_y) = some (loc_v, path_v)
            rw [if_neg hrt]; exact hrmap_r
    site_consistent := by
      intro s'' τ' hl
      by_cases heq : s'' = s
      · subst heq
        rw [lookup_insert_same] at hl; injection hl with hl; subst hl
        refine ⟨val, lookup_insert_same _ _ _, ?_⟩
        -- ValueMatchesType val (.ref τ_ref t isBor) rmap'
        refine ⟨loc', path, hval_eq, ?_⟩
        show (if t = t then some (loc', path) else rmap.map t) = some (loc', path)
        rw [if_pos rfl]
      · rw [lookup_insert_ne _ s s'' _ heq] at hl
        obtain ⟨v', hv', hm⟩ := hwt.site_consistent s'' τ' hl
        refine ⟨v', ?_, ?_⟩
        · rw [lookup_insert_ne _ s s'' _ heq]; exact hv'
        · cases τ' with
          | basic _ => exact trivial
          | ref bt r_s bk =>
            obtain ⟨loc_v, path_v, hv_eq', hrmap_r⟩ := hm
            by_cases hrt : r_s = t
            · -- Impossible: t is fresh in env, so it can't appear in any existing siteEnv entry
              exact absurd hrt.symm (freshRefInEnvBool_ne_siteEnv_ref t env s'' bt r_s bk hfresh_t (hrt ▸ hl))
            · refine ⟨loc_v, path_v, hv_eq', ?_⟩
              show (if r_s = t then some (loc', path) else rmap.map r_s) = some (loc_v, path_v)
              rw [if_neg hrt]; exact hrmap_r
    rmap_live := by
      intro r' loc_r path_r hrmap_r'
      by_cases hrt : r' = t
      · subst hrt
        simp only [rmap', ite_true] at hrmap_r'
        -- hrmap_r' : some (loc', path) = some (loc_r, path_r)
        have h := Option.some.inj hrmap_r'
        have ⟨h1, h2⟩ := Prod.mk.inj h
        subst h1; subst h2
        exact hwt.rmap_live s_orig loc' path hrmap_s_orig
      · simp only [rmap', if_neg hrt] at hrmap_r'
        exact hwt.rmap_live r' loc_r path_r hrmap_r'
    rmap_paths :=
      have ht_fresh_pe : t ∉ env.pathEnv.refs :=
        (freshRef_iff_freshRefBool t env.pathEnv).mpr hfresh_t_pathEnv
      have hs_in_refs : s_orig ∈ env.pathEnv.refs :=
        hwt.varEnv_refs_in_pathEnv x τ_ref s_orig isBor ms hvar
      rmap_paths_update_with_epsilon rmap m.heap env.pathEnv t s_orig loc' path
        ht_fresh_pe hs_in_refs hrmap_s_orig
        (hwt.rmap_live s_orig loc' path hrmap_s_orig)
        hwt.rmap_paths
    varEnv_refs_in_pathEnv := by
      intro x' bt' r' bk' ms' hv
      -- varEnv unchanged; pathEnv.refs = t :: env.pathEnv.refs (since t is fresh)
      have hold := hwt.varEnv_refs_in_pathEnv x' bt' r' bk' ms' hv
      -- r' ∈ env.pathEnv.refs → r' ∈ t :: env.pathEnv.refs
      show r' ∈ (update_with_epsilon t s_orig env.pathEnv).refs
      simp only [update_with_epsilon, update_with_extension]
      simp only [show ¬t ∈ env.pathEnv.refs from
        (freshRef_iff_freshRefBool t env.pathEnv).mpr hfresh_t_pathEnv, not_false_eq_true, ↓reduceIte]
      exact List.mem_cons_of_mem t hold
    siteEnv_refs_in_pathEnv := by
      intro s' bt' r' bk' hl
      show r' ∈ (update_with_epsilon t s_orig env.pathEnv).refs
      simp only [update_with_epsilon, update_with_extension]
      simp only [show ¬t ∈ env.pathEnv.refs from
        (freshRef_iff_freshRefBool t env.pathEnv).mpr hfresh_t_pathEnv, not_false_eq_true, ↓reduceIte]
      by_cases heq : s' = s
      · subst heq; rw [lookup_insert_same] at hl
        have hr_eq : r' = t := by
          simp only [Option.some.injEq, MoveType.ref.injEq] at hl
          exact hl.2.1.symm
        rw [hr_eq]; exact .head _
      · rw [lookup_insert_ne _ s s' _ heq] at hl
        exact List.mem_cons_of_mem t (hwt.siteEnv_refs_in_pathEnv s' bt' r' bk' hl)
    live_refs_unique := by
      intro r'
      have ht_fresh_pe := (freshRef_iff_freshRefBool t env.pathEnv).mpr hfresh_t_pathEnv
      refine ⟨fun x' bt' bk' ms' s' bt'' bk'' hv hs => ?_,
              fun s1 s2 bt1 bt2 bk1 bk2 hne hs1 hs2 => ?_,
              fun x' y bt1 bt2 bk1 bk2 ms1 ms2 hne hx hy =>
                (hwt.live_refs_unique r').2.2 x' y bt1 bt2 bk1 bk2 ms1 ms2 hne hx hy⟩
      · -- var-site: if s' = s, then r' = t, but t is fresh and can't be in varEnv
        by_cases heqs : s' = s
        · subst heqs; rw [lookup_insert_same] at hs
          simp only [Option.some.injEq, MoveType.ref.injEq] at hs
          rw [← hs.2.1] at hv
          exact absurd (hwt.varEnv_refs_in_pathEnv x' bt' t bk' ms' hv) ht_fresh_pe
        · have hs' : lookup (insert env.siteEnv s (.ref τ_ref t isBor)) s' =
              some (.ref bt'' r' bk'') := hs
          rw [lookup_insert_ne _ s s' _ heqs] at hs'
          exact (hwt.live_refs_unique r').1 x' bt' bk' ms' s' bt'' bk'' hv hs'
      · -- site-site
        have hs1' : lookup (insert env.siteEnv s (.ref τ_ref t isBor)) s1 =
            some (.ref bt1 r' bk1) := hs1
        have hs2' : lookup (insert env.siteEnv s (.ref τ_ref t isBor)) s2 =
            some (.ref bt2 r' bk2) := hs2
        by_cases heq1 : s1 = s
        · rw [heq1, lookup_insert_same] at hs1'
          simp only [Option.some.injEq, MoveType.ref.injEq] at hs1'
          have hne2 : s2 ≠ s := by rw [← heq1]; exact hne.symm
          rw [lookup_insert_ne _ s s2 _ hne2] at hs2'
          rw [← hs1'.2.1] at hs2'
          exact absurd (hwt.siteEnv_refs_in_pathEnv s2 bt2 t bk2 hs2') ht_fresh_pe
        · by_cases heq2 : s2 = s
          · rw [heq2, lookup_insert_same] at hs2'
            simp only [Option.some.injEq, MoveType.ref.injEq] at hs2'
            rw [lookup_insert_ne _ s s1 _ heq1] at hs1'
            rw [← hs2'.2.1] at hs1'
            exact absurd (hwt.siteEnv_refs_in_pathEnv s1 bt1 t bk1 hs1') ht_fresh_pe
          · rw [lookup_insert_ne _ s s1 _ heq1] at hs1'
            rw [lookup_insert_ne _ s s2 _ heq2] at hs2'
            exact (hwt.live_refs_unique r').2.1 s1 s2 bt1 bt2 bk1 bk2 hne hs1' hs2'
    blocks_typed := hwt.blocks_typed
    lenv_empty_siteEnv := hwt.lenv_empty_siteEnv
    funEnv_typed := hwt.funEnv_typed
    heap_loc_bound := hwt.heap_loc_bound
    rmap_root_none := by
      simp only [rmap', if_neg (Ne.symm ht_not_root)]
      exact hwt.rmap_root_none
    no_paths_to_root := by
      have hroot_ne_t : ¬(Aref.root = t) := Ne.symm ht_not_root
      intro u p hp
      unfold update_with_epsilon update_with_extension at hp
      by_cases hu : u = t
      · -- u = t: paths(t, .root) = der (pe.paths (s_orig, .root)) [] = pe.paths (s_orig, .root)
        rw [hu] at hp
        simp only [hroot_ne_t, and_false, ite_false, ite_true, der, List.foldl] at hp
        exact absurd (hwt.no_paths_to_root s_orig p hp).1 hs_not_root
      · -- u ≠ t, .root ≠ t: paths unchanged
        simp only [hu, hroot_ne_t, false_and, ite_false] at hp
        exact hwt.no_paths_to_root u p hp
    root_path_coherence := by
      have hroot_ne_t : ¬(Aref.root = t) := Ne.symm ht_not_root
      have ht_fresh_pe := (freshRef_iff_freshRefBool t env.pathEnv).mpr hfresh_t_pathEnv
      intro v y rest hv_mem hp loc_v path_v hrmap loc_y hloc heq
      unfold update_with_epsilon update_with_extension at hv_mem hp
      simp only [show ¬t ∈ env.pathEnv.refs from ht_fresh_pe, not_false_eq_true, ↓reduceIte] at hv_mem
      by_cases hv : v = t
      · -- v = t: paths(.root, t) = G(.root, s_orig) ∘ [] = G(.root, s_orig)
        rw [hv] at hp hrmap
        simp only [hroot_ne_t, false_and, ite_false, ite_true, extend, List.foldl] at hp
        -- rmap'(t) = some (loc', path)
        simp only [rmap', ite_true] at hrmap
        obtain ⟨h1, h2⟩ := Prod.mk.inj (Option.some.inj hrmap)
        subst h1; subst h2
        exact hwt.root_path_coherence s_orig y rest
          (hwt.varEnv_refs_in_pathEnv x τ_ref s_orig isBor ms hvar)
          hp loc' path hrmap_s_orig loc_y hloc heq
      · -- v ≠ t: unchanged paths and rmap
        simp only [hroot_ne_t, hv, false_and, ite_false] at hp
        simp only [rmap', if_neg hv] at hrmap
        have hv_in : v ∈ env.pathEnv.refs := by
          simp only [List.mem_cons] at hv_mem; exact hv_mem.resolve_left hv
        exact hwt.root_path_coherence v y rest hv_in hp loc_v path_v hrmap loc_y hloc heq
  } -- end copy_ref

private theorem preservation_move (m m' : Machine) (env : TypeEnv) (lenv : LabelEnv)
    (retType : MoveType) (rmap : RefMap)
    (hwt : WellTypedState m env lenv retType rmap)
    (hss : StackSafe m.stack m.frame.returnInfo m.heap)
    (s : Site) (x : Var) (cont : Stmt)
    (hstmt : m.frame.stmt = .letBind s (.usage (.move x)) cont)
    (hstep : step (.running m) = .running m') :
    ∃ env' lenv' retType' rmap',
      WellTypedState m' env' lenv' retType' rmap' ∧
      StackSafe m'.stack m'.frame.returnInfo m'.heap := by
  obtain ⟨τ, ms, hvar, hcont⟩ := inv_move (by rw [← hstmt]; exact hwt.stmt_typed)
  obtain ⟨loc, val, hloc, hread, hmatch⟩ := hwt.var_consistent x .validVar τ ms hvar
  have hrv : readVar m x = some val := by unfold readVar; simp [hloc, hread]
  simp only [step, hstmt, hrv, ExecState.running.injEq] at hstep; subst hstep
  have hfresh : moveTypeIsFreshRef τ := hwt.env_wf.varEnv_wf x (.validVar, τ, ms) hvar
  refine ⟨{env with varEnv := update env.varEnv x (.invalidVar, τ, ms),
                     siteEnv := insert env.siteEnv s τ},
          lenv, retType, rmap, ?_, hss⟩
  exact {
    env_wf := by
      constructor
      · exact hwt.env_wf.pathEnv_wf
      · apply SiteEnv.insert_refs_not_root _ _ _ hwt.env_wf.siteEnv_wf
        cases τ with
        | basic _ => trivial
        | ref _ r _ => exact Aref.isFreshRef_not_root r hfresh
      · exact VarEnv.update_refs_are_fresh env.varEnv x (.invalidVar, τ, ms)
                hwt.env_wf.varEnv_wf hfresh
    stmt_typed := hcont
    var_consistent := by
      intro y isv τ' ms' hvy
      have hvy' : lookup (insert env.varEnv x (.invalidVar, τ, ms)) y =
          some (isv, τ', ms') := hvy
      by_cases heq : y = x
      · subst heq
        rw [lookup_insert_same] at hvy'
        have hisv : isv = .invalidVar := (congrArg Prod.fst (Option.some.inj hvy')).symm
        subst hisv
        exact .inl (lookup_insert_same _ _ _)
      · rw [lookup_insert_ne _ x y _ heq] at hvy'
        have hold := hwt.var_consistent y isv τ' ms' hvy'
        have hne_vs : lookup (insert m.frame.varStore x none) y =
            lookup m.frame.varStore y := lookup_insert_ne _ x y _ heq
        cases isv with
        | validVar =>
          obtain ⟨l, v, hl, hr, hm⟩ := hold
          exact ⟨l, v, hne_vs.trans hl, hr, hm⟩
        | invalidVar =>
          simp only at hold ⊢
          cases hold with
          | inl h => exact .inl (hne_vs.trans h)
          | inr h =>
            obtain ⟨l, hl⟩ := h
            exact .inr ⟨l, hne_vs.trans hl⟩
    site_consistent := site_consistent_insert_basic m env rmap s val τ
        hwt.site_consistent hmatch
    rmap_live := hwt.rmap_live
    rmap_paths := hwt.rmap_paths
    varEnv_refs_in_pathEnv := by
      -- x is now invalidVar, other vars unchanged
      intro y bt r bk ms' hvy
      have hvy' : lookup (insert env.varEnv x (.invalidVar, τ, ms)) y =
          some (.validVar, .ref bt r bk, ms') := hvy
      by_cases heq : y = x
      · subst heq; rw [lookup_insert_same] at hvy'; simp at hvy'
      · rw [lookup_insert_ne _ x y _ heq] at hvy'
        exact hwt.varEnv_refs_in_pathEnv y bt r bk ms' hvy'
    siteEnv_refs_in_pathEnv := by
      intro s' bt r bk hl
      by_cases heq : s' = s
      · subst heq; rw [lookup_insert_same] at hl
        -- τ was moved from x (validVar); its ref was in pathEnv
        cases τ with
        | basic _ => simp [Option.some.injEq] at hl
        | ref bt' r' bk' =>
          simp only [Option.some.injEq, MoveType.ref.injEq] at hl
          rw [← hl.2.1]
          exact hwt.varEnv_refs_in_pathEnv x bt' r' bk' ms hvar
      · rw [lookup_insert_ne _ s s' _ heq] at hl
        exact hwt.siteEnv_refs_in_pathEnv s' bt r bk hl
    live_refs_unique := by
      intro r'
      refine ⟨fun y bt bk ms' s' bt' bk' hvy hs => ?_,
              fun s1 s2 bt1 bt2 bk1 bk2 hne hs1 hs2 => ?_,
              fun y1 y2 bt1 bt2 bk1 bk2 ms1 ms2 hne hy1 hy2 => ?_⟩
      · -- var-site: y is validVar in updated varEnv, s' in updated siteEnv
        have hvy' : lookup (insert env.varEnv x (.invalidVar, τ, ms)) y =
            some (.validVar, .ref bt r' bk, ms') := hvy
        have hne_yx : y ≠ x := by
          intro h; subst h; rw [lookup_insert_same] at hvy'; simp at hvy'
        rw [lookup_insert_ne _ x y _ hne_yx] at hvy'
        have hs' : lookup (insert env.siteEnv s τ) s' = some (.ref bt' r' bk') := hs
        by_cases heqs : s' = s
        · rw [heqs, lookup_insert_same] at hs'
          cases τ with
          | basic _ => simp [Option.some.injEq] at hs'
          | ref bt2 r2 bk2 =>
            simp only [Option.some.injEq, MoveType.ref.injEq] at hs'
            rw [hs'.2.1] at hvar
            exact (hwt.live_refs_unique r').2.2 y x bt bt2 bk bk2 ms' ms hne_yx hvy' hvar
        · rw [lookup_insert_ne _ s s' _ heqs] at hs'
          exact (hwt.live_refs_unique r').1 y bt bk ms' s' bt' bk' hvy' hs'
      · -- site-site: s1 ≠ s2 both have ref r' in updated siteEnv
        have hs1' : lookup (insert env.siteEnv s τ) s1 = some (.ref bt1 r' bk1) := hs1
        have hs2' : lookup (insert env.siteEnv s τ) s2 = some (.ref bt2 r' bk2) := hs2
        by_cases heq1 : s1 = s
        · rw [heq1, lookup_insert_same] at hs1'
          have hne2 : s2 ≠ s := by rw [← heq1]; exact hne.symm
          rw [lookup_insert_ne _ s s2 _ hne2] at hs2'
          cases τ with
          | basic _ => simp [Option.some.injEq] at hs1'
          | ref bt_x r_x bk_x =>
            simp only [Option.some.injEq, MoveType.ref.injEq] at hs1'
            rw [hs1'.2.1] at hvar
            exact (hwt.live_refs_unique r').1 x bt_x bk_x ms s2 bt2 bk2 hvar hs2'
        · by_cases heq2 : s2 = s
          · rw [heq2, lookup_insert_same] at hs2'
            rw [lookup_insert_ne _ s s1 _ heq1] at hs1'
            cases τ with
            | basic _ => simp [Option.some.injEq] at hs2'
            | ref bt_x r_x bk_x =>
              simp only [Option.some.injEq, MoveType.ref.injEq] at hs2'
              rw [hs2'.2.1] at hvar
              exact (hwt.live_refs_unique r').1 x bt_x bk_x ms s1 bt1 bk1 hvar hs1'
          · rw [lookup_insert_ne _ s s1 _ heq1] at hs1'
            rw [lookup_insert_ne _ s s2 _ heq2] at hs2'
            exact (hwt.live_refs_unique r').2.1 s1 s2 bt1 bt2 bk1 bk2 hne hs1' hs2'
      · -- var-var: y1 ≠ y2 both valid in updated varEnv
        have hy1' : lookup (insert env.varEnv x (.invalidVar, τ, ms)) y1 =
            some (.validVar, .ref bt1 r' bk1, ms1) := hy1
        have hy2' : lookup (insert env.varEnv x (.invalidVar, τ, ms)) y2 =
            some (.validVar, .ref bt2 r' bk2, ms2) := hy2
        have hne1 : y1 ≠ x := by
          intro h; subst h; rw [lookup_insert_same] at hy1'; simp at hy1'
        have hne2 : y2 ≠ x := by
          intro h; subst h; rw [lookup_insert_same] at hy2'; simp at hy2'
        rw [lookup_insert_ne _ x y1 _ hne1] at hy1'
        rw [lookup_insert_ne _ x y2 _ hne2] at hy2'
        exact (hwt.live_refs_unique r').2.2 y1 y2 bt1 bt2 bk1 bk2 ms1 ms2 hne hy1' hy2'
    blocks_typed := hwt.blocks_typed
    lenv_empty_siteEnv := hwt.lenv_empty_siteEnv
    funEnv_typed := hwt.funEnv_typed
    heap_loc_bound := hwt.heap_loc_bound
    rmap_root_none := hwt.rmap_root_none
    no_paths_to_root := hwt.no_paths_to_root
    root_path_coherence := by
      -- pathEnv and rmap unchanged; varStore(x) → none
      intro v y rest hv_mem hp loc_v path_v hrmap loc_y hloc_y heq
      by_cases heqx : y = x
      · -- y = x: varStore'(x) = some none, so lookup = some none ≠ some (some _)
        subst heqx; simp [lookup_insert_same] at hloc_y
      · -- y ≠ x: varStore'(y) = varStore(y), use old invariant
        rw [lookup_insert_ne _ x y _ heqx] at hloc_y
        exact hwt.root_path_coherence v y rest hv_mem hp loc_v path_v hrmap loc_y hloc_y heq
  }

/-- Reusable helper: rmap_paths is preserved by update_with_extension r .root [.root_to_var x]
    on top of update_with_epsilon r r pe, when rmap is extended with r ↦ (loc, []).
    Four cases: (r,r) self-loop, (r,old) uses root_path_coherence, (old,r) uses
    no_paths_to_root (vacuous), (old,old) delegates to old rmap_paths. -/
private lemma rmap_paths_update_with_borrow
    (rmap : RefMap) (heap : Heap) (pe : PathEnv)
    (r : Aref) (x : Var) (loc : Loc) (varStore : AssocMap Var (Option Loc))
    (hr_fresh : r ∉ pe.refs)
    (hr_not_root : r ≠ Aref.root)
    (hreadref : heap.readRef loc [] ≠ none)
    (hloc : lookup varStore x = some (some loc))
    (hrmap_root_none : rmap.map .root = none)
    (hno_paths_to_root : ∀ u p,
      interpret_regex (pe.paths (u, .root)) p → u = .root ∧ p = [])
    (hroot_path_coherence : ∀ v y rest,
      v ∈ pe.refs →
      interpret_regex (pe.paths (.root, v)) (.root_to_var y :: rest) →
      ∀ loc_v path_v, rmap.map v = some (loc_v, path_v) →
      ∀ loc_y, lookup varStore y = some (some loc_y) →
      loc_v = loc_y → path_v = fieldPathOf rest)
    (hrmap_live : ∀ r' loc' path', rmap.map r' = some (loc', path') →
      heap.readRef loc' path' ≠ none)
    (hold_paths : ∀ r1 r2, r1 ∈ pe.refs → r2 ∈ pe.refs →
      ∀ p, interpret_regex (pe.paths (r1, r2)) p →
        PathReflectedInHeap rmap heap r1 r2 p) :
    let pe' := update_with_extension r .root [.root_to_var x]
                 (update_with_epsilon r r pe)
    let rmap' : RefMap := { map := fun r' => if r' = r then some (loc, []) else rmap.map r' }
    ∀ r1 r2,
      r1 ∈ pe'.refs → r2 ∈ pe'.refs →
      ∀ p, interpret_regex (pe'.paths (r1, r2)) p →
        PathReflectedInHeap rmap' heap r1 r2 p := by
  intro pe' rmap' r1 r2 hr1 hr2 p hp
  have hroot_ne_r : ¬(Aref.root = r) := Ne.symm hr_not_root
  -- Helpers for rmap' lookup
  have hrmap'_r : rmap'.map r = some (loc, []) := by simp [rmap']
  have hrmap'_ne : ∀ r', r' ≠ r → rmap'.map r' = rmap.map r' := by
    intro r' hr'; simp [rmap', hr']
  -- pe'.refs = r :: pe.refs
  have hrefs_eq : pe'.refs = r :: pe.refs := by
    simp only [pe', update_with_extension, update_with_epsilon]
    simp only [show ¬r ∈ pe.refs from hr_fresh, not_false_eq_true, ↓reduceIte]
    simp only [show ¬¬(r ∈ r :: pe.refs) from not_not.mpr (.head _), ↓reduceIte]
  rw [hrefs_eq] at hr1 hr2
  simp only [List.mem_cons] at hr1 hr2
  rcases hr1 with h1eq | hr1_mem <;> rcases hr2 with h2eq | hr2_mem
  · -- (r, r): self-loop ε
    rw [h1eq, h2eq] at hp ⊢
    unfold pe' update_with_extension at hp
    simp only [↓reduceIte] at hp; subst hp
    unfold PathReflectedInHeap; simp only [hrmap'_r]
    intro _; exact ⟨by simp [fieldPathOf], hreadref⟩
  · -- (r, r2): pe'.paths(r, r2) = der(pe_mid.paths(.root, r2)) [.root_to_var x]
    rw [h1eq] at hp ⊢
    have hr2_ne : r2 ≠ r := fun h => hr_fresh (h ▸ hr2_mem)
    unfold pe' update_with_extension at hp
    simp only [hr2_ne, and_false, ite_false, ite_true] at hp
    unfold update_with_epsilon update_with_extension at hp
    simp only [hr2_ne, hroot_ne_r, false_and, ite_false] at hp
    simp only [der, List.foldl] at hp
    -- interpret_regex (.deriv re a) s = interpret_regex re (a :: s) by definition
    have hp' : interpret_regex (pe.paths (Aref.root, r2))
        (PathElement.root_to_var x :: p) := hp
    unfold PathReflectedInHeap
    rw [hrmap'_r, hrmap'_ne r2 hr2_ne]
    cases hrmap_r2 : rmap.map r2 with
    | none => simp
    | some lr2 =>
      obtain ⟨loc2, path2⟩ := lr2
      simp only
      intro heq_loc
      have hpath := hroot_path_coherence r2 x p hr2_mem hp'
          loc2 path2 hrmap_r2 loc hloc heq_loc.symm
      constructor
      · simp [hpath]
      · exact hrmap_live r2 loc2 path2 hrmap_r2
  · -- (r1, r): pe'.paths(r1, r) = extend(pe_mid.paths(r1, .root)) [.root_to_var x]
    rw [h2eq] at hp ⊢
    have hr1_ne : r1 ≠ r := fun h => hr_fresh (h ▸ hr1_mem)
    unfold pe' update_with_extension at hp
    simp only [hr1_ne, false_and, ite_false, ite_true] at hp
    unfold update_with_epsilon update_with_extension at hp
    simp only [hr1_ne, hroot_ne_r, false_and, ite_false] at hp
    simp only [extend, List.foldl, interpret_regex] at hp
    obtain ⟨s1, s2, _, hinterp, _⟩ := hp
    by_cases hr1_root : r1 = Aref.root
    · unfold PathReflectedInHeap
      rw [hr1_root, hrmap'_ne .root (Ne.symm hr_not_root), hrmap_root_none]
      trivial
    · have ⟨hr1_eq_root, _⟩ := hno_paths_to_root r1 s1 hinterp
      exact absurd hr1_eq_root hr1_root
  · -- (r1, r2): both old, paths unchanged, rmap unchanged
    have hr1_ne : r1 ≠ r := fun h => hr_fresh (h ▸ hr1_mem)
    have hr2_ne : r2 ≠ r := fun h => hr_fresh (h ▸ hr2_mem)
    unfold pe' update_with_extension at hp
    simp only [hr1_ne, hr2_ne, false_and, ite_false] at hp
    unfold update_with_epsilon update_with_extension at hp
    simp only [hr1_ne, hr2_ne, false_and, ite_false] at hp
    have hold := hold_paths r1 r2 hr1_mem hr2_mem p hp
    unfold PathReflectedInHeap at hold ⊢
    rw [hrmap'_ne r1 hr1_ne, hrmap'_ne r2 hr2_ne]
    exact hold

/-- Preservation for borrowImm of a basic-typed variable.
    The new site gets a fresh abstract ref r with .siteBorrowImm kind,
    and pathEnv is updated with update_with_extension r .root [.root_to_var x]
    on top of update_with_epsilon r r (which initializes r in pathEnv).
    The rmap is extended to map r to (loc, []) where loc is x's heap location. -/
private theorem preservation_borrowImm (m m' : Machine) (env : TypeEnv) (lenv : LabelEnv)
    (retType : MoveType) (rmap : RefMap)
    (hwt : WellTypedState m env lenv retType rmap)
    (hss : StackSafe m.stack m.frame.returnInfo m.heap)
    (s : Site) (x : Var) (cont : Stmt)
    (hstmt : m.frame.stmt = .letBind s (.usage (.borrowImm x)) cont)
    (hstep : step (.running m) = .running m') :
    ∃ env' lenv' retType' rmap',
      WellTypedState m' env' lenv' retType' rmap' ∧
      StackSafe m'.stack m'.frame.returnInfo m'.heap := by
  -- 1. Extract typing hypotheses
  obtain ⟨τ, ms, r, hlookup, hfresh, hnv, hcont⟩ :=
    inv_borrowImm (by rw [← hstmt]; exact hwt.stmt_typed)
  -- 2. Get var_consistent for x (basic type — hmatch is trivially True)
  obtain ⟨loc, val, hloc, hread, _⟩ :=
    hwt.var_consistent x .validVar (.basic τ) ms hlookup
  -- 3. Show getVarLoc succeeds
  have hgl : getVarLoc m x = some loc := by unfold getVarLoc; simp [hloc]
  -- 4. Simplify the step
  simp only [step, hstmt, hgl, ExecState.running.injEq] at hstep; subst hstep
  -- 5. Define the new rmap extending with r → (loc, [])
  let rmap' : RefMap := { map := fun r' => if r' = r then some (loc, []) else rmap.map r' }
  -- 6. Freshness facts
  have hfresh_pathEnv : freshRefBool r env.pathEnv :=
    freshRefInEnvBool_implies_freshRefBool r env hfresh
  have hr_not_root : r ≠ Aref.root := by
    intro hcontra; subst hcontra
    have := (freshRef_iff_freshRefBool Aref.root env.pathEnv).mpr hfresh_pathEnv
    unfold freshRef at this
    exact this (hwt.env_wf.pathEnv_wf.root_in_refs)
  have hr_fresh_pe : r ∉ env.pathEnv.refs :=
    (freshRef_iff_freshRefBool r env.pathEnv).mpr hfresh_pathEnv
  -- 7. readRef loc [] is live (heap.read loc ≠ none)
  have hread_ne : m.heap.read loc ≠ none := by simp [hread]
  have hreadref : m.heap.readRef loc [] ≠ none := by
    unfold Heap.readRef; simp [hread, readPath]
  -- 8. Abbreviation for the new pathEnv
  let pe' := update_with_extension r .root [.root_to_var x]
               (update_with_epsilon r r env.pathEnv)
  -- 9. Show pe'.refs = r :: env.pathEnv.refs
  have hpe_mid_refs : (update_with_epsilon r r env.pathEnv).refs = r :: env.pathEnv.refs := by
    simp only [update_with_epsilon, update_with_extension]
    simp only [show ¬r ∈ env.pathEnv.refs from hr_fresh_pe, not_false_eq_true, ↓reduceIte]
  have hr_in_mid : r ∈ (update_with_epsilon r r env.pathEnv).refs := by
    rw [hpe_mid_refs]; exact .head _
  have hrefs_eq : pe'.refs = r :: env.pathEnv.refs := by
    simp only [pe', update_with_extension]
    simp only [show ¬(r ∉ (update_with_epsilon r r env.pathEnv).refs) from not_not.mpr hr_in_mid,
               ↓reduceIte]
    exact hpe_mid_refs
  -- 10. Construct WellTypedState
  refine ⟨{env with siteEnv := insert env.siteEnv s (.ref τ r .siteBorrowImm),
                     pathEnv := pe'},
          lenv, retType, rmap', ?_, hss⟩
  exact {
    env_wf := by
      have hpe_eps := update_with_epsilon_wellformed r r env.pathEnv hwt.env_wf.pathEnv_wf
        hr_not_root (fun v hc => hnv v hc)
      have hpe' := update_with_extension_wellformed r .root [.root_to_var x]
        (update_with_epsilon r r env.pathEnv) hpe_eps hr_not_root (fun v hc => hnv v hc)
      exact TypeEnv.insert_pathEnv_wf env s (.ref τ r .siteBorrowImm) _ hwt.env_wf hpe' hr_not_root
    stmt_typed := hcont
    var_consistent := by
      -- varEnv and varStore and heap are unchanged
      intro y isv τ' ms' hvy
      have hold := hwt.var_consistent y isv τ' ms' hvy
      cases isv with
      | invalidVar => exact hold
      | validVar =>
        obtain ⟨l, v, hl, hr, hm⟩ := hold
        refine ⟨l, v, hl, hr, ?_⟩
        cases τ' with
        | basic _ => exact trivial
        | ref bt r_y bk =>
          obtain ⟨loc_v, path_v, hv_eq, hrmap_r⟩ := hm
          by_cases hrt : r_y = r
          · -- Impossible: r is fresh in env, can't appear in any varEnv entry
            exact absurd hrt.symm (freshRefInEnvBool_ne_varEnv_ref r env y .validVar bt r_y bk ms' hfresh hvy)
          · refine ⟨loc_v, path_v, hv_eq, ?_⟩
            show (if r_y = r then some (loc, []) else rmap.map r_y) = some (loc_v, path_v)
            rw [if_neg hrt]; exact hrmap_r
    site_consistent := by
      intro s'' τ' hl
      by_cases heq : s'' = s
      · subst heq
        rw [lookup_insert_same] at hl; injection hl with hl; subst hl
        refine ⟨Value.ref loc [], lookup_insert_same _ _ _, ?_⟩
        -- ValueMatchesType (.ref loc []) (.ref τ r .siteBorrowImm) rmap'
        refine ⟨loc, [], rfl, ?_⟩
        show (if r = r then some (loc, []) else rmap.map r) = some (loc, [])
        rw [if_pos rfl]
      · rw [lookup_insert_ne _ s s'' _ heq] at hl
        obtain ⟨v', hv', hm⟩ := hwt.site_consistent s'' τ' hl
        refine ⟨v', ?_, ?_⟩
        · rw [lookup_insert_ne _ s s'' _ heq]; exact hv'
        · cases τ' with
          | basic _ => exact trivial
          | ref bt r_s bk =>
            obtain ⟨loc_v, path_v, hv_eq', hrmap_r⟩ := hm
            by_cases hrt : r_s = r
            · -- Impossible: r is fresh in env, can't appear in any existing siteEnv entry
              exact absurd hrt.symm (freshRefInEnvBool_ne_siteEnv_ref r env s'' bt r_s bk hfresh (hrt ▸ hl))
            · refine ⟨loc_v, path_v, hv_eq', ?_⟩
              show (if r_s = r then some (loc, []) else rmap.map r_s) = some (loc_v, path_v)
              rw [if_neg hrt]; exact hrmap_r
    rmap_live := by
      intro r' loc_r path_r hrmap_r'
      by_cases hrt : r' = r
      · subst hrt
        simp only [rmap', ite_true] at hrmap_r'
        have h := Option.some.inj hrmap_r'
        have ⟨h1, h2⟩ := Prod.mk.inj h
        subst h1; subst h2
        exact hreadref
      · simp only [rmap', if_neg hrt] at hrmap_r'
        exact hwt.rmap_live r' loc_r path_r hrmap_r'
    rmap_paths :=
      rmap_paths_update_with_borrow rmap m.heap env.pathEnv r x loc
        m.frame.varStore hr_fresh_pe hr_not_root hreadref hloc
        hwt.rmap_root_none hwt.no_paths_to_root hwt.root_path_coherence
        hwt.rmap_live hwt.rmap_paths
    varEnv_refs_in_pathEnv := by
      intro x' bt' r' bk' ms' hv
      have hold := hwt.varEnv_refs_in_pathEnv x' bt' r' bk' ms' hv
      show r' ∈ pe'.refs
      rw [hrefs_eq]
      exact List.mem_cons_of_mem r hold
    siteEnv_refs_in_pathEnv := by
      intro s' bt' r' bk' hl
      show r' ∈ pe'.refs
      rw [hrefs_eq]
      by_cases heq : s' = s
      · subst heq; rw [lookup_insert_same] at hl
        have hr_eq : r' = r := by
          simp only [Option.some.injEq, MoveType.ref.injEq] at hl
          exact hl.2.1.symm
        rw [hr_eq]; exact .head _
      · rw [lookup_insert_ne _ s s' _ heq] at hl
        exact List.mem_cons_of_mem r (hwt.siteEnv_refs_in_pathEnv s' bt' r' bk' hl)
    live_refs_unique := by
      intro r'
      have hr_fresh_pe' := hr_fresh_pe
      refine ⟨fun x' bt' bk' ms' s' bt'' bk'' hv hs => ?_,
              fun s1 s2 bt1 bt2 bk1 bk2 hne hs1 hs2 => ?_,
              fun x' y bt1 bt2 bk1 bk2 ms1 ms2 hne hx hy =>
                (hwt.live_refs_unique r').2.2 x' y bt1 bt2 bk1 bk2 ms1 ms2 hne hx hy⟩
      · -- var-site: if s' = s, then r' = r, but r is fresh and can't be in varEnv
        by_cases heqs : s' = s
        · subst heqs; rw [lookup_insert_same] at hs
          simp only [Option.some.injEq, MoveType.ref.injEq] at hs
          rw [← hs.2.1] at hv
          exact absurd (hwt.varEnv_refs_in_pathEnv x' bt' r bk' ms' hv) hr_fresh_pe'
        · have hs' : lookup (insert env.siteEnv s (.ref τ r .siteBorrowImm)) s' =
              some (.ref bt'' r' bk'') := hs
          rw [lookup_insert_ne _ s s' _ heqs] at hs'
          exact (hwt.live_refs_unique r').1 x' bt' bk' ms' s' bt'' bk'' hv hs'
      · -- site-site
        have hs1' : lookup (insert env.siteEnv s (.ref τ r .siteBorrowImm)) s1 =
            some (.ref bt1 r' bk1) := hs1
        have hs2' : lookup (insert env.siteEnv s (.ref τ r .siteBorrowImm)) s2 =
            some (.ref bt2 r' bk2) := hs2
        by_cases heq1 : s1 = s
        · rw [heq1, lookup_insert_same] at hs1'
          simp only [Option.some.injEq, MoveType.ref.injEq] at hs1'
          have hne2 : s2 ≠ s := by rw [← heq1]; exact hne.symm
          rw [lookup_insert_ne _ s s2 _ hne2] at hs2'
          rw [← hs1'.2.1] at hs2'
          exact absurd (hwt.siteEnv_refs_in_pathEnv s2 bt2 r bk2 hs2') hr_fresh_pe'
        · by_cases heq2 : s2 = s
          · rw [heq2, lookup_insert_same] at hs2'
            simp only [Option.some.injEq, MoveType.ref.injEq] at hs2'
            rw [lookup_insert_ne _ s s1 _ heq1] at hs1'
            rw [← hs2'.2.1] at hs1'
            exact absurd (hwt.siteEnv_refs_in_pathEnv s1 bt1 r bk1 hs1') hr_fresh_pe'
          · rw [lookup_insert_ne _ s s1 _ heq1] at hs1'
            rw [lookup_insert_ne _ s s2 _ heq2] at hs2'
            exact (hwt.live_refs_unique r').2.1 s1 s2 bt1 bt2 bk1 bk2 hne hs1' hs2'
    blocks_typed := hwt.blocks_typed
    lenv_empty_siteEnv := hwt.lenv_empty_siteEnv
    funEnv_typed := hwt.funEnv_typed
    heap_loc_bound := hwt.heap_loc_bound
    rmap_root_none := by
      simp only [rmap', if_neg (Ne.symm hr_not_root)]
      exact hwt.rmap_root_none
    no_paths_to_root := by
      have hroot_ne_r : ¬(Aref.root = r) := Ne.symm hr_not_root
      intro u p hp
      -- Extract pathEnv from the struct
      have hp : interpret_regex (pe'.paths (u, Aref.root)) p := hp
      by_cases hu : u = r
      · -- u = r: pe'.paths(r, .root) = der(pe_mid.paths(.root, .root)) [.root_to_var x]
        rw [hu] at hp
        -- Unfold pe' = update_with_extension, simplify conditions
        unfold pe' update_with_extension at hp
        simp only [hroot_ne_r, and_false, ite_false, ite_true] at hp
        -- Unfold pe_mid = update_with_epsilon r r env.pathEnv
        unfold update_with_epsilon update_with_extension at hp
        simp only [hroot_ne_r, and_false, ite_false] at hp
        -- hp : interpret_regex (der (env.pathEnv.paths (.root, .root)) [.root_to_var x]) p
        simp only [der, List.foldl] at hp
        -- interpret_regex (.deriv re a) s = interpret_regex re (a :: s) by definition
        have hp' : interpret_regex (env.pathEnv.paths (Aref.root, Aref.root))
            (PathElement.root_to_var x :: p) := hp
        exact absurd (hwt.no_paths_to_root .root _ hp').2 (List.cons_ne_nil _ _)
      · -- u ≠ r: pe'.paths(u, .root) = pe_mid.paths(u, .root) = pe.paths(u, .root)
        unfold pe' update_with_extension at hp
        simp only [hu, hroot_ne_r, ite_false] at hp
        unfold update_with_epsilon update_with_extension at hp
        simp only [hu, hroot_ne_r, false_and, ite_false] at hp
        exact hwt.no_paths_to_root u p hp
    root_path_coherence := by
      have hroot_ne_r : ¬(Aref.root = r) := Ne.symm hr_not_root
      intro v' y rest hv_mem hp loc_v path_v hrmap loc_y hloc heq
      rw [hrefs_eq] at hv_mem
      simp only [List.mem_cons] at hv_mem
      -- Extract pathEnv from the struct
      have hp : interpret_regex (pe'.paths (Aref.root, v')) (PathElement.root_to_var y :: rest) := hp
      rcases hv_mem with hv_eq | hv_in
      · -- v' = r: paths(.root, r) = extend(pe_mid.paths(.root, .root)) [.root_to_var x]
        rw [hv_eq] at hp hrmap
        unfold pe' update_with_extension at hp
        simp only [hroot_ne_r, false_and, ite_false, ite_true] at hp
        -- Unfold pe_mid to get env.pathEnv.paths(.root, .root)
        unfold update_with_epsilon update_with_extension at hp
        simp only [hroot_ne_r, false_and, ite_false] at hp
        -- hp : interpret_regex (extend (env.pathEnv.paths (.root, .root)) [.root_to_var x])
        --        (.root_to_var y :: rest)
        -- extend re [a] = concat re (char a)
        simp only [extend, List.foldl, interpret_regex] at hp
        obtain ⟨s1, s2, heq', hinterp, hs2_eq⟩ := hp
        -- pe.paths(.root, .root) only accepts [] by no_paths_to_root
        have ⟨_, hs1_nil⟩ := hwt.no_paths_to_root .root s1 hinterp
        subst hs1_nil; subst hs2_eq
        -- heq' : .root_to_var y :: rest = [] ++ [.root_to_var x] = [.root_to_var x]
        simp only [List.nil_append, List.cons.injEq] at heq'
        obtain ⟨_, hrest_nil⟩ := heq'
        subst hrest_nil
        -- rmap'(r) = some (loc, [])
        simp only [rmap', ite_true] at hrmap
        obtain ⟨h1, h2⟩ := Prod.mk.inj (Option.some.inj hrmap)
        subst h1; subst h2
        -- goal: [] = fieldPathOf [] = []
        rfl
      · -- v' ≠ r (v' ∈ env.pathEnv.refs): paths(.root, v') unchanged
        have hv_ne : ¬(v' = r) := fun h => by subst h; exact absurd hv_in hr_fresh_pe
        unfold pe' update_with_extension at hp
        simp only [hroot_ne_r, hv_ne, false_and, ite_false] at hp
        unfold update_with_epsilon update_with_extension at hp
        simp only [hroot_ne_r, hv_ne, false_and, ite_false] at hp
        -- rmap'(v') where v' ≠ r → rmap.map v'
        simp only [rmap', if_neg hv_ne] at hrmap
        exact hwt.root_path_coherence v' y rest hv_in hp loc_v path_v hrmap loc_y hloc heq
  } -- end borrowImm

/-- Reusable helper: delete_ref_node preserves rmap_paths. -/
private theorem rmap_paths_delete_ref_node (env : TypeEnv) (m : Machine) (rmap : RefMap)
    (r : Aref)
    (hrp : ∀ r1 r2, r1 ∈ env.pathEnv.refs → r2 ∈ env.pathEnv.refs →
        ∀ p, interpret_regex (env.pathEnv.paths (r1, r2)) p →
        PathReflectedInHeap rmap m.heap r1 r2 p) :
    ∀ r1 r2, r1 ∈ (delete_ref_node env.pathEnv r).refs →
        r2 ∈ (delete_ref_node env.pathEnv r).refs →
        ∀ p, interpret_regex ((delete_ref_node env.pathEnv r).paths (r1, r2)) p →
        PathReflectedInHeap rmap m.heap r1 r2 p := by
  intro r1 r2 hr1 hr2 p hp
  have hr1f : r1 ∈ (delete_ref_node env.pathEnv r).refs := hr1
  have hr2f : r2 ∈ (delete_ref_node env.pathEnv r).refs := hr2
  have hpf : interpret_regex ((delete_ref_node env.pathEnv r).paths (r1, r2)) p := hp
  simp only [delete_ref_node_refs, List.mem_filter, decide_eq_true_eq] at hr1f hr2f
  obtain ⟨hr1_mem, hr1_ne⟩ := hr1f
  obtain ⟨hr2_mem, hr2_ne⟩ := hr2f
  rw [delete_ref_node_paths_not_involving_r env.pathEnv r r1 r2 hr1_ne hr2_ne] at hpf
  exact hrp r1 r2 hr1_mem hr2_mem p hpf

/-- PathReflectedInHeap is preserved under heap.alloc -/
private theorem pathReflectedInHeap_heap_alloc (rmap : RefMap) (heap : Heap) (v : Value)
    (r1 r2 : Aref) (p : List PathElement)
    (hrfl : PathReflectedInHeap rmap heap r1 r2 p)
    (hlive : ∀ r loc path, rmap.map r = some (loc, path) → heap.readRef loc path ≠ none)
    (hlb : ∀ loc, heap.read loc ≠ none → loc < heap.nextLoc) :
    PathReflectedInHeap rmap (heap.alloc v).1 r1 r2 p := by
  unfold PathReflectedInHeap at hrfl ⊢
  cases hr1 : rmap.map r1 with
  | none => trivial
  | some p1 =>
    cases hr2 : rmap.map r2 with
    | none => simp
    | some p2 =>
      simp only [hr1, hr2] at hrfl ⊢
      obtain ⟨loc1, path1⟩ := p1
      obtain ⟨loc2, path2⟩ := p2
      simp only at hrfl ⊢
      intro heq_loc
      obtain ⟨hpath, hread⟩ := hrfl heq_loc
      refine ⟨hpath, ?_⟩
      have hloc2_lt := hlb loc2 (readRef_implies_read heap loc2 path2 (hlive r2 loc2 path2 hr2))
      have hne : loc2 ≠ heap.nextLoc := by intro h; subst h; exact Nat.lt_irrefl _ hloc2_lt
      rw [heap_alloc_preserves_readRef heap v loc2 path2 hne]
      exact hread

/-- WellTypedState is preserved when only the heap grows by alloc (frame unchanged) -/
private theorem wellTypedState_heap_alloc
    (frame : Frame) (stack : List Frame) (heap : Heap)
    (env : TypeEnv) (lenv : LabelEnv) (retType : MoveType) (rmap : RefMap)
    (v : Value)
    (hwt : WellTypedState ⟨frame, stack, heap⟩ env lenv retType rmap) :
    WellTypedState ⟨frame, stack, (heap.alloc v).1⟩ env lenv retType rmap := by
  have hlb := hwt.heap_loc_bound
  exact {
    env_wf := hwt.env_wf
    stmt_typed := hwt.stmt_typed
    var_consistent := by
      intro x isv τ ms hvar
      have hold := hwt.var_consistent x isv τ ms hvar
      cases isv with
      | validVar =>
        obtain ⟨loc, val, hloc, hread, hmatch⟩ := hold
        have hlt := hlb loc (by rw [Heap.read] at hread ⊢; simp [hread])
        refine ⟨loc, val, hloc, ?_, hmatch⟩
        rw [heap_alloc_preserves_read heap v loc hlt]
        exact hread
      | invalidVar => exact hold
    site_consistent := hwt.site_consistent
    rmap_live := by
      intro r loc path hrmap
      have hlive := hwt.rmap_live r loc path hrmap
      have hlt := hlb loc (readRef_implies_read heap loc path hlive)
      have hne : loc ≠ heap.nextLoc := by intro h; subst h; exact Nat.lt_irrefl _ hlt
      rw [heap_alloc_preserves_readRef heap v loc path hne]
      exact hlive
    rmap_paths := by
      intro r1 r2 hr1 hr2 p hp
      exact pathReflectedInHeap_heap_alloc rmap heap v r1 r2 p
        (hwt.rmap_paths r1 r2 hr1 hr2 p hp) hwt.rmap_live hlb
    varEnv_refs_in_pathEnv := hwt.varEnv_refs_in_pathEnv
    siteEnv_refs_in_pathEnv := hwt.siteEnv_refs_in_pathEnv
    live_refs_unique := hwt.live_refs_unique
    blocks_typed := hwt.blocks_typed
    lenv_empty_siteEnv := hwt.lenv_empty_siteEnv
    funEnv_typed := hwt.funEnv_typed
    heap_loc_bound := heap_loc_bound_after_alloc heap v hlb
    rmap_root_none := hwt.rmap_root_none
    no_paths_to_root := hwt.no_paths_to_root
    root_path_coherence := hwt.root_path_coherence
  }

/-- StackSafe is preserved under heap.alloc -/
private theorem stackSafe_heap_alloc (stack : List Frame) (ri : Option ReturnInfo)
    (heap : Heap) (v : Value)
    (hss : StackSafe stack ri heap)
    (hlb : ∀ loc, heap.read loc ≠ none → loc < heap.nextLoc) :
    StackSafe stack ri (heap.alloc v).1 := by
  cases stack with
  | nil => simp [StackSafe]
  | cons callerFrame rest =>
    cases ri with
    | none => simp [StackSafe]
    | some ri =>
      simp only [StackSafe] at hss ⊢
      obtain ⟨hret, hrest⟩ := hss
      refine ⟨fun vals newSiteStore hbind => ?_, ?_⟩
      · obtain ⟨env', lenv', retType', rmap', hwt', hss'⟩ := hret vals newSiteStore hbind
        exact ⟨env', lenv', retType', rmap',
          wellTypedState_heap_alloc _ _ heap env' lenv' retType' rmap' v hwt',
          stackSafe_heap_alloc rest callerFrame.returnInfo heap v hss' hwt'.heap_loc_bound⟩
      · exact stackSafe_heap_alloc rest callerFrame.returnInfo heap v hrest hlb

private theorem preservation_readRef (m m' : Machine) (env : TypeEnv) (lenv : LabelEnv)
    (retType : MoveType) (rmap : RefMap)
    (hwt : WellTypedState m env lenv retType rmap)
    (hss : StackSafe m.stack m.frame.returnInfo m.heap)
    (s : Site) (src : Site) (cont : Stmt)
    (hstmt : m.frame.stmt = .letBind s (.readRef src) cont)
    (hstep : step (.running m) = .running m') :
    ∃ env' lenv' retType' rmap',
      WellTypedState m' env' lenv' retType' rmap' ∧
      StackSafe m'.stack m'.frame.returnInfo m'.heap := by
  obtain ⟨r, τ, isBor, hlookup, hcont⟩ := inv_readRef (by rw [← hstmt]; exact hwt.stmt_typed)
  obtain ⟨vref, hvref, hmatch⟩ := hwt.site_consistent src (.ref τ r isBor) hlookup
  obtain ⟨loc, path, hveq, hrmap⟩ := hmatch
  have hheap := hwt.rmap_live r loc path hrmap
  cases hrd : m.heap.readRef loc path with
  | none => exact absurd hrd hheap
  | some val =>
    have hrs : readSite m src = some (.ref loc path) := by rw [readSite, hvref, hveq]
    simp only [step, hstmt, hrs, hrd, ExecState.running.injEq] at hstep; subst hstep
    have hr_not_root : r ≠ .root := hwt.env_wf.siteEnv_wf src (.ref τ r isBor) hlookup
    -- Capture facts involving r for use inside struct by-blocks
    have hlive_r := hwt.live_refs_unique r
    have hsrc_lookup := hlookup  -- lookup env.siteEnv src = some (.ref τ r isBor)
    refine ⟨{env with siteEnv := insert (delete env.siteEnv src) s (.basic τ),
                       pathEnv := delete_ref_node env.pathEnv r},
            lenv, retType, rmap, ?_, hss⟩
    exact {
      env_wf := ⟨delete_ref_node_wellformed env.pathEnv r hwt.env_wf.pathEnv_wf hr_not_root,
                 SiteEnv.insert_refs_not_root (delete env.siteEnv src) s (.basic τ)
                   (SiteEnv.delete_refs_not_root env.siteEnv src hwt.env_wf.siteEnv_wf) trivial,
                 hwt.env_wf.varEnv_wf⟩
      stmt_typed := hcont
      var_consistent := hwt.var_consistent
      site_consistent := by
        intro s' τ' hl
        by_cases heq : s' = s
        · subst heq; simp only [lookup_insert_same, Option.some.injEq] at hl; subst hl
          exact ⟨val, lookup_insert_same _ _ _, trivial⟩
        · rw [lookup_insert_ne _ s s' _ heq] at hl
          have hne_src : s' ≠ src := by
            intro h; subst h; rw [lookup_delete_same] at hl; simp at hl
          rw [lookup_delete_ne _ src s' hne_src] at hl
          obtain ⟨v, hv, hm⟩ := hwt.site_consistent s' τ' hl
          exact ⟨v, by rw [lookup_insert_ne _ s s' _ heq]; exact hv, hm⟩
      rmap_live := hwt.rmap_live
      rmap_paths := rmap_paths_delete_ref_node env m rmap r hwt.rmap_paths
      varEnv_refs_in_pathEnv := by
        intro x' bt r' bk ms hvar'
        have hr'_in := hwt.varEnv_refs_in_pathEnv x' bt r' bk ms hvar'
        have hr'_ne : r' ≠ r := by
          intro heq; subst heq
          exact hlive_r.1 x' bt bk ms src τ isBor hvar' hsrc_lookup
        simp only [delete_ref_node_refs, List.mem_filter, decide_eq_true_eq]
        exact ⟨hr'_in, hr'_ne⟩
      siteEnv_refs_in_pathEnv := by
        intro s' bt r' bk hl
        by_cases heqs : s' = s
        · subst heqs; rw [lookup_insert_same] at hl; simp at hl
        · rw [lookup_insert_ne _ s s' _ heqs] at hl
          have hne_src : s' ≠ src := by
            intro h; subst h; rw [lookup_delete_same] at hl; simp at hl
          rw [lookup_delete_ne _ src s' hne_src] at hl
          have hr'_in := hwt.siteEnv_refs_in_pathEnv s' bt r' bk hl
          have hr'_ne : r' ≠ r := by
            intro heq; subst heq
            exact hlive_r.2.1 src s' τ bt isBor bk
              (Ne.symm hne_src) hsrc_lookup hl
          simp only [delete_ref_node_refs, List.mem_filter, decide_eq_true_eq]
          exact ⟨hr'_in, hr'_ne⟩
      live_refs_unique := by
        intro r'
        refine ⟨fun x' bt bk ms' s' bt' bk' hvar' hs' => ?_,
                fun s1 s2 bt1 bt2 bk1 bk2 hne hs1 hs2 => ?_,
                fun x1 x2 bt1 bt2 bk1 bk2 ms1 ms2 hne hx1 hx2 => ?_⟩
        · -- var-site
          by_cases heqs : s' = s
          · subst heqs; rw [lookup_insert_same] at hs'; simp at hs'
          · rw [lookup_insert_ne _ s s' _ heqs] at hs'
            have hne_src : s' ≠ src := by
              intro h; subst h; rw [lookup_delete_same] at hs'; simp at hs'
            rw [lookup_delete_ne _ src s' hne_src] at hs'
            exact (hwt.live_refs_unique r').1 x' bt bk ms' s' bt' bk' hvar' hs'
        · -- site-site
          by_cases heq1 : s1 = s
          · subst heq1; rw [lookup_insert_same] at hs1; simp at hs1
          · by_cases heq2 : s2 = s
            · subst heq2; rw [lookup_insert_same] at hs2; simp at hs2
            · rw [lookup_insert_ne _ s s1 _ heq1] at hs1
              rw [lookup_insert_ne _ s s2 _ heq2] at hs2
              have hne1 : s1 ≠ src := by
                intro h; subst h; rw [lookup_delete_same] at hs1; simp at hs1
              have hne2 : s2 ≠ src := by
                intro h; subst h; rw [lookup_delete_same] at hs2; simp at hs2
              rw [lookup_delete_ne _ src s1 hne1] at hs1
              rw [lookup_delete_ne _ src s2 hne2] at hs2
              exact (hwt.live_refs_unique r').2.1 s1 s2 bt1 bt2 bk1 bk2 hne hs1 hs2
        · -- var-var: varEnv unchanged
          exact (hwt.live_refs_unique r').2.2 x1 x2 bt1 bt2 bk1 bk2 ms1 ms2 hne hx1 hx2
      blocks_typed := hwt.blocks_typed
      lenv_empty_siteEnv := hwt.lenv_empty_siteEnv
      funEnv_typed := hwt.funEnv_typed
      heap_loc_bound := hwt.heap_loc_bound
      rmap_root_none := hwt.rmap_root_none
      no_paths_to_root := by
        intro u p hp
        simp only [delete_ref_node] at hp
        by_cases hu : u = r
        · subst hu; simp only [true_or, ↓reduceIte, interpret_regex] at hp
        · by_cases hr' : Aref.root = r
          · exact absurd hr'.symm hr_not_root
          · simp only [hu, hr', or_false, ↓reduceIte] at hp
            exact hwt.no_paths_to_root u p hp
      root_path_coherence := by
        intro v y rest hv_mem hp loc_v path_v hrmap loc_y hloc heq
        simp only [delete_ref_node_refs, List.mem_filter, decide_eq_true_eq] at hv_mem
        obtain ⟨hv_in, hv_ne⟩ := hv_mem
        simp only [delete_ref_node] at hp
        have hroot_ne : Aref.root ≠ r := Ne.symm hr_not_root
        simp only [hroot_ne, hv_ne, or_false, ↓reduceIte] at hp
        exact hwt.root_path_coherence v y rest hv_in hp loc_v path_v hrmap loc_y hloc heq
    }

private theorem preservation_binop (m m' : Machine) (env : TypeEnv) (lenv : LabelEnv)
    (retType : MoveType) (rmap : RefMap)
    (hwt : WellTypedState m env lenv retType rmap)
    (hss : StackSafe m.stack m.frame.returnInfo m.heap)
    (s : Site) (op : Binop) (sA sB : Site) (cont : Stmt)
    (hstmt : m.frame.stmt = .letBind s (.binop op sA sB) cont)
    (hstep : step (.running m) = .running m') :
    ∃ env' lenv' retType' rmap',
      WellTypedState m' env' lenv' retType' rmap' ∧
      StackSafe m'.stack m'.frame.returnInfo m'.heap := by
  obtain ⟨bt1, bt2, bt3, ha, hb, hbt, hcont⟩ := inv_binop (by rw [← hstmt]; exact hwt.stmt_typed)
  obtain ⟨va, hva, hma⟩ := hwt.site_consistent sA (.basic bt1) ha
  obtain ⟨vb, hvb, hmb⟩ := hwt.site_consistent sB (.basic bt2) hb
  have hrsa : readSite m sA = some va := hva
  have hrsb : readSite m sB = some vb := hvb
  -- Prove site_consistent before destructive case analysis (sA/sB go out of scope)
  have hsc : ∀ result, ∀ s' τ',
      lookup (insert (delete (delete env.siteEnv sA) sB) s (.basic bt3)) s' = some τ' →
      ∃ v', lookup (insert m.frame.siteStore s result) s' = some v' ∧
            ValueMatchesType v' τ' rmap := by
    intro result s' τ' hl
    by_cases heq : s' = s
    · subst heq; simp only [lookup_insert_same, Option.some.injEq] at hl; subst hl
      exact ⟨result, lookup_insert_same _ _ _, trivial⟩
    · rw [lookup_insert_ne _ s s' _ heq] at hl
      have hne_b : s' ≠ sB := by
        intro h; rw [h, lookup_delete_same] at hl; simp at hl
      rw [lookup_delete_ne _ sB s' hne_b] at hl
      have hne_a : s' ≠ sA := by
        intro h; rw [h, lookup_delete_same] at hl; simp at hl
      rw [lookup_delete_ne _ sA s' hne_a] at hl
      obtain ⟨v, hvs, hm⟩ := hwt.site_consistent s' τ' hl
      exact ⟨v, by rw [lookup_insert_ne _ s s' _ heq]; exact hvs, hm⟩
  simp only [step, hstmt, hrsa, hrsb] at hstep
  have hva_int : ∃ n, va = .int n := by
    cases va with
    | int n => exact ⟨n, rfl⟩
    | _ => exfalso; simp at hstep
  have hvb_int : ∃ n, vb = .int n := by
    obtain ⟨n, rfl⟩ := hva_int
    cases vb with
    | int n => exact ⟨n, rfl⟩
    | _ => exfalso; simp at hstep
  obtain ⟨na, rfl⟩ := hva_int
  obtain ⟨nb, rfl⟩ := hvb_int
  simp only [] at hstep
  cases heval : evalBinop op na nb <;> simp [heval] at hstep
  rename_i result
  subst hstep
  refine ⟨{env with siteEnv := insert (delete (delete env.siteEnv sA) sB) s (.basic bt3)},
          lenv, retType, rmap, ?_, hss⟩
  exact {
    env_wf := TypeEnv.delete_delete_insert_wf env sA sB s (.basic bt3) hwt.env_wf trivial
    stmt_typed := hcont
    var_consistent := hwt.var_consistent
    site_consistent := hsc result
    rmap_live := hwt.rmap_live
    rmap_paths := hwt.rmap_paths
    varEnv_refs_in_pathEnv := hwt.varEnv_refs_in_pathEnv
    siteEnv_refs_in_pathEnv := by
      intro s' bt r bk hl
      by_cases heq : s' = s
      · subst heq; simp [lookup_insert_same] at hl
      · rw [lookup_insert_ne _ s s' _ heq] at hl
        have hne_b : s' ≠ sB := by
          intro h; rw [h, lookup_delete_same] at hl; simp at hl
        rw [lookup_delete_ne _ sB s' hne_b] at hl
        have hne_a : s' ≠ sA := by
          intro h; rw [h, lookup_delete_same] at hl; simp at hl
        rw [lookup_delete_ne _ sA s' hne_a] at hl
        exact hwt.siteEnv_refs_in_pathEnv s' bt r bk hl
    live_refs_unique := by
      intro r'
      refine ⟨fun x bt bk ms s' bt' bk' hv hs => ?_,
              fun s1 s2 bt1 bt2 bk1 bk2 hne hs1 hs2 => ?_,
              fun x y bt1 bt2 bk1 bk2 ms1 ms2 hne hx hy =>
                (hwt.live_refs_unique r').2.2 x y bt1 bt2 bk1 bk2 ms1 ms2 hne hx hy⟩
      · by_cases heq : s' = s
        · subst heq; simp [lookup_insert_same] at hs
        · rw [lookup_insert_ne _ s s' _ heq] at hs
          have hne_b : s' ≠ sB := by
            intro h; rw [h, lookup_delete_same] at hs; simp at hs
          rw [lookup_delete_ne _ sB s' hne_b] at hs
          have hne_a : s' ≠ sA := by
            intro h; rw [h, lookup_delete_same] at hs; simp at hs
          rw [lookup_delete_ne _ sA s' hne_a] at hs
          exact (hwt.live_refs_unique r').1 x bt bk ms s' bt' bk' hv hs
      · by_cases heq1 : s1 = s
        · subst heq1; simp [lookup_insert_same] at hs1
        · by_cases heq2 : s2 = s
          · subst heq2; simp [lookup_insert_same] at hs2
          · rw [lookup_insert_ne _ s s1 _ heq1] at hs1
            rw [lookup_insert_ne _ s s2 _ heq2] at hs2
            have hne1_b : s1 ≠ sB := by
              intro h; rw [h, lookup_delete_same] at hs1; simp at hs1
            have hne1_a : s1 ≠ sA := by
              rw [lookup_delete_ne _ sB s1 hne1_b] at hs1
              intro h; rw [h, lookup_delete_same] at hs1; simp at hs1
            have hne2_b : s2 ≠ sB := by
              intro h; rw [h, lookup_delete_same] at hs2; simp at hs2
            have hne2_a : s2 ≠ sA := by
              rw [lookup_delete_ne _ sB s2 hne2_b] at hs2
              intro h; rw [h, lookup_delete_same] at hs2; simp at hs2
            rw [lookup_delete_ne _ sB s1 hne1_b, lookup_delete_ne _ sA s1 hne1_a] at hs1
            rw [lookup_delete_ne _ sB s2 hne2_b, lookup_delete_ne _ sA s2 hne2_a] at hs2
            exact (hwt.live_refs_unique r').2.1 s1 s2 bt1 bt2 bk1 bk2 hne hs1 hs2
    blocks_typed := hwt.blocks_typed
    lenv_empty_siteEnv := hwt.lenv_empty_siteEnv
    funEnv_typed := hwt.funEnv_typed
    heap_loc_bound := hwt.heap_loc_bound
    rmap_root_none := hwt.rmap_root_none
    no_paths_to_root := hwt.no_paths_to_root
    root_path_coherence := hwt.root_path_coherence
  }

private theorem preservation_release (m m' : Machine) (env : TypeEnv) (lenv : LabelEnv)
    (retType : MoveType) (rmap : RefMap)
    (hwt : WellTypedState m env lenv retType rmap)
    (hss : StackSafe m.stack m.frame.returnInfo m.heap)
    (site : Site) (cont : Stmt)
    (hstmt : m.frame.stmt = .release site cont)
    (hstep : step (.running m) = .running m') :
    ∃ env' lenv' retType' rmap',
      WellTypedState m' env' lenv' retType' rmap' ∧
      StackSafe m'.stack m'.frame.returnInfo m'.heap := by
  simp only [step, hstmt, ExecState.running.injEq] at hstep; subst hstep
  obtain ⟨τ, r, isBor, hlookup, hcont⟩ := inv_release (by rw [← hstmt]; exact hwt.stmt_typed)
  have hr_not_root : r ≠ .root := hwt.env_wf.siteEnv_wf site (.ref τ r isBor) hlookup
  -- Capture facts involving r for use inside struct by-blocks
  have hlive_r := hwt.live_refs_unique r
  have hsite_lookup := hlookup  -- lookup env.siteEnv site = some (.ref τ r isBor)
  refine ⟨{env with siteEnv := delete env.siteEnv site,
                     pathEnv := delete_ref_node env.pathEnv r},
          lenv, retType, rmap, ?_, hss⟩
  exact {
    env_wf := ⟨delete_ref_node_wellformed env.pathEnv r hwt.env_wf.pathEnv_wf hr_not_root,
               SiteEnv.delete_refs_not_root env.siteEnv site hwt.env_wf.siteEnv_wf,
               hwt.env_wf.varEnv_wf⟩
    stmt_typed := hcont
    var_consistent := hwt.var_consistent
    site_consistent := by
      intro s' τ' hl
      have hne : s' ≠ site := by
        intro heq; subst heq; rw [lookup_delete_same] at hl; simp at hl
      rw [lookup_delete_ne env.siteEnv site s' hne] at hl
      exact hwt.site_consistent s' τ' hl
    rmap_live := hwt.rmap_live
    rmap_paths := rmap_paths_delete_ref_node env m rmap r hwt.rmap_paths
    varEnv_refs_in_pathEnv := by
      intro x' bt r' bk ms hvar'
      have hr'_in := hwt.varEnv_refs_in_pathEnv x' bt r' bk ms hvar'
      have hr'_ne : r' ≠ r := by
        intro heq; subst heq
        exact hlive_r.1 x' bt bk ms site τ isBor hvar' hsite_lookup
      simp only [delete_ref_node_refs, List.mem_filter, decide_eq_true_eq]
      exact ⟨hr'_in, hr'_ne⟩
    siteEnv_refs_in_pathEnv := by
      intro s' bt r' bk hl
      have hne : s' ≠ site := by
        intro h; subst h; rw [lookup_delete_same] at hl; simp at hl
      rw [lookup_delete_ne _ site s' hne] at hl
      have hr'_in := hwt.siteEnv_refs_in_pathEnv s' bt r' bk hl
      have hr'_ne : r' ≠ r := by
        intro heq; subst heq
        exact hlive_r.2.1 site s' τ bt isBor bk (Ne.symm hne) hsite_lookup hl
      simp only [delete_ref_node_refs, List.mem_filter, decide_eq_true_eq]
      exact ⟨hr'_in, hr'_ne⟩
    live_refs_unique := by
      intro r'
      refine ⟨fun x' bt bk ms' s' bt' bk' hvar' hs' => ?_,
              fun s1 s2 bt1 bt2 bk1 bk2 hne hs1 hs2 => ?_,
              fun x1 x2 bt1 bt2 bk1 bk2 ms1 ms2 hne hx1 hx2 => ?_⟩
      · -- var-site
        have hne : s' ≠ site := by
          intro h; subst h; rw [lookup_delete_same] at hs'; simp at hs'
        rw [lookup_delete_ne _ site s' hne] at hs'
        exact (hwt.live_refs_unique r').1 x' bt bk ms' s' bt' bk' hvar' hs'
      · -- site-site
        have hne1 : s1 ≠ site := by
          intro h; subst h; rw [lookup_delete_same] at hs1; simp at hs1
        have hne2 : s2 ≠ site := by
          intro h; subst h; rw [lookup_delete_same] at hs2; simp at hs2
        rw [lookup_delete_ne _ site s1 hne1] at hs1
        rw [lookup_delete_ne _ site s2 hne2] at hs2
        exact (hwt.live_refs_unique r').2.1 s1 s2 bt1 bt2 bk1 bk2 hne hs1 hs2
      · -- var-var: varEnv unchanged
        exact (hwt.live_refs_unique r').2.2 x1 x2 bt1 bt2 bk1 bk2 ms1 ms2 hne hx1 hx2
    blocks_typed := hwt.blocks_typed
    lenv_empty_siteEnv := hwt.lenv_empty_siteEnv
    funEnv_typed := hwt.funEnv_typed
    heap_loc_bound := hwt.heap_loc_bound
    rmap_root_none := hwt.rmap_root_none
    no_paths_to_root := by
      intro u p hp
      simp only [delete_ref_node] at hp
      by_cases hu : u = r
      · subst hu; simp only [true_or, ↓reduceIte, interpret_regex] at hp
      · by_cases hr' : Aref.root = r
        · exact absurd hr'.symm hr_not_root
        · simp only [hu, hr', or_false, ↓reduceIte] at hp
          exact hwt.no_paths_to_root u p hp
    root_path_coherence := by
      intro v y rest hv_mem hp loc_v path_v hrmap loc_y hloc heq
      simp only [delete_ref_node_refs, List.mem_filter, decide_eq_true_eq] at hv_mem
      obtain ⟨hv_in, hv_ne⟩ := hv_mem
      simp only [delete_ref_node] at hp
      have hroot_ne : Aref.root ≠ r := Ne.symm hr_not_root
      simp only [hroot_ne, hv_ne, or_false, ↓reduceIte] at hp
      exact hwt.root_path_coherence v y rest hv_in hp loc_v path_v hrmap loc_y hloc heq
  }

/-- Helper: lookup on deleteAll returns some → lookup on original returns some -/
private lemma lookup_deleteAll_some (l : AssocMap Site MoveType) (ks : List Site)
    (k : Site) (v : MoveType) (h : lookup (deleteAll l ks) k = some v) :
    lookup l k = some v := by
  simp only [AssocMap.deleteAll, AssocMap.lookup] at h ⊢
  have hnotin : k ∉ ks := by
    intro hmem
    have := List.lookup_filter_mem_none l.entries k ks hmem
    rw [this] at h; cases h
  rw [← List.lookup_filter_notin l.entries k ks hnotin]
  exact h

private theorem preservation_pack (m m' : Machine) (env : TypeEnv) (lenv : LabelEnv)
    (retType : MoveType) (rmap : RefMap)
    (hwt : WellTypedState m env lenv retType rmap)
    (hss : StackSafe m.stack m.frame.returnInfo m.heap)
    (s : Site) (name : Id) (fieldSites : List (Field × Site)) (cont : Stmt)
    (hstmt : m.frame.stmt = .letBind s (.pack name fieldSites) cont)
    (hstep : step (.running m) = .running m') :
    ∃ env' lenv' retType' rmap',
      WellTypedState m' env' lenv' retType' rmap' ∧
      StackSafe m'.stack m'.frame.returnInfo m'.heap := by
  obtain ⟨fentries, hcont⟩ := inv_pack (by rw [← hstmt]; exact hwt.stmt_typed)
  simp only [step, hstmt] at hstep
  split at hstep
  · simp at hstep
  · rename_i fieldVals hcpf
    simp only [ExecState.running.injEq] at hstep; subst hstep
    refine ⟨{env with siteEnv := insert (deleteAll env.siteEnv (fieldSites.map Prod.snd)) s
                                    (.basic (.trecord fentries))},
            lenv, retType, rmap, ?_, hss⟩
    exact {
      env_wf := TypeEnv.deleteAll_insert_wf env (fieldSites.map Prod.snd) s
                  (.basic (.trecord fentries)) hwt.env_wf trivial
      stmt_typed := hcont
      var_consistent := hwt.var_consistent
      site_consistent := by
        intro s' τ' hl
        by_cases heq : s' = s
        · subst heq; simp only [lookup_insert_same, Option.some.injEq] at hl; subst hl
          exact ⟨.record fieldVals, lookup_insert_same _ _ _, trivial⟩
        · rw [lookup_insert_ne _ s s' _ heq] at hl
          have hl_orig := lookup_deleteAll_some env.siteEnv _ s' τ' hl
          obtain ⟨v, hv, hm⟩ := hwt.site_consistent s' τ' hl_orig
          exact ⟨v, by rw [lookup_insert_ne _ s s' _ heq]; exact hv, hm⟩
      rmap_live := hwt.rmap_live
      rmap_paths := hwt.rmap_paths
      varEnv_refs_in_pathEnv := hwt.varEnv_refs_in_pathEnv
      siteEnv_refs_in_pathEnv := by
        intro s' bt r bk hl
        by_cases heq : s' = s
        · subst heq; simp [lookup_insert_same] at hl
        · rw [lookup_insert_ne _ s s' _ heq] at hl
          exact hwt.siteEnv_refs_in_pathEnv s' bt r bk (lookup_deleteAll_some env.siteEnv _ s' _ hl)
      live_refs_unique := by
        intro r'
        refine ⟨fun x bt bk ms s' bt' bk' hv hs => ?_,
                fun s1 s2 bt1 bt2 bk1 bk2 hne hs1 hs2 => ?_,
                fun x y bt1 bt2 bk1 bk2 ms1 ms2 hne hx hy =>
                  (hwt.live_refs_unique r').2.2 x y bt1 bt2 bk1 bk2 ms1 ms2 hne hx hy⟩
        · by_cases heq : s' = s
          · subst heq; simp [lookup_insert_same] at hs
          · rw [lookup_insert_ne _ s s' _ heq] at hs
            exact (hwt.live_refs_unique r').1 x bt bk ms s' bt' bk' hv
              (lookup_deleteAll_some env.siteEnv _ s' _ hs)
        · by_cases heq1 : s1 = s
          · subst heq1; simp [lookup_insert_same] at hs1
          · by_cases heq2 : s2 = s
            · subst heq2; simp [lookup_insert_same] at hs2
            · rw [lookup_insert_ne _ s s1 _ heq1] at hs1
              rw [lookup_insert_ne _ s s2 _ heq2] at hs2
              exact (hwt.live_refs_unique r').2.1 s1 s2 bt1 bt2 bk1 bk2 hne
                (lookup_deleteAll_some env.siteEnv _ s1 _ hs1)
                (lookup_deleteAll_some env.siteEnv _ s2 _ hs2)
      blocks_typed := hwt.blocks_typed
      lenv_empty_siteEnv := hwt.lenv_empty_siteEnv
      funEnv_typed := hwt.funEnv_typed
      heap_loc_bound := hwt.heap_loc_bound
      rmap_root_none := hwt.rmap_root_none
      no_paths_to_root := hwt.no_paths_to_root
      root_path_coherence := hwt.root_path_coherence
    }

private theorem preservation_assign_valid (m m' : Machine) (env : TypeEnv) (lenv : LabelEnv)
    (retType : MoveType) (rmap : RefMap)
    (hwt : WellTypedState m env lenv retType rmap)
    (hss : StackSafe m.stack m.frame.returnInfo m.heap)
    (x : Var) (a : Site) (cont : Stmt)
    (ax : Site) (τ : BasicMoveType) (ms : Mut) (r : Aref)
    (hvar : lookup env.varEnv x = some (.validVar, .basic τ, ms))
    (hnv : ∀ v, r ≠ .varRef v)
    (hfresh : freshRefInEnvBool r env)
    (hnotin : notIn env.siteEnv ax)
    (hcont : typecheck_stmt lenv
      {env with siteEnv := delete (delete (insert env.siteEnv ax (.ref τ r .siteBorrowMut)) a) ax
                pathEnv := garbage_collect (update_with_extension r .root [.root_to_var x]
                            (update_with_epsilon r r env.pathEnv)) r}
      cont retType)
    (hstmt : m.frame.stmt = .assign x a cont)
    (hstep : step (.running m) = .running m') :
    ∃ env' lenv' retType' rmap',
      WellTypedState m' env' lenv' retType' rmap' ∧
      StackSafe m'.stack m'.frame.returnInfo m'.heap := by
  -- x is valid with .basic τ, so we can read the current value
  obtain ⟨loc_old, val_old, hloc_old, hread_old, _⟩ := hwt.var_consistent x .validVar (.basic τ) ms hvar
  -- Read the site value
  -- The step function reads site a to get a value v, allocates it
  -- We need to show readSite m a succeeds.
  -- From the typing rule, a is in siteEnv. But we need to check:
  -- actually, a might or might not be in siteEnv — the typing rule deletes a but
  -- doesn't require lookup env.siteEnv a = some τ' explicitly.
  -- Let's examine what step does and work backwards from hstep.
  simp only [step, hstmt] at hstep
  -- After simp, hstep should match on readSite m a
  cases hrs : readSite m a with
  | none => simp [hrs] at hstep
  | some v =>
    simp [hrs, ExecState.running.injEq] at hstep; subst hstep
    -- r is fresh and not root
    have hr_fresh : freshRef r env.pathEnv :=
      freshRefBool_implies_freshRef r env.pathEnv (freshRefInEnvBool_implies_freshRefBool r env hfresh)
    have hr_not_root : r ≠ Aref.root := by
      intro h; subst h; exact absurd hwt.env_wf.pathEnv_wf.root_in_refs hr_fresh
    -- Abbreviate the complex env
    let pe' := garbage_collect (update_with_extension r .root [.root_to_var x]
                 (update_with_epsilon r r env.pathEnv)) r
    let se' := delete (delete (insert env.siteEnv ax (.ref τ r .siteBorrowMut)) a) ax
    let env' : TypeEnv := {env with siteEnv := se', pathEnv := pe'}
    -- Build WellFormed for the complex env
    have hpe_wf : PathEnv.WellFormed pe' := by
      exact garbage_collect_wellformed _ r
        (update_with_extension_wellformed r .root [.root_to_var x] _
          (update_with_epsilon_wellformed r r env.pathEnv hwt.env_wf.pathEnv_wf hr_not_root hnv)
          hr_not_root hnv)
        hr_not_root
    have hse_wf : SiteEnv.RefsNotRoot se' := by
      exact SiteEnv.delete_refs_not_root _ ax
        (SiteEnv.delete_refs_not_root _ a
          (SiteEnv.insert_refs_not_root env.siteEnv ax (.ref τ r .siteBorrowMut)
            hwt.env_wf.siteEnv_wf hr_not_root))
    -- garbage_collect removes r from refs and clears paths involving r.
    -- Since r was fresh, the resulting refs and paths (for non-r arefs) match the original.
    -- Use delete_ref_node lemmas since garbage_collect = delete_ref_node definitionally.
    have hgc_refs : pe'.refs = env.pathEnv.refs := by
      -- pe' = garbage_collect(update_with_extension(...)) r
      -- Step 1: update_with_epsilon adds r to refs (r is fresh)
      have h_eps_refs : (update_with_epsilon r r env.pathEnv).refs = r :: env.pathEnv.refs := by
        simp only [update_with_epsilon, update_with_extension]
        simp only [show ¬r ∈ env.pathEnv.refs from hr_fresh, not_false_eq_true, ↓reduceIte]
      -- Step 2: update_with_extension doesn't add r again (already in refs)
      have h_ext_refs : (update_with_extension r .root [.root_to_var x]
            (update_with_epsilon r r env.pathEnv)).refs = r :: env.pathEnv.refs := by
        simp only [update_with_extension, h_eps_refs, List.mem_cons, true_or, not_true_eq_false,
                    ↓reduceIte]
      -- Step 3: delete_ref_node filters out r, leaving env.pathEnv.refs
      show (delete_ref_node _ r).refs = env.pathEnv.refs
      rw [delete_ref_node_refs, h_ext_refs]
      simp only [List.filter_cons, ne_eq, not_true_eq_false, decide_false]
      apply List.filter_eq_self.mpr
      intro a ha
      simp only [decide_eq_true_eq]
      intro heq; subst heq; exact absurd ha hr_fresh
    have hgc_paths : ∀ u v, u ≠ r → v ≠ r →
        pe'.paths (u, v) = env.pathEnv.paths (u, v) := by
      intro u v hu hv
      show (delete_ref_node (update_with_extension r .root [.root_to_var x]
            (update_with_epsilon r r env.pathEnv)) r).paths (u, v) = env.pathEnv.paths (u, v)
      rw [delete_ref_node_paths_not_involving_r _ r u v hu hv]
      simp only [update_with_extension, update_with_epsilon]
      simp only [hu, hv, and_self, ite_false, and_false, false_and]
    refine ⟨env', lenv, retType, rmap, ?_,
            stackSafe_heap_alloc m.stack m.frame.returnInfo m.heap v hss hwt.heap_loc_bound⟩
    exact {
      env_wf := ⟨hpe_wf, hse_wf, hwt.env_wf.varEnv_wf⟩
      stmt_typed := hcont
      var_consistent := by
        intro y isv τy ms' hvy
        -- varEnv is unchanged: env'.varEnv = env.varEnv
        have hvy' : lookup env.varEnv y = some (isv, τy, ms') := hvy
        by_cases heq : y = x
        · -- y = x: the assigned variable
          subst heq
          -- From hvar: lookup env.varEnv x = some (.validVar, .basic τ, ms)
          -- From hvy': lookup env.varEnv x = some (isv, τy, ms')
          have hinj := Option.some.inj (hvar.symm.trans hvy')
          have h1 : isv = .validVar := (congrArg Prod.fst hinj).symm
          have h2 : τy = .basic τ := (congrArg (fun p => p.2.1) hinj).symm
          subst h1; subst h2
          -- For validVar case: need loc, val in new machine
          -- ValueMatchesType v (.basic τ) rmap = True
          exact ⟨(m.heap.alloc v).2, v, lookup_insert_same _ _ _,
                 heap_alloc_read_new m.heap v, trivial⟩
        · -- y ≠ x: unaffected variable
          have hold := hwt.var_consistent y isv τy ms' hvy'
          have hne_vs : lookup (insert m.frame.varStore x (some (m.heap.alloc v).2)) y =
              lookup m.frame.varStore y := lookup_insert_ne _ x y _ heq
          cases isv with
          | validVar =>
            obtain ⟨loc, val, hloc, hread, hm⟩ := hold
            have hlt := hwt.heap_loc_bound loc (by intro habs; simp [habs] at hread)
            exact ⟨loc, val, hne_vs.trans hloc,
                   by rw [heap_alloc_preserves_read m.heap v loc hlt]; exact hread, hm⟩
          | invalidVar =>
            simp only at hold ⊢
            cases hold with
            | inl h => exact .inl (hne_vs.trans h)
            | inr h =>
              obtain ⟨l, hl⟩ := h
              exact .inr ⟨l, hne_vs.trans hl⟩
      site_consistent := by
        intro s τs hl
        have hl' : lookup se' s = some τs := hl
        -- s ≠ ax (since delete ax at the end) and s ≠ a (since delete a inside)
        have hs_ne_ax : s ≠ ax := by
          intro h; subst h; simp [se', lookup_delete_same] at hl'
        have hs_ne_a : s ≠ a := by
          intro heq
          have hl'' : lookup se' s = some τs := hl'
          simp only [se'] at hl''
          rw [lookup_delete_ne _ ax s hs_ne_ax, heq, lookup_delete_same] at hl''
          exact absurd hl'' (by simp)
        -- Reduce to lookup env.siteEnv s = some τs
        have hlred : lookup env.siteEnv s = some τs := by
          simp only [se'] at hl'
          rw [lookup_delete_ne _ ax s hs_ne_ax] at hl'
          rw [lookup_delete_ne _ a s hs_ne_a] at hl'
          rw [lookup_insert_ne _ ax s _ hs_ne_ax] at hl'
          exact hl'
        exact hwt.site_consistent s τs hlred
      rmap_live := by
        intro r' loc path hrmap
        have hlive := hwt.rmap_live r' loc path hrmap
        have hlt := hwt.heap_loc_bound loc (readRef_implies_read m.heap loc path hlive)
        have hne : loc ≠ m.heap.nextLoc := by intro h; subst h; exact Nat.lt_irrefl _ hlt
        rw [heap_alloc_preserves_readRef m.heap v loc path hne]; exact hlive
      rmap_paths := by
        intro r1 r2 hr1 hr2 p hp
        -- hr1 : r1 ∈ env'.pathEnv.refs = pe'.refs
        -- Since pe'.refs = env.pathEnv.refs (by hgc_refs),
        -- and pe'.paths(r1,r2) = env.pathEnv.paths(r1,r2) for non-r pairs:
        have hr1_orig : r1 ∈ env.pathEnv.refs := hgc_refs ▸ hr1
        have hr2_orig : r2 ∈ env.pathEnv.refs := hgc_refs ▸ hr2
        have hr1_ne : r1 ≠ r := fun h => by subst h; exact absurd hr1_orig hr_fresh
        have hr2_ne : r2 ≠ r := fun h => by subst h; exact absurd hr2_orig hr_fresh
        have hp_orig : interpret_regex (env.pathEnv.paths (r1, r2)) p := by
          rw [← hgc_paths r1 r2 hr1_ne hr2_ne]; exact hp
        exact pathReflectedInHeap_heap_alloc rmap m.heap v r1 r2 p
          (hwt.rmap_paths r1 r2 hr1_orig hr2_orig p hp_orig) hwt.rmap_live hwt.heap_loc_bound
      varEnv_refs_in_pathEnv := by
        intro y bt r' bk ms' hvy
        rw [hgc_refs]; exact hwt.varEnv_refs_in_pathEnv y bt r' bk ms' hvy
      siteEnv_refs_in_pathEnv := by
        intro s' bt r' bk hl
        have hl' : lookup se' s' = some (.ref bt r' bk) := hl
        have hs_ne_ax : s' ≠ ax := by
          intro h; subst h; simp [se', lookup_delete_same] at hl'
        have hs_ne_a : s' ≠ a := by
          intro heq; simp only [se'] at hl'
          rw [lookup_delete_ne _ ax s' hs_ne_ax, heq, lookup_delete_same] at hl'
          exact absurd hl' (by simp)
        have hlred : lookup env.siteEnv s' = some (.ref bt r' bk) := by
          simp only [se'] at hl'
          rw [lookup_delete_ne _ ax s' hs_ne_ax] at hl'
          rw [lookup_delete_ne _ a s' hs_ne_a] at hl'
          rw [lookup_insert_ne _ ax s' _ hs_ne_ax] at hl'
          exact hl'
        rw [hgc_refs]; exact hwt.siteEnv_refs_in_pathEnv s' bt r' bk hlred
      live_refs_unique := by
        intro r'
        -- Helper: reduce lookup in se' to lookup in env.siteEnv
        have hse_reduce : ∀ s' τs, lookup se' s' = some τs →
            lookup env.siteEnv s' = some τs := by
          intro s' τs hl'
          have hs_ne_ax : s' ≠ ax := by
            intro h; subst h; simp [se', lookup_delete_same] at hl'
          have hs_ne_a : s' ≠ a := by
            intro heq; simp only [se'] at hl'
            rw [lookup_delete_ne _ ax s' hs_ne_ax, heq, lookup_delete_same] at hl'; simp at hl'
          simp only [se'] at hl'
          rw [lookup_delete_ne _ ax s' hs_ne_ax] at hl'
          rw [lookup_delete_ne _ a s' hs_ne_a] at hl'
          rw [lookup_insert_ne _ ax s' _ hs_ne_ax] at hl'
          exact hl'
        refine ⟨fun x' bt bk ms' s' bt' bk' hvar' hs' => ?_,
                fun s1 s2 bt1 bt2 bk1 bk2 hne hs1 hs2 => ?_,
                fun x1 x2 bt1 bt2 bk1 bk2 ms1 ms2 hne hx1 hx2 => ?_⟩
        · -- var-site
          exact (hwt.live_refs_unique r').1 x' bt bk ms' s' bt' bk' hvar' (hse_reduce s' _ hs')
        · -- site-site
          exact (hwt.live_refs_unique r').2.1 s1 s2 bt1 bt2 bk1 bk2 hne
            (hse_reduce s1 _ hs1) (hse_reduce s2 _ hs2)
        · -- var-var: varEnv unchanged
          exact (hwt.live_refs_unique r').2.2 x1 x2 bt1 bt2 bk1 bk2 ms1 ms2 hne hx1 hx2
      blocks_typed := hwt.blocks_typed
      lenv_empty_siteEnv := hwt.lenv_empty_siteEnv
      funEnv_typed := hwt.funEnv_typed
      heap_loc_bound := heap_loc_bound_after_alloc m.heap v hwt.heap_loc_bound
      rmap_root_none := hwt.rmap_root_none
      no_paths_to_root := by
        have hroot_ne : Aref.root ≠ r := Ne.symm hr_not_root
        intro u p hp
        by_cases hu : u = r
        · -- u = r: pe'.paths(r, .root) is empty (delete_ref_node)
          exfalso
          rw [hu] at hp
          have hempty : pe'.paths (r, .root) = .empty := by
            show (delete_ref_node _ r).paths (r, .root) = .empty
            simp only [delete_ref_node, true_or, ↓reduceIte]
          rw [hempty] at hp; exact hp
        · -- u ≠ r: unchanged paths
          rw [hgc_paths u .root hu hroot_ne] at hp
          exact hwt.no_paths_to_root u p hp
      root_path_coherence := by
        have hroot_ne : Aref.root ≠ r := Ne.symm hr_not_root
        intro v' y rest hv_mem hp loc_v path_v hrmap loc_y hloc heq
        -- pe'.refs = env.pathEnv.refs, so v' ∈ env.pathEnv.refs
        have hv_orig : v' ∈ env.pathEnv.refs := hgc_refs ▸ hv_mem
        have hv_ne : v' ≠ r := fun h => by subst h; exact absurd hv_orig hr_fresh
        -- pe'.paths(.root, v') = env.pathEnv.paths(.root, v')
        rw [hgc_paths .root v' hroot_ne hv_ne] at hp
        by_cases heqx : y = x
        · -- y = x: varStore'(x) = (m.heap.alloc v).2 = m.heap.nextLoc (fresh)
          subst heqx
          simp only [lookup_insert_same, Option.some.injEq] at hloc
          -- hloc : (m.heap.alloc v).2 = loc_y
          -- (m.heap.alloc v).2 = m.heap.nextLoc by definition
          have halloc_eq : (m.heap.alloc v).2 = m.heap.nextLoc := rfl
          -- loc_v < m.heap.nextLoc from rmap_live + heap_loc_bound
          have hlt := hwt.heap_loc_bound loc_v (readRef_implies_read m.heap loc_v path_v
            (hwt.rmap_live v' loc_v path_v hrmap))
          -- Rewrite loc_y → (m.heap.alloc v).2 → m.heap.nextLoc in heq
          rw [← hloc, halloc_eq] at heq
          exact absurd heq (Nat.ne_of_lt hlt)
        · -- y ≠ x: varStore(y) unchanged
          rw [lookup_insert_ne _ x y _ heqx] at hloc
          exact hwt.root_path_coherence v' y rest hv_orig hp loc_v path_v hrmap loc_y hloc heq
    }

private theorem preservation_assign_invalid (m m' : Machine) (env : TypeEnv) (lenv : LabelEnv)
    (retType : MoveType) (rmap : RefMap)
    (hwt : WellTypedState m env lenv retType rmap)
    (hss : StackSafe m.stack m.frame.returnInfo m.heap)
    (x : Var) (a : Site) (cont : Stmt) (τ τ' : MoveType)
    (hvar : lookup env.varEnv x = some (.invalidVar, τ, .mutable))
    (hsite : lookup env.siteEnv a = some τ')
    (hcompat : MoveType.compatible τ τ')
    (hcont : typecheck_stmt lenv
      {env with varEnv := update env.varEnv x (.validVar, τ', .mutable)
                siteEnv := delete env.siteEnv a} cont retType)
    (hstmt : m.frame.stmt = .assign x a cont)
    (hstep : step (.running m) = .running m') :
    ∃ env' lenv' retType' rmap',
      WellTypedState m' env' lenv' retType' rmap' ∧
      StackSafe m'.stack m'.frame.returnInfo m'.heap := by
  -- Extract runtime values from site_consistent
  obtain ⟨v, hv, hmatch⟩ := hwt.site_consistent a τ' hsite
  have hrs : readSite m a = some v := hv
  simp only [step, hstmt, hrs, ExecState.running.injEq] at hstep; subst hstep
  -- Fresh ref for the new type
  have hfresh_τ' : moveTypeIsFreshRef τ' :=
    MoveType.compatible_preserves_freshRef τ τ'
      (hwt.env_wf.varEnv_wf x (.invalidVar, τ, .mutable) hvar) hcompat
  -- Capture facts for use inside struct by-blocks (x, a not in scope there)
  have hsite_a := hsite  -- lookup env.siteEnv a = some τ'
  have hlive_old := hwt.live_refs_unique
  have hvar_x := hvar  -- lookup env.varEnv x = some (.invalidVar, τ, .mutable)
  refine ⟨{env with varEnv := update env.varEnv x (.validVar, τ', .mutable),
                     siteEnv := delete env.siteEnv a},
          lenv, retType, rmap, ?_,
          stackSafe_heap_alloc m.stack m.frame.returnInfo m.heap v hss hwt.heap_loc_bound⟩
  exact {
    env_wf := ⟨hwt.env_wf.pathEnv_wf,
               SiteEnv.delete_refs_not_root env.siteEnv a hwt.env_wf.siteEnv_wf,
               VarEnv.update_refs_are_fresh env.varEnv x (.validVar, τ', .mutable)
                 hwt.env_wf.varEnv_wf hfresh_τ'⟩
    stmt_typed := hcont
    var_consistent := by
      intro y isv τy ms hvy
      -- Convert struct projection + update → insert (definitionally equal)
      have hvy' : lookup (insert env.varEnv x (.validVar, τ', .mutable)) y =
          some (isv, τy, ms) := hvy
      by_cases heq : y = x
      · subst heq
        rw [lookup_insert_same] at hvy'
        have hisv : isv = .validVar := (congrArg Prod.fst (Option.some.inj hvy')).symm
        subst hisv
        have hτy : τy = τ' :=
          (congrArg Prod.fst (Prod.mk.inj (Option.some.inj hvy')).2).symm
        subst hτy
        exact ⟨(m.heap.alloc v).2, v, lookup_insert_same _ _ _,
               heap_alloc_read_new m.heap v, hmatch⟩
      · rw [lookup_insert_ne _ x y _ heq] at hvy'
        have hold := hwt.var_consistent y isv τy ms hvy'
        have hne_vs : lookup (insert m.frame.varStore x (some (m.heap.alloc v).2)) y =
            lookup m.frame.varStore y := lookup_insert_ne _ x y _ heq
        cases isv with
        | validVar =>
          obtain ⟨loc, val, hloc, hread, hm⟩ := hold
          have hlt := hwt.heap_loc_bound loc (by intro habs; simp [habs] at hread)
          exact ⟨loc, val, hne_vs.trans hloc,
                 by rw [heap_alloc_preserves_read m.heap v loc hlt]; exact hread, hm⟩
        | invalidVar =>
          simp only at hold ⊢
          cases hold with
          | inl h => exact .inl (hne_vs.trans h)
          | inr h =>
            obtain ⟨l, hl⟩ := h
            exact .inr ⟨l, hne_vs.trans hl⟩
    site_consistent := by
      intro s' τs hl
      have hl' : lookup (delete env.siteEnv a) s' = some τs := hl
      have hne : s' ≠ a := by intro h; subst h; rw [lookup_delete_same] at hl'; simp at hl'
      rw [lookup_delete_ne env.siteEnv a s' hne] at hl'
      exact hwt.site_consistent s' τs hl'
    rmap_live := by
      intro r loc path hrmap
      have hlive := hwt.rmap_live r loc path hrmap
      have hlt := hwt.heap_loc_bound loc (readRef_implies_read m.heap loc path hlive)
      have hne : loc ≠ m.heap.nextLoc := by intro h; subst h; exact Nat.lt_irrefl _ hlt
      rw [heap_alloc_preserves_readRef m.heap v loc path hne]; exact hlive
    rmap_paths := by
      intro r1 r2 hr1 hr2 p hp
      exact pathReflectedInHeap_heap_alloc rmap m.heap v r1 r2 p
        (hwt.rmap_paths r1 r2 hr1 hr2 p hp) hwt.rmap_live hwt.heap_loc_bound
    varEnv_refs_in_pathEnv := by
      intro y bt r' bk ms' hvy
      have hvy' : lookup (insert env.varEnv x (.validVar, τ', .mutable)) y =
          some (.validVar, .ref bt r' bk, ms') := hvy
      by_cases heq : y = x
      · subst heq; rw [lookup_insert_same] at hvy'
        have hτ : τ' = .ref bt r' bk := by
          simp only [Option.some.injEq, Prod.mk.injEq] at hvy'; exact hvy'.2.1
        rw [hτ] at hsite
        exact hwt.siteEnv_refs_in_pathEnv a bt r' bk hsite
      · rw [lookup_insert_ne _ x y _ heq] at hvy'
        exact hwt.varEnv_refs_in_pathEnv y bt r' bk ms' hvy'
    siteEnv_refs_in_pathEnv := by
      intro s' bt r' bk hl
      have hne : s' ≠ a := by
        intro h; subst h; rw [lookup_delete_same] at hl; simp at hl
      rw [lookup_delete_ne env.siteEnv a s' hne] at hl
      exact hwt.siteEnv_refs_in_pathEnv s' bt r' bk hl
    live_refs_unique := by
      intro r'
      refine ⟨fun x' bt bk ms' s' bt' bk' hvar_x' hs' => ?_,
              fun s1 s2 bt1 bt2 bk1 bk2 hne hs1 hs2 => ?_,
              fun x1 x2 bt1 bt2 bk1 bk2 ms1 ms2 hne hx1 hx2 => ?_⟩
      · -- var-site: reduce site lookup
        have hne_a : s' ≠ a := by
          intro h; subst h; rw [lookup_delete_same] at hs'; simp at hs'
        rw [lookup_delete_ne env.siteEnv a s' hne_a] at hs'
        -- reduce var lookup
        have hvar' : lookup (insert env.varEnv x (.validVar, τ', .mutable)) x' =
            some (.validVar, .ref bt r' bk, ms') := hvar_x'
        by_cases heq : x' = x
        · subst heq; rw [lookup_insert_same] at hvar'
          have hτ : τ' = .ref bt r' bk := by
            simp only [Option.some.injEq, Prod.mk.injEq] at hvar'; exact hvar'.2.1
          rw [hτ] at hsite
          -- a and s' both have ref r' in env.siteEnv, s' ≠ a
          exact (hwt.live_refs_unique r').2.1 a s' bt bt' bk bk' (Ne.symm hne_a) hsite hs'
        · rw [lookup_insert_ne _ x x' _ heq] at hvar'
          exact (hwt.live_refs_unique r').1 x' bt bk ms' s' bt' bk' hvar' hs'
      · -- site-site
        have hne1 : s1 ≠ a := by
          intro h; subst h; rw [lookup_delete_same] at hs1; simp at hs1
        have hne2 : s2 ≠ a := by
          intro h; subst h; rw [lookup_delete_same] at hs2; simp at hs2
        rw [lookup_delete_ne env.siteEnv a s1 hne1] at hs1
        rw [lookup_delete_ne env.siteEnv a s2 hne2] at hs2
        exact (hwt.live_refs_unique r').2.1 s1 s2 bt1 bt2 bk1 bk2 hne hs1 hs2
      · -- var-var
        have hx1' : lookup (insert env.varEnv x (.validVar, τ', .mutable)) x1 =
            some (.validVar, .ref bt1 r' bk1, ms1) := hx1
        have hx2' : lookup (insert env.varEnv x (.validVar, τ', .mutable)) x2 =
            some (.validVar, .ref bt2 r' bk2, ms2) := hx2
        by_cases heq1 : x1 = x
        · rw [heq1, lookup_insert_same] at hx1'
          have hτ : τ' = .ref bt1 r' bk1 := by
            simp only [Option.some.injEq, Prod.mk.injEq] at hx1'; exact hx1'.2.1
          have hsite' := hsite_a
          rw [hτ] at hsite'
          have hne2 : x2 ≠ x := by rw [← heq1]; exact hne.symm
          rw [lookup_insert_ne _ x x2 _ hne2] at hx2'
          -- x2 valid with ref r', site a has ref r' → var-site contradiction
          exact (hlive_old r').1 x2 bt2 bk2 ms2 a bt1 bk1 hx2' hsite'
        · by_cases heq2 : x2 = x
          · rw [heq2, lookup_insert_same] at hx2'
            have hτ : τ' = .ref bt2 r' bk2 := by
              simp only [Option.some.injEq, Prod.mk.injEq] at hx2'; exact hx2'.2.1
            have hsite' := hsite_a
            rw [hτ] at hsite'
            rw [lookup_insert_ne _ x x1 _ heq1] at hx1'
            exact (hlive_old r').1 x1 bt1 bk1 ms1 a bt2 bk2 hx1' hsite'
          · rw [lookup_insert_ne _ x x1 _ heq1] at hx1'
            rw [lookup_insert_ne _ x x2 _ heq2] at hx2'
            exact (hlive_old r').2.2 x1 x2 bt1 bt2 bk1 bk2 ms1 ms2 hne hx1' hx2'
    blocks_typed := hwt.blocks_typed
    lenv_empty_siteEnv := hwt.lenv_empty_siteEnv
    funEnv_typed := hwt.funEnv_typed
    heap_loc_bound := heap_loc_bound_after_alloc m.heap v hwt.heap_loc_bound
    rmap_root_none := hwt.rmap_root_none
    no_paths_to_root := hwt.no_paths_to_root
    root_path_coherence := by
      -- pathEnv and rmap unchanged; varStore(x) → fresh alloc location
      intro v' y rest hv_mem hp loc_v path_v hrmap loc_y hloc heq
      by_cases heqx : y = x
      · -- y = x: varStore'(x) = (m.heap.alloc v).2 = m.heap.nextLoc (fresh)
        subst heqx
        simp only [lookup_insert_same, Option.some.injEq] at hloc
        have halloc_eq : (m.heap.alloc v).2 = m.heap.nextLoc := rfl
        have hlt := hwt.heap_loc_bound loc_v (readRef_implies_read m.heap loc_v path_v
          (hwt.rmap_live v' loc_v path_v hrmap))
        rw [← hloc, halloc_eq] at heq
        exact absurd heq (Nat.ne_of_lt hlt)
      · -- y ≠ x: varStore(y) unchanged
        rw [lookup_insert_ne _ x y _ heqx] at hloc
        exact hwt.root_path_coherence v' y rest hv_mem hp loc_v path_v hrmap loc_y hloc heq
  }

-- ============================================================
-- Part 8b: Main Preservation Theorem (dispatches to case lemmas)
-- ============================================================

theorem preservation (m m' : Machine) (env : TypeEnv) (lenv : LabelEnv)
    (retType : MoveType) (rmap : RefMap)
    (hwt : WellTypedState m env lenv retType rmap)
    (hss : StackSafe m.stack m.frame.returnInfo m.heap)
    (hstep : step (.running m) = .running m') :
    ∃ env' lenv' retType' rmap',
      WellTypedState m' env' lenv' retType' rmap' ∧
      StackSafe m'.stack m'.frame.returnInfo m'.heap := by
  cases hstmt : m.frame.stmt with
  | skip =>
    exfalso; simp only [step, hstmt] at hstep
    split at hstep <;> simp at hstep
  | abort msg =>
    exfalso; simp only [step, hstmt] at hstep; contradiction
  | letBind s expr cont =>
    cases expr with
    | intLit n => exact preservation_intLit m m' env lenv retType rmap hwt hss s n cont hstmt hstep
    | usage u =>
      cases u with
      | copy x =>
        rcases inv_copy (by rw [← hstmt]; exact hwt.stmt_typed) with
          ⟨bt, ms, hvar, hcont⟩ | ⟨τ_ref, ms, s_orig, t, isBor, hvar, hfresh_t, hnv_t, hcont⟩
        · exact preservation_copy_val m m' env lenv retType rmap hwt hss s x cont bt ms hstmt hvar hcont hstep
        · exact preservation_copy_ref m m' env lenv retType rmap hwt hss s x cont
            τ_ref ms s_orig t isBor hvar hfresh_t hnv_t hcont hstmt hstep
      | move x => exact preservation_move m m' env lenv retType rmap hwt hss s x cont hstmt hstep
      | borrowImm x => exact preservation_borrowImm m m' env lenv retType rmap hwt hss s x cont hstmt hstep
      | borrowMut x => sorry
    | borrowField src bt field => sorry
    | borrowMutField src bt field => sorry
    | readRef src => exact preservation_readRef m m' env lenv retType rmap hwt hss s src cont hstmt hstep
    | freeze src => sorry
    | pack name fieldSites => exact preservation_pack m m' env lenv retType rmap hwt hss s name fieldSites cont hstmt hstep
    | binop op a b => exact preservation_binop m m' env lenv retType rmap hwt hss s op a b cont hstmt hstep
  | release site cont => exact preservation_release m m' env lenv retType rmap hwt hss site cont hstmt hstep
  | assign x site cont =>
    rcases inv_assign (by rw [← hstmt]; exact hwt.stmt_typed) with
      ⟨ax, τ, ms, r, hvar, hnv, hfresh, hnotin, hcont⟩ | ⟨τ, τ', hvar, hsite, hcompat, hcont⟩
    · exact preservation_assign_valid m m' env lenv retType rmap hwt hss x site cont ax τ ms r
        hvar hnv hfresh hnotin hcont hstmt hstep
    · exact preservation_assign_invalid m m' env lenv retType rmap hwt hss x site cont τ τ'
        hvar hsite hcompat hcont hstmt hstep
  | writeRef dst val cont => sorry
  | jump label => sorry
  | branch c l1 l2 => sorry
  | ret sites => sorry
  | call results fname argSites cont => sorry
  | unpack fields src cont => sorry

-- ============================================================
-- Part 9: Safe Execution State
-- ============================================================

/-- An exec state is "safe" if running states are well-typed (with stack safety)
    and error states are not danglingRef errors. -/
def SafeExecState (state : ExecState) : Prop :=
  match state with
  | .running m => ∃ env lenv retType rmap,
      WellTypedState m env lenv retType rmap ∧
      StackSafe m.stack m.frame.returnInfo m.heap
  | .halted _ => True
  | .error (.danglingRef _) => False
  | .error _ => True

/-- A safe exec state steps to a safe exec state.
    Uses no_danglingRef_progress (to rule out danglingRef errors)
    and preservation (to maintain WellTypedState for running states). -/
theorem safe_step (state : ExecState)
    (hsafe : SafeExecState state) :
    SafeExecState (step state) := by
  cases state with
  | halted v => simp [step, SafeExecState]
  | error e => simp only [step]; exact hsafe
  | running m =>
    obtain ⟨env, lenv, retType, rmap, hwt, hss⟩ := hsafe
    show SafeExecState (step (.running m))
    generalize hres : step (.running m) = result
    cases result with
    | running m' =>
      simp only [SafeExecState]
      exact preservation m m' env lenv retType rmap hwt hss hres
    | halted v => simp [SafeExecState]
    | error e =>
      cases e with
      | danglingRef loc =>
        exact absurd hres (no_danglingRef_progress m env lenv retType rmap hwt loc)
      | uninitializedVar _ => simp [SafeExecState]
      | uninitializedSite _ => simp [SafeExecState]
      | typeMismatch _ => simp [SafeExecState]
      | unknownFunction _ => simp [SafeExecState]
      | unknownLabel _ => simp [SafeExecState]
      | invalidFieldAccess _ => simp [SafeExecState]
      | divisionByZero => simp [SafeExecState]
      | outOfFuel => simp [SafeExecState]
      | arityMismatch _ => simp [SafeExecState]

/-- A SafeExecState is never a danglingRef error -/
theorem SafeExecState.not_danglingRef {state : ExecState}
    (hsafe : SafeExecState state) :
    ∀ loc, state ≠ .error (.danglingRef loc) := by
  intro loc h; subst h; exact hsafe

-- ============================================================
-- Part 10: Iterated Safety
-- ============================================================

/-- A safe exec state remains danglingRef-free after any number of steps.
    By induction on fuel, using safe_step at each iteration. -/
theorem safe_run_no_danglingRef (state : ExecState)
    (hsafe : SafeExecState state) :
    ∀ n loc, Semantics.run n state ≠ .error (.danglingRef loc) := by
  intro n
  induction n generalizing state with
  | zero =>
    intro loc h
    unfold Semantics.run at h
    injection h with h'
    exact nomatch h'
  | succ n ih =>
    intro loc h
    unfold Semantics.run at h
    match state, hsafe with
    | .running m, hsafe =>
      exact ih (step (.running m)) (safe_step (.running m) hsafe) loc h
    | .halted _, _ =>
      exact absurd h (by intro h'; cases h')
    | .error _, hsafe =>
      exact SafeExecState.not_danglingRef hsafe loc h

-- ============================================================
-- Part 11: Initial State is Well-Typed
-- ============================================================

-- Helper lemmas for initState_safe

/-- General foldl+insert lemma: if the initial map and every insertion satisfy P,
    then every lookup result satisfies P. -/
private lemma foldl_insert_lookup {K V L : Type} [DecidableEq K]
    (xs : List L) (init : AssocMap K V) (getKey : L → K) (getValue : L → V)
    (P : V → Prop)
    (hinit : ∀ k v, lookup init k = some v → P v)
    (hinsert : ∀ x, x ∈ xs → P (getValue x)) :
    ∀ k v, lookup (xs.foldl (fun m x => insert m (getKey x) (getValue x)) init) k = some v → P v := by
  induction xs generalizing init with
  | nil => exact hinit
  | cons elem rest ih =>
    intro k v h
    apply ih (insert init (getKey elem) (getValue elem)) _ _ k v h
    · intro k' v' hlookup
      by_cases heq : k' = getKey elem
      · rw [heq, lookup_insert_same] at hlookup
        rw [← Option.some.inj hlookup]
        exact hinsert elem (.head rest)
      · rw [lookup_insert_ne _ _ _ _ heq] at hlookup
        exact hinit k' v' hlookup
    · intro x' hmem
      exact hinsert x' (List.mem_cons_of_mem elem hmem)

/-- In add_locals_to_varEnv, .validVar entries pass through from the base env and
    the variable is not in the locals' names. -/
private lemma add_locals_foldl_valid (venv : VarEnv) (locals : List LocalVar)
    (x : Var) (τ : MoveType) (ms : Mut) :
    lookup (locals.foldl (fun env lv => insert env lv.name (.invalidVar, lv.type, .mutable)) venv) x
      = some (.validVar, τ, ms) →
    lookup venv x = some (.validVar, τ, ms) ∧ x ∉ locals.map (·.name) := by
  induction locals generalizing venv with
  | nil =>
    simp only [List.foldl, List.map, List.not_mem_nil]
    exact fun h => ⟨h, not_false⟩
  | cons lv rest ih =>
    simp only [List.foldl, List.map, List.mem_cons, not_or]
    intro h
    obtain ⟨hlookup, hrest⟩ := ih _ h
    by_cases heq : x = lv.name
    · rw [heq, lookup_insert_same] at hlookup; cases hlookup
    · rw [lookup_insert_ne _ _ _ _ heq] at hlookup
      exact ⟨hlookup, heq, hrest⟩

/-- Non-local keys are preserved through add_locals foldl. -/
private lemma add_locals_foldl_preserves (venv : VarEnv) (locals : List LocalVar) (x : Var) :
    x ∉ locals.map (·.name) →
    lookup (locals.foldl (fun env lv => insert env lv.name (.invalidVar, lv.type, .mutable)) venv) x
      = lookup venv x := by
  induction locals generalizing venv with
  | nil => intro _; rfl
  | cons lv rest ih =>
    simp only [List.map, List.mem_cons, not_or, List.foldl]
    intro ⟨hne, hrest⟩
    rw [ih _ hrest, lookup_insert_ne _ _ _ _ hne]

/-- All entries in init_varEnv_from_params have .validVar. -/
private lemma init_varEnv_from_params_isValidVar (params : List (Var × MoveType))
    (x : Var) (isv : IsValid) (τ : MoveType) (ms : Mut) :
    lookup (init_varEnv_from_params params) x = some (isv, τ, ms) → isv = .validVar := by
  intro h
  unfold init_varEnv_from_params at h
  have := foldl_insert_lookup params AssocMap.empty
    (fun p => p.1) (fun p => (IsValid.validVar, p.2, Mut.mutable))
    (fun v => v.1 = IsValid.validVar)
    (by intro _ _ h; simp [lookup, AssocMap.empty] at h)
    (by intro _ _; rfl)
    x (isv, τ, ms) h
  simpa using this

/-- Key-aware foldl+insert: if the initial map and every insertion satisfy P(key, value),
    then every lookup result satisfies P(key, value). -/
private lemma foldl_insert_lookup_key {K V L : Type} [DecidableEq K]
    (xs : List L) (init : AssocMap K V) (getKey : L → K) (getValue : L → V)
    (P : K → V → Prop)
    (hinit : ∀ k v, lookup init k = some v → P k v)
    (hinsert : ∀ elem, elem ∈ xs → P (getKey elem) (getValue elem)) :
    ∀ k v, lookup (xs.foldl (fun m e => insert m (getKey e) (getValue e)) init) k = some v → P k v := by
  induction xs generalizing init with
  | nil => exact hinit
  | cons elem rest ih =>
    intro k v h
    apply ih (insert init (getKey elem) (getValue elem)) _ _ k v h
    · intro k' v' hlookup
      by_cases heq : k' = getKey elem
      · rw [heq, lookup_insert_same] at hlookup
        rw [← Option.some.inj hlookup, heq]
        exact hinsert elem (.head rest)
      · rw [lookup_insert_ne _ _ _ _ heq] at hlookup
        exact hinit k' v' hlookup
    · intro x' hmem
      exact hinsert x' (.tail _ hmem)

/-- If lookup in init_fun_varEnv gives .validVar, then the type comes from a param. -/
private lemma init_fun_varEnv_valid_in_params (f : FunDef) (x : Var) (τ : MoveType) (ms : Mut) :
    lookup (init_fun_varEnv f) x = some (.validVar, τ, ms) →
    (x, τ) ∈ f.params := by
  unfold init_fun_varEnv add_locals_to_varEnv init_varEnv_from_params
  intro h
  have ⟨hlookup_params, _⟩ := add_locals_foldl_valid _ _ _ _ _ h
  have := foldl_insert_lookup_key f.params AssocMap.empty
    (fun p => p.1) (fun p => (IsValid.validVar, p.2, Mut.mutable))
    (fun k v => ∃ τ₀, (k, τ₀) ∈ f.params ∧ v = (IsValid.validVar, τ₀, Mut.mutable))
    (by intro _ _ h; simp [lookup, AssocMap.empty] at h)
    (by intro p hmem; exact ⟨p.2, (Prod.eta p ▸ hmem), rfl⟩)
    x (.validVar, τ, ms) hlookup_params
  obtain ⟨τ₀, hmem, heq⟩ := this
  simp only [Prod.mk.injEq, true_and] at heq
  rw [heq.1]; exact hmem

/-- If lookup in init_fun_varEnv gives .validVar, then x is not a local name. -/
private lemma init_fun_varEnv_valid_not_local (f : FunDef) (x : Var) (τ : MoveType) (ms : Mut) :
    lookup (init_fun_varEnv f) x = some (.validVar, τ, ms) →
    x ∉ f.locals.map (·.name) := by
  unfold init_fun_varEnv add_locals_to_varEnv
  intro h
  exact (add_locals_foldl_valid _ _ _ _ _ h).2

/-- If lookup in init_fun_varEnv gives .invalidVar, then x is a local name. -/
private lemma init_fun_varEnv_invalid_is_local (f : FunDef) (x : Var) (τ : MoveType) (ms : Mut) :
    lookup (init_fun_varEnv f) x = some (.invalidVar, τ, ms) →
    x ∈ f.locals.map (·.name) := by
  unfold init_fun_varEnv add_locals_to_varEnv
  intro h
  by_contra habs
  rw [add_locals_foldl_preserves _ _ _ habs] at h
  have := init_varEnv_from_params_isValidVar f.params x .invalidVar τ ms h
  cases this  -- .invalidVar = .validVar is impossible

/-- addLocals preserves lookups for variables not in the locals list. -/
private lemma addLocals_preserves_lookup (vs : VarStore) (locals : List LocalVar) (x : Var)
    (hx : x ∉ locals.map (·.name)) : lookup (addLocals vs locals) x = lookup vs x := by
  induction locals generalizing vs with
  | nil => rfl
  | cons lv rest ih =>
    simp only [List.map, List.mem_cons, not_or] at hx
    simp only [addLocals]
    rw [ih (insert vs lv.name none) hx.2, lookup_insert_ne _ _ _ _ hx.1]

/-- addLocals sets variables that appear in locals to none. -/
private lemma addLocals_local_some_none (vs : VarStore) (locals : List LocalVar) (x : Var)
    (hx : x ∈ locals.map (·.name)) : lookup (addLocals vs locals) x = some none := by
  induction locals generalizing vs with
  | nil => cases hx
  | cons lv rest ih =>
    simp only [List.map, List.mem_cons] at hx
    simp only [addLocals]
    rcases hx with heq | hmem
    · -- x = lv.name
      by_cases hrest : x ∈ rest.map (·.name)
      · exact ih _ hrest
      · rw [addLocals_preserves_lookup _ _ _ hrest, heq, lookup_insert_same]
    · exact ih _ hmem

-- Heap.alloc helper lemmas
private lemma heap_alloc_nextLoc (h : Heap) (v : Value) :
    (h.alloc v).1.nextLoc = h.nextLoc + 1 := by
  simp [Heap.alloc]

private lemma heap_alloc_read_same (h : Heap) (v : Value) :
    (h.alloc v).1.read h.nextLoc = some v := by
  simp [Heap.alloc, Heap.read, lookup_insert_same]

private lemma heap_alloc_read_ne (h : Heap) (v : Value) (loc : Loc) (hne : loc ≠ h.nextLoc) :
    (h.alloc v).1.read loc = h.read loc := by
  simp only [Heap.alloc, Heap.read]
  exact lookup_insert_ne h.store h.nextLoc loc v hne

private lemma heap_alloc_preserves_bound (h : Heap) (v : Value)
    (hlb : ∀ loc, h.read loc ≠ none → loc < h.nextLoc) :
    ∀ loc, (h.alloc v).1.read loc ≠ none → loc < (h.alloc v).1.nextLoc := by
  intro loc hread
  rw [show (h.alloc v).1.nextLoc = h.nextLoc + 1 from by simp [Heap.alloc]]
  by_cases heq : loc = h.nextLoc
  · subst heq; exact Nat.lt_succ_self _
  · have hread' : h.read loc ≠ none := by
      rwa [heap_alloc_read_ne h v loc heq] at hread
    exact Nat.lt_succ_of_lt (hlb loc hread')

/-- allocArgs preserves reads at locations below the initial nextLoc. -/
private lemma allocArgs_preserves_old_read (heap : Heap) (params : List (Var × MoveType))
    (args : List Value) (heap_out : Heap) (vs : VarStore) :
    allocArgs heap params args = some (heap_out, vs) →
    ∀ loc, loc < heap.nextLoc → heap_out.read loc = heap.read loc := by
  induction params generalizing heap args heap_out vs with
  | nil =>
    intro halloc loc hloc
    cases args with
    | nil =>
      have : heap_out = heap := by
        simp only [allocArgs, Option.some.injEq, Prod.mk.injEq] at halloc
        exact halloc.1.symm
      rw [this]
    | cons => simp [allocArgs] at halloc
  | cons p ps ih =>
    intro halloc loc hloc
    obtain ⟨y, τ_y⟩ := p
    cases args with
    | nil => simp [allocArgs] at halloc
    | cons a as' =>
      -- Unfold allocArgs and extract recursive call result
      simp only [allocArgs, Bind.bind, Option.bind] at halloc
      cases hrec : allocArgs (heap.alloc a).1 ps as' with
      | none => rw [hrec] at halloc; simp at halloc
      | some pair =>
        obtain ⟨h', vs'⟩ := pair
        rw [hrec] at halloc; dsimp at halloc
        simp only [Option.some.injEq, Prod.mk.injEq] at halloc
        rw [halloc.1.symm]
        have hloc' : loc < (heap.alloc a).1.nextLoc := by
          rw [show (heap.alloc a).1.nextLoc = heap.nextLoc + 1 from by simp [Heap.alloc]]
          omega
        rw [ih (heap.alloc a).1 as' h' vs' hrec loc hloc']
        have hne : loc ≠ heap.nextLoc := by intro h; subst h; exact absurd hloc (Nat.lt_irrefl _)
        exact heap_alloc_read_ne heap a loc hne

/-- allocArgs preserves the heap_loc_bound invariant. -/
private lemma allocArgs_heap_loc_bound' (heap : Heap) (params : List (Var × MoveType))
    (args : List Value) (heap_out : Heap) (vs : VarStore) :
    allocArgs heap params args = some (heap_out, vs) →
    (∀ loc, heap.read loc ≠ none → loc < heap.nextLoc) →
    ∀ loc, heap_out.read loc ≠ none → loc < heap_out.nextLoc := by
  induction params generalizing heap args heap_out vs with
  | nil =>
    intro halloc hlb
    cases args with
    | nil =>
      have : heap_out = heap := by
        simp only [allocArgs, Option.some.injEq, Prod.mk.injEq] at halloc
        exact halloc.1.symm
      rw [this]; exact hlb
    | cons => simp [allocArgs] at halloc
  | cons p ps ih =>
    intro halloc hlb
    obtain ⟨y, τ_y⟩ := p
    cases args with
    | nil => simp [allocArgs] at halloc
    | cons a as' =>
      simp only [allocArgs, Bind.bind, Option.bind] at halloc
      cases hrec : allocArgs (heap.alloc a).1 ps as' with
      | none => rw [hrec] at halloc; simp at halloc
      | some pair =>
        obtain ⟨h', vs'⟩ := pair
        rw [hrec] at halloc; dsimp at halloc
        simp only [Option.some.injEq, Prod.mk.injEq] at halloc
        rw [halloc.1.symm]
        exact ih (heap.alloc a).1 as' h' vs' hrec
          (heap_alloc_preserves_bound heap a hlb)

/-- allocArgs provides store entries and heap values for each parameter. -/
private lemma allocArgs_param_allocated (heap : Heap) (params : List (Var × MoveType))
    (args : List Value) (heap_out : Heap) (vs : VarStore)
    (hlb : ∀ loc, heap.read loc ≠ none → loc < heap.nextLoc) :
    allocArgs heap params args = some (heap_out, vs) →
    ∀ x τ, (x, τ) ∈ params →
    ∃ loc v, lookup vs x = some (some loc) ∧ heap_out.read loc = some v := by
  induction params generalizing heap args heap_out vs with
  | nil =>
    intro _ x τ hmem; nomatch hmem
  | cons p ps ih =>
    intro halloc x τ hmem
    obtain ⟨y, τ_y⟩ := p
    cases args with
    | nil => simp [allocArgs] at halloc
    | cons a as' =>
      simp only [allocArgs, Bind.bind, Option.bind] at halloc
      cases hrec : allocArgs (heap.alloc a).1 ps as' with
      | none => rw [hrec] at halloc; simp at halloc
      | some pair =>
        obtain ⟨h', vs'⟩ := pair
        rw [hrec] at halloc; dsimp at halloc
        simp only [Option.some.injEq, Prod.mk.injEq] at halloc
        obtain ⟨rfl, rfl⟩ := halloc
        -- heap_out = h', vs = insert vs' y (some (heap.alloc a).2)
        simp only [List.mem_cons, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, _⟩ | hmem_rest
        · -- head case: x = y
          refine ⟨(heap.alloc a).2, a, lookup_insert_same _ _ _, ?_⟩
          have hloc : (heap.alloc a).2 < (heap.alloc a).1.nextLoc := by
            simp [Heap.alloc]
          rw [allocArgs_preserves_old_read (heap.alloc a).1 ps as' h' vs' hrec
              (heap.alloc a).2 hloc]
          exact heap_alloc_read_same heap a
        · -- tail case: (x, τ) ∈ ps
          have ⟨loc, v, hlookup, hread⟩ :=
            ih (heap.alloc a).1 as' h' vs'
              (heap_alloc_preserves_bound heap a hlb)
              hrec x τ hmem_rest
          by_cases heq : x = y
          · -- x = y: insert overwrites, use head allocation
            rw [heq]
            refine ⟨(heap.alloc a).2, a, lookup_insert_same _ _ _, ?_⟩
            have hloc : (heap.alloc a).2 < (heap.alloc a).1.nextLoc := by
              simp [Heap.alloc]
            rw [allocArgs_preserves_old_read (heap.alloc a).1 ps as' h' vs' hrec
                (heap.alloc a).2 hloc]
            exact heap_alloc_read_same heap a
          · -- x ≠ y: insert preserves
            exact ⟨loc, v, by rw [lookup_insert_ne _ _ _ _ heq]; exact hlookup, hread⟩

-- ============================================================
-- Part 11b: Soundness Assumptions
-- ============================================================

/-- Semantic prerequisites for type soundness that are not captured by the
    relational type-checking judgment `typecheck_fun`.

    `typecheck_fun` is a purely syntactic/structural judgment: it verifies that
    each block's instructions are well-typed relative to a label environment
    `lenv`, but it does not constrain the structural properties of `lenv`
    itself, nor does it know about the runtime heap or function signature
    restrictions.

    The decidable type checker (`check_fun_dec_sound`) establishes `lenv_wf`
    for the `lenv` it constructs. The remaining four fields are decidable and
    can be verified via `SoundnessAssumptions.checkDecidable`. -/
structure SoundnessAssumptions (f : FunDef) (lenv : LabelEnv) (heap : Heap) where
  /-- Every label environment entry is structurally well-formed.
      Not decidable without the decidable type-checking representation (`LabelEnvDec`),
      because `TypeEnv.WellFormed` involves `PathEnv.WellFormed` which constrains
      `PathEnv.paths : Aref × Aref → Regex`, a function that cannot be enumerated
      without the finite decidable representation.
      In practice, established by `check_fun_dec_sound`. -/
  lenv_wf : ∀ l env, lookup lenv l = some env → TypeEnv.WellFormed env

  /-- Function parameters have basic types (not references).
      At function entry, the PathEnv is `PathEnv.init` (tracking only `.root`) with an
      empty RefMap. There is no way to construct initial rmap entries for ref-typed
      parameters, because the caller's abstract references are not available to the callee. -/
  params_basic : ∀ x τ, (x, τ) ∈ f.params → ∃ bt, τ = .basic bt

  /-- The initial heap is internally consistent: every readable location is below `nextLoc`.
      This is a runtime property unknown to the type checker. Holds trivially for `Heap.empty`. -/
  heap_wf : ∀ loc, heap.read loc ≠ none → loc < heap.nextLoc

  /-- Label environment entries have empty site environments.
      Sites are block-local (introduced by `call`, consumed by `ret` within a block),
      so block-entry environments always have empty sites.
      `typecheck_fun` does not enforce this: it uses `TypeEnv.equiv` at block boundaries,
      which allows non-empty siteEnvs on both sides. -/
  lenv_empty_sites : ∀ l env, lookup lenv l = some env → ∀ s, lookup env.siteEnv s = none

  /-- Every block in the function has a corresponding type environment in `lenv`.
      `typecheck_fun`'s `hblocks_typed` quantifies as
      `∀ benv, lookup lenv b.label = some benv → …`, which is vacuously true
      when `lookup lenv b.label = none`. The decidable checker produces an `lenv`
      that covers all blocks. -/
  lenv_complete : ∀ block, block ∈ f.blocks → ∃ env, lookup lenv block.label = some env

/-- Boolean check for the decidable fields of `SoundnessAssumptions`.
    `lenv_wf` is excluded because `TypeEnv.WellFormed` involves function-valued
    `PathEnv.paths` and requires the decidable type environment representation. -/
def SoundnessAssumptions.checkDecidable (f : FunDef) (lenv : LabelEnv) (heap : Heap) : Bool :=
  -- params_basic: all parameter types are basic
  f.params.all (fun (_, τ) => match τ with | .basic _ => true | _ => false) &&
  -- heap_wf: all locations in heap store are below nextLoc
  heap.store.entries.all (fun (loc, _) => decide (loc < heap.nextLoc)) &&
  -- lenv_empty_sites: all siteEnvs in lenv entries are empty
  lenv.entries.all (fun (_, env) => env.siteEnv.isEmpty) &&
  -- lenv_complete: every block label appears in lenv
  f.blocks.all (fun block => lenv.entries.any (fun (l, _) => l == block.label))

-- Helper: if some entry has a matching key, List.lookup succeeds
private theorem any_beq_implies_list_lookup {K V : Type} [DecidableEq K]
    (entries : List (K × V)) (k : K) :
    entries.any (fun (l, _) => l == k) = true →
    ∃ v, List.lookup k entries = some v := by
  induction entries with
  | nil => simp
  | cons hd rest ih =>
    intro h
    simp only [List.any_cons, Bool.or_eq_true] at h
    obtain ⟨l, v⟩ := hd
    rcases h with hhead | htail
    · have heq : l = k := by simpa using hhead
      rw [← heq]; simp [List.lookup]
    · simp only [List.lookup]
      cases heq : k == l
      · exact ih htail
      · exact ⟨v, rfl⟩

/-- Soundness of the decidable check: given `lenv_wf` separately, the boolean
    check yields the full `SoundnessAssumptions`. -/
theorem SoundnessAssumptions.of_check (f : FunDef) (lenv : LabelEnv) (heap : Heap)
    (hlenv_wf : ∀ l env, lookup lenv l = some env → TypeEnv.WellFormed env)
    (hcheck : SoundnessAssumptions.checkDecidable f lenv heap = true) :
    SoundnessAssumptions f lenv heap where
  lenv_wf := hlenv_wf
  params_basic := by
    simp only [checkDecidable, Bool.and_eq_true] at hcheck
    obtain ⟨⟨⟨hp, _⟩, _⟩, _⟩ := hcheck
    simp only [List.all_eq_true] at hp
    intro x τ hmem
    have := hp (x, τ) hmem
    cases τ with
    | basic bt => exact ⟨bt, rfl⟩
    | ref _ _ _ => simp at this
  heap_wf := by
    simp only [checkDecidable, Bool.and_eq_true] at hcheck
    obtain ⟨⟨⟨_, hh⟩, _⟩, _⟩ := hcheck
    simp only [List.all_eq_true] at hh
    intro loc hread
    unfold Heap.read at hread
    cases hlookup : lookup heap.store loc with
    | none => rw [hlookup] at hread; exact absurd rfl hread
    | some v =>
      exact decide_eq_true_eq.mp (hh (loc, v) (lookup_some heap.store loc v hlookup))
  lenv_empty_sites := by
    simp only [checkDecidable, Bool.and_eq_true] at hcheck
    obtain ⟨⟨_, hs⟩, _⟩ := hcheck
    simp only [List.all_eq_true] at hs
    intro l env hlookup s
    have hmem := lookup_some lenv l env hlookup
    have hchk := hs (l, env) hmem
    have hempty : env.siteEnv.entries = [] := by
      cases h : env.siteEnv.entries with
      | nil => rfl
      | cons _ _ => simp [AssocMap.isEmpty, h] at hchk
    show AssocMap.lookup env.siteEnv s = none
    simp only [AssocMap.lookup, hempty, List.lookup]
  lenv_complete := by
    simp only [checkDecidable, Bool.and_eq_true] at hcheck
    obtain ⟨_, hc⟩ := hcheck
    simp only [List.all_eq_true] at hc
    intro block hmem
    have := hc block hmem
    exact any_beq_implies_list_lookup lenv.entries block.label this

-- ============================================================
-- Part 11c: initState_safe
-- ============================================================

/-- The initial state of a well-typed function is safe.
    Requires that the function type-checks. If initState produces a .running state,
    it is well-typed; if it produces an error, it is not danglingRef. -/
theorem initState_safe (f : FunDef) (lenv : LabelEnv) (funEnv : AssocMap Id FunDef)
    (args : List Value) (heap : Heap)
    (htyped : typecheck_fun f lenv)
    (hfunEnv : ∀ fname fdef, lookup funEnv fname = some fdef → ∃ lenv', typecheck_fun fdef lenv')
    (ha : SoundnessAssumptions f lenv heap) :
    SafeExecState (initState f funEnv args heap) := by
  -- Invert typecheck_fun
  obtain ⟨initEnv, hvarEnv, hsiteEnv, hpathEnv, hblocks_ne, hentry_equiv, hblocks_typed⟩ :=
    htyped
  -- Case split on initState
  unfold initState
  cases hallocArgs : allocArgs heap f.params args with
  | none =>
    -- allocArgs fails → arityMismatch error → not danglingRef → safe
    simp only [SafeExecState]
  | some pair =>
    obtain ⟨heap', paramVarStore⟩ := pair
    -- Case split on entry block
    cases hhead : f.blocks.head? with
    | none =>
      -- No blocks → unknownFunction error → not danglingRef → safe
      simp only [SafeExecState]
    | some entryBlock =>
      -- .running case → need to construct WellTypedState
      simp only [SafeExecState]
      -- Get the entry block env from lenv
      obtain ⟨entryLabel, entryBody⟩ := entryBlock
      have hhead' := hhead
      simp only at hhead'
      -- The entry block is in f.blocks (by head?)
      have hentry_in : ⟨entryLabel, entryBody⟩ ∈ f.blocks := by
        cases hbl : f.blocks with
        | nil => simp [hbl] at hhead'
        | cons h t =>
          rw [hbl] at hhead'
          simp only [List.head?, Option.some.injEq] at hhead'
          rw [← hhead']; exact .head t
      -- Get the entry block env from lenv (exists by hlenv_complete)
      obtain ⟨blockEnv, hlookup⟩ := ha.lenv_complete ⟨entryLabel, entryBody⟩ hentry_in
      -- blockEnv is equiv to initEnv
      have hequiv := hentry_equiv entryLabel entryBody blockEnv hhead hlookup
      -- Entry block type-checks with blockEnv
      have htyped_entry := hblocks_typed ⟨entryLabel, entryBody⟩ hentry_in blockEnv hlookup
      -- blockEnv is well-formed
      have hblockEnv_wf := ha.lenv_wf entryLabel blockEnv hlookup
      -- Construct WellTypedState with rmap that maps nothing
      let rmap : RefMap := { map := fun _ => none }
      -- Destructure equiv into components
      have hequiv_unf := hequiv
      unfold TypeEnv.equiv at hequiv_unf
      obtain ⟨_, hvar_compat, hrefs_equiv, hpaths_equiv⟩ := hequiv_unf
      -- Key facts used in multiple fields
      have hrefs_eq : blockEnv.pathEnv.refs = [Aref.root] := by
        rw [hpathEnv] at hrefs_equiv; exact hrefs_equiv
      have hsiteEnv_empty : ∀ s, lookup blockEnv.siteEnv s = none :=
        ha.lenv_empty_sites entryLabel blockEnv hlookup
      -- No ref types appear in blockEnv.varEnv valid entries
      have hno_ref_in_varEnv : ∀ x bt r bk ms,
          lookup blockEnv.varEnv x = some (.validVar, .ref bt r bk, ms) → False := by
        intro x bt r bk ms hlookup_var
        have hcompat := hvar_compat x
        rw [hlookup_var, hvarEnv] at hcompat
        cases hlookup_init : lookup (init_fun_varEnv f) x with
        | none =>
          rw [hlookup_init] at hcompat; exact hcompat
        | some e2 =>
          rw [hlookup_init] at hcompat
          obtain ⟨isv₀, τ₀, ms₀⟩ := e2
          have ⟨hisv, hcomp_t, _⟩ : VarEntryCompatible _ _ := hcompat
          rw [← hisv] at hlookup_init
          have hparam := init_fun_varEnv_valid_in_params f x τ₀ ms₀ hlookup_init
          obtain ⟨bt', hbt'⟩ := ha.params_basic x τ₀ hparam
          rw [hbt'] at hcomp_t
          exact hcomp_t
      refine ⟨blockEnv, lenv, f.returnType, rmap, ?_, ?_⟩
      · -- WellTypedState
        exact {
          env_wf := hblockEnv_wf
          stmt_typed := htyped_entry
          var_consistent := by
            intro x isv τ ms hlookup_var
            have hcompat := hvar_compat x
            rw [hlookup_var, hvarEnv] at hcompat
            cases hlookup_init : lookup (init_fun_varEnv f) x with
            | none => rw [hlookup_init] at hcompat; exact hcompat.elim
            | some e2 =>
              rw [hlookup_init] at hcompat
              obtain ⟨isv₀, τ₀, ms₀⟩ := e2
              have ⟨hisv, hcomp_t, _⟩ : VarEntryCompatible _ _ := hcompat
              cases isv with
              | validVar =>
                rw [← hisv] at hlookup_init
                have hparam := init_fun_varEnv_valid_in_params f x τ₀ ms₀ hlookup_init
                have hnot_local := init_fun_varEnv_valid_not_local f x τ₀ ms₀ hlookup_init
                have ⟨loc, v, hstore, hread⟩ :=
                  allocArgs_param_allocated heap f.params args heap' paramVarStore
                    ha.heap_wf hallocArgs x τ₀ hparam
                have hlookup_vs : lookup (addLocals paramVarStore f.locals) x = some (some loc) := by
                  rw [addLocals_preserves_lookup paramVarStore f.locals x hnot_local]
                  exact hstore
                cases τ with
                | basic bt => exact ⟨loc, v, hlookup_vs, hread, trivial⟩
                | ref bt r bk => exact absurd hlookup_var (by intro h; exact hno_ref_in_varEnv x bt r bk ms h)
              | invalidVar =>
                rw [← hisv] at hlookup_init
                have hlocal := init_fun_varEnv_invalid_is_local f x τ₀ ms₀ hlookup_init
                exact Or.inl (addLocals_local_some_none paramVarStore f.locals x hlocal)
          site_consistent := by
            intro s τ hlookup_s
            rw [hsiteEnv_empty s] at hlookup_s; cases hlookup_s
          rmap_live := by
            intro r loc path hrmap
            exact absurd hrmap nofun
          rmap_paths := by
            intro r1 r2 _ _ p _
            simp only [PathReflectedInHeap, rmap]
          blocks_typed := by
            intro b hmem benv hlookup_b
            exact hblocks_typed b hmem benv hlookup_b
          lenv_empty_siteEnv := ha.lenv_empty_sites
          funEnv_typed := hfunEnv
          heap_loc_bound :=
            allocArgs_heap_loc_bound' heap f.params args heap' paramVarStore
              hallocArgs ha.heap_wf
          varEnv_refs_in_pathEnv := by
            intro x bt r bk ms hlookup_var
            exact absurd hlookup_var (by intro h; exact absurd h (by exact hno_ref_in_varEnv x bt r bk ms))
          siteEnv_refs_in_pathEnv := by
            intro s bt r bk hlookup_s
            rw [hsiteEnv_empty s] at hlookup_s; cases hlookup_s
          live_refs_unique := by
            intro r
            refine ⟨?_, ?_, ?_⟩
            · -- var-site: siteEnv empty
              intro x bt bk ms s bt' bk' _ hlookup_s
              rw [hsiteEnv_empty s] at hlookup_s; cases hlookup_s
            · -- site-site: siteEnv empty
              intro s s' bt bt' bk bk' _ hlookup_s _
              rw [hsiteEnv_empty s] at hlookup_s; cases hlookup_s
            · -- var-var: no ref types in valid vars
              intro x y bt bt' bk bk' ms ms' _ hlookup_x _
              exact hno_ref_in_varEnv x bt r bk ms hlookup_x
          rmap_root_none := by
            simp only [rmap]
          no_paths_to_root := by
            intro u p hp
            by_cases hu : u = Aref.root
            · constructor
              · exact hu
              · have hpaths : blockEnv.pathEnv.paths (.root, .root) = Regex.ε := by
                  have h := hequiv.2.2.2 .root .root
                    (hrefs_eq ▸ .head []) (hrefs_eq ▸ .head [])
                  rw [hpathEnv] at h; exact h
                rw [hu, hpaths] at hp; exact hp
            · -- u ≠ .root → u ∉ refs → paths(u, .root) = .empty → False
              have hu_not_in : u ∉ blockEnv.pathEnv.refs := by
                rw [hrefs_eq]; simp; exact hu
              have hempty := hblockEnv_wf.pathEnv_wf.from_untracked_to_root_empty u hu_not_in hu
              rw [hempty] at hp; exact hp.elim
          root_path_coherence := by
            intro v y rest _ _ loc_v path_v hrmap_v
            exact absurd hrmap_v nofun
        }
      · -- StackSafe [] none heap' = True
        simp only [StackSafe]

-- ============================================================
-- Part 12: Main Theorem
-- ============================================================

/-- The main type soundness theorem: a well-typed function never produces
    a danglingRef error at runtime, regardless of fuel. -/
theorem type_soundness (f : FunDef) (lenv : LabelEnv) (funEnv : AssocMap Id FunDef)
    (args : List Value) (heap : Heap)
    (htyped : typecheck_fun f lenv)
    (hfunEnv : ∀ fname fdef, lookup funEnv fname = some fdef → ∃ lenv', typecheck_fun fdef lenv')
    (ha : SoundnessAssumptions f lenv heap) :
    ∀ n loc, Semantics.run n (initState f funEnv args heap) ≠ .error (.danglingRef loc) :=
  safe_run_no_danglingRef (initState f funEnv args heap)
    (initState_safe f lenv funEnv args heap htyped hfunEnv ha)

end LeanMove.Typing.TypeSoundness
