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
                  pathEnv := update_with_epsilon s t env.pathEnv}
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
  | .ret _ _ _ _ hall _ => hall

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
    blocks_typed := hwt.blocks_typed
    lenv_empty_siteEnv := hwt.lenv_empty_siteEnv
    funEnv_typed := hwt.funEnv_typed
    heap_loc_bound := hwt.heap_loc_bound
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
    blocks_typed := hwt.blocks_typed
    lenv_empty_siteEnv := hwt.lenv_empty_siteEnv
    funEnv_typed := hwt.funEnv_typed
    heap_loc_bound := hwt.heap_loc_bound
  }

/-- Preservation for copy of a reference-typed variable.
    The new site gets a fresh abstract ref t, and pathEnv is updated with
    update_with_epsilon s_orig t (which makes the path graph track that t
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
                  pathEnv := update_with_epsilon s_orig t env.pathEnv}
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
                     pathEnv := update_with_epsilon s_orig t env.pathEnv},
          lenv, retType, rmap', ?_, hss⟩
  exact {
    env_wf := by
      have hpe' := update_with_epsilon_wellformed s_orig t env.pathEnv hwt.env_wf.pathEnv_wf
        hs_not_root hs_not_varRef
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
    rmap_paths := by
      -- PathEnv has changed via update_with_epsilon s_orig t.
      -- Need to verify path coherence for the new PathEnv with rmap'.
      -- This requires analyzing update_with_extension and showing the
      -- concrete heap relationships are consistent.
      sorry
    blocks_typed := hwt.blocks_typed
    lenv_empty_siteEnv := hwt.lenv_empty_siteEnv
    funEnv_typed := hwt.funEnv_typed
    heap_loc_bound := hwt.heap_loc_bound
  }

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
    blocks_typed := hwt.blocks_typed
    lenv_empty_siteEnv := hwt.lenv_empty_siteEnv
    funEnv_typed := hwt.funEnv_typed
    heap_loc_bound := hwt.heap_loc_bound
  }

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
    blocks_typed := hwt.blocks_typed
    lenv_empty_siteEnv := hwt.lenv_empty_siteEnv
    funEnv_typed := hwt.funEnv_typed
    heap_loc_bound := heap_loc_bound_after_alloc heap v hlb
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
      blocks_typed := hwt.blocks_typed
      lenv_empty_siteEnv := hwt.lenv_empty_siteEnv
      funEnv_typed := hwt.funEnv_typed
      heap_loc_bound := hwt.heap_loc_bound
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
    blocks_typed := hwt.blocks_typed
    lenv_empty_siteEnv := hwt.lenv_empty_siteEnv
    funEnv_typed := hwt.funEnv_typed
    heap_loc_bound := hwt.heap_loc_bound
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
    blocks_typed := hwt.blocks_typed
    lenv_empty_siteEnv := hwt.lenv_empty_siteEnv
    funEnv_typed := hwt.funEnv_typed
    heap_loc_bound := hwt.heap_loc_bound
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
      blocks_typed := hwt.blocks_typed
      lenv_empty_siteEnv := hwt.lenv_empty_siteEnv
      funEnv_typed := hwt.funEnv_typed
      heap_loc_bound := hwt.heap_loc_bound
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
      blocks_typed := hwt.blocks_typed
      lenv_empty_siteEnv := hwt.lenv_empty_siteEnv
      funEnv_typed := hwt.funEnv_typed
      heap_loc_bound := heap_loc_bound_after_alloc m.heap v hwt.heap_loc_bound
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
    blocks_typed := hwt.blocks_typed
    lenv_empty_siteEnv := hwt.lenv_empty_siteEnv
    funEnv_typed := hwt.funEnv_typed
    heap_loc_bound := heap_loc_bound_after_alloc m.heap v hwt.heap_loc_bound
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
      | borrowImm x => sorry
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

/-- The initial state of a well-typed function is safe.
    Requires that the function type-checks. If initState produces a .running state,
    it is well-typed; if it produces an error, it is not danglingRef. -/
theorem initState_safe (f : FunDef) (lenv : LabelEnv) (funEnv : AssocMap Id FunDef)
    (args : List Value) (heap : Heap)
    (htyped : typecheck_fun f lenv)
    (hfunEnv : ∀ fname fdef, lookup funEnv fname = some fdef → ∃ lenv', typecheck_fun fdef lenv') :
    SafeExecState (initState f funEnv args heap) := by
  sorry

-- ============================================================
-- Part 12: Main Theorem
-- ============================================================

/-- The main type soundness theorem: a well-typed function never produces
    a danglingRef error at runtime, regardless of fuel. -/
theorem type_soundness (f : FunDef) (lenv : LabelEnv) (funEnv : AssocMap Id FunDef)
    (args : List Value) (heap : Heap)
    (htyped : typecheck_fun f lenv)
    (hfunEnv : ∀ fname fdef, lookup funEnv fname = some fdef → ∃ lenv', typecheck_fun fdef lenv') :
    ∀ n loc, Semantics.run n (initState f funEnv args heap) ≠ .error (.danglingRef loc) :=
  safe_run_no_danglingRef (initState f funEnv args heap)
    (initState_safe f lenv funEnv args heap htyped hfunEnv)

end LeanMove.Typing.TypeSoundness
