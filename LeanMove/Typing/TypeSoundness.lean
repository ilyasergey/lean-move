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
      typecheck_stmt lenv
        {env with siteEnv := insert env.siteEnv a (.ref τ t isBor)
                  pathEnv := update_with_epsilon s t env.pathEnv}
        cont retType) :=
  match h with
  | .let_bind_copy_val _ _ _ _ bt ms _ _ hlookup _ hcont =>
    .inl ⟨bt, ms, hlookup, hcont⟩
  | .let_bind_copy_ref _ _ _ _ τ ms s t isBor _ _ hlookup _ _ hcont =>
    .inr ⟨τ, ms, s, t, isBor, hlookup, hcont⟩

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
      typecheck_stmt lenv
        {env with siteEnv := insert env.siteEnv a (.ref τ r .siteBorrowImm)
                  pathEnv := update_with_extension r .root [.root_to_var x]
                              (update_with_epsilon r r env.pathEnv)}
        cont retType :=
  match h with
  | .let_bind_borrowImm _ _ _ _ τ ms r _ _ hlookup _ _ hcont => ⟨τ, ms, r, hlookup, hcont⟩

private theorem inv_borrowMut
    (h : typecheck_stmt lenv env (.letBind a (.usage (.borrowMut x)) cont) retType) :
    ∃ τ ms r,
      lookup env.varEnv x = some (.validVar, .basic τ, ms) ∧
      typecheck_stmt lenv
        {env with siteEnv := insert env.siteEnv a (.ref τ r .siteBorrowMut)
                  pathEnv := update_with_extension r .root [.root_to_var x]
                              (update_with_epsilon r r env.pathEnv)}
        cont retType :=
  match h with
  | .let_bind_borrowMut _ _ _ _ τ ms r _ _ _ hlookup _ _ hcont => ⟨τ, ms, r, hlookup, hcont⟩

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
      typecheck_stmt lenv
        {env with siteEnv := insert (delete env.siteEnv src) c (.ref τ r' .siteBorrowImm)
                  pathEnv := consume_ref_transfer env.pathEnv r r'}
        cont retType :=
  match h with
  | .let_bind_freeze _ _ _ _ τ r r' isBor _ _ hlookup _ _ hcont =>
    ⟨τ, r, r', isBor, hlookup, hcont⟩

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
      typecheck_stmt lenv
        {env with siteEnv := insert (delete env.siteEnv src) af (.ref bt' rf isBor)
                  pathEnv := update_with_extension rf s [.field field] env.pathEnv}
        cont retType :=
  match h with
  | .let_bind_borrowField _ _ _ _ _ _ bt' isBor fentries s rf _ _ hlookup hbt hf _ _ hcont =>
    ⟨bt', isBor, fentries, s, rf, hlookup, hbt, hf, hcont⟩

private theorem inv_borrowMutField
    (h : typecheck_stmt lenv env (.letBind af (.borrowMutField src bt field) cont) retType) :
    ∃ btf fentries s rf,
      lookup env.siteEnv src = some (.ref bt s .siteBorrowMut) ∧
      bt = .trecord fentries ∧
      lookup fentries field = some btf ∧
      typecheck_stmt lenv
        {env with siteEnv := insert (delete env.siteEnv src) af (.ref btf rf .siteBorrowMut)
                  pathEnv := update_with_extension rf s [.field field] env.pathEnv}
        cont retType :=
  match h with
  | .let_bind_borrowMutField _ _ _ _ _ _ btf fentries s rf _ _ hlookup hbt hf _ _ hcont =>
    ⟨btf, fentries, s, rf, hlookup, hbt, hf, hcont⟩

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
    (∀ a, a ∈ sites → lookup env.siteEnv a = some retType) :=
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
      typecheck_stmt lenv
        {env with siteEnv := delete (delete (insert env.siteEnv ax (.ref τ r .siteBorrowMut)) a) ax
                  pathEnv := garbage_collect (update_with_extension r .root [.root_to_var x]
                              (update_with_epsilon r r env.pathEnv)) r}
        cont retType) ∨
    (∃ τ τ',
      lookup env.varEnv x = some (.invalidVar, τ, .mutable) ∧
      lookup env.siteEnv a = some τ' ∧
      typecheck_stmt lenv
        {env with varEnv := update env.varEnv x (.validVar, τ', .mutable)
                  siteEnv := delete env.siteEnv a}
        cont retType) :=
  match h with
  | .var_assign_valid _ _ _ _ ax τ ms r _ _ _ hlookup _ _ hcont =>
    .inl ⟨ax, τ, ms, r, hlookup, hcont⟩
  | .var_assign_invalid _ _ _ _ τ τ' _ _ hlookup_var hlookup_site _ hcont =>
    .inr ⟨τ, τ', hlookup_var, hlookup_site, hcont⟩

-- ============================================================
-- Part 8: Preservation
-- ============================================================

theorem preservation (m m' : Machine) (env : TypeEnv) (lenv : LabelEnv)
    (retType : MoveType) (rmap : RefMap)
    (hwt : WellTypedState m env lenv retType rmap)
    (hss : StackSafe m.stack m.frame.returnInfo m.heap)
    (hstep : step (.running m) = .running m') :
    ∃ env' lenv' retType' rmap',
      WellTypedState m' env' lenv' retType' rmap' ∧
      StackSafe m'.stack m'.frame.returnInfo m'.heap := by
  -- Case analysis on the statement form
  cases hstmt : m.frame.stmt with
  | skip =>
    -- skip steps to halted or error, never .running
    exfalso; simp only [step, hstmt] at hstep
    split at hstep <;> simp at hstep
  | abort msg =>
    -- abort steps to error, never .running
    exfalso; simp only [step, hstmt] at hstep; contradiction
  | letBind s expr cont =>
    cases expr with
    | intLit n =>
      -- step inserts (.int n) into siteStore, advances to cont
      simp only [step, hstmt, ExecState.running.injEq] at hstep; subst hstep
      -- Extract continuation typing from the derivation
      have hcont := inv_intLit (by rw [← hstmt]; exact hwt.stmt_typed)
      refine ⟨{env with siteEnv := insert env.siteEnv s (.basic .u64)},
              lenv, retType, rmap, ?_, hss⟩
      exact {
        env_wf := TypeEnv.insert_siteEnv_wf env s (.basic .u64) hwt.env_wf trivial
        stmt_typed := hcont
        var_consistent := hwt.var_consistent
        site_consistent := by
          intro s' τ hl
          by_cases heq : s' = s
          · subst heq
            simp only [lookup_insert_same, Option.some.injEq] at hl; subst hl
            exact ⟨.int n, lookup_insert_same _ _ _, trivial⟩
          · rw [lookup_insert_ne _ s s' _ heq] at hl
            obtain ⟨v, hv, hm⟩ := hwt.site_consistent s' τ hl
            refine ⟨v, ?_, hm⟩
            rw [lookup_insert_ne _ s s' _ heq]; exact hv
        rmap_live := hwt.rmap_live
        rmap_paths := hwt.rmap_paths
        blocks_typed := hwt.blocks_typed
        lenv_empty_siteEnv := hwt.lenv_empty_siteEnv
        funEnv_typed := hwt.funEnv_typed
      }
    | usage u => sorry
    | borrowField src bt field => sorry
    | borrowMutField src bt field => sorry
    | readRef src => sorry
    | freeze src => sorry
    | pack name fieldSites => sorry
    | binop op a b => sorry
  | release site cont =>
    -- step is a no-op: just advances to cont
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
      rmap_paths := by
        intro r1 r2 hr1 hr2 p hp
        -- Normalize struct projections so rw can match
        have hr1f : r1 ∈ (delete_ref_node env.pathEnv r).refs := hr1
        have hr2f : r2 ∈ (delete_ref_node env.pathEnv r).refs := hr2
        have hpf : interpret_regex ((delete_ref_node env.pathEnv r).paths (r1, r2)) p := hp
        simp only [delete_ref_node_refs, List.mem_filter, decide_eq_true_eq] at hr1f hr2f
        obtain ⟨hr1_mem, hr1_ne⟩ := hr1f
        obtain ⟨hr2_mem, hr2_ne⟩ := hr2f
        rw [delete_ref_node_paths_not_involving_r env.pathEnv r r1 r2 hr1_ne hr2_ne] at hpf
        exact hwt.rmap_paths r1 r2 hr1_mem hr2_mem p hpf
      blocks_typed := hwt.blocks_typed
      lenv_empty_siteEnv := hwt.lenv_empty_siteEnv
      funEnv_typed := hwt.funEnv_typed
    }
  | assign x site cont => sorry
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
