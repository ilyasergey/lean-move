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

/-- A value matches a MoveType, given a reference map for resolving abstract refs -/
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

/-- Writing to a heap location preserves reads at different locations -/
theorem heap_write_preserves_read (h : Heap) (wloc rloc : Loc) (v : Value) :
    wloc ≠ rloc →
    (h.write wloc v).read rloc = h.read rloc := by
  intro hne
  simp only [Heap.write, Heap.read]
  simp only [AssocMap.lookup, AssocMap.insert]
  simp only [List.lookup]
  sorry -- requires properties of AssocMap.insert/lookup interaction

/-- Writing through writeRef at one location preserves readRef at a different location -/
theorem heap_writeRef_preserves_readRef_diff_loc (h : Heap) (wloc rloc : Loc)
    (wp rp : List Field) (v : Value) (h' : Heap) :
    wloc ≠ rloc →
    h.writeRef wloc wp v = some h' →
    h'.readRef rloc rp = h.readRef rloc rp := by
  intro hne hwrite
  simp only [Heap.writeRef, Heap.readRef] at *
  sorry -- follows from heap_write_preserves_read

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
  var_consistent : ∀ x isv τ ms,
    lookup env.varEnv x = some (isv, τ, ms) →
    match isv with
    | .validVar =>
      ∃ loc, lookup m.frame.varStore x = some (some loc) ∧
             m.heap.read loc ≠ none
    | .invalidVar =>
      lookup m.frame.varStore x = some none ∨
      ∃ loc, lookup m.frame.varStore x = some (some loc)

  -- 4. Site consistency: SiteEnv tracks what SiteStore has
  site_consistent : ∀ s τ,
    lookup env.siteEnv s = some τ →
    ∃ v, lookup m.frame.siteStore s = some v ∧ ValueMatchesType v τ rmap

  -- 5. Heap consistency via rmap:
  --    Every live abstract reference maps to a valid concrete heap location
  rmap_live : ∀ r, r ∈ env.pathEnv.refs →
    r ≠ .root →
    ∃ loc path, rmap.map r = some (loc, path) ∧
                m.heap.readRef loc path ≠ none

  -- 6. Path–heap coherence:
  --    PathEnv paths correspond to concrete field relationships in the heap
  rmap_paths : ∀ r1 r2,
    r1 ∈ env.pathEnv.refs → r2 ∈ env.pathEnv.refs →
    ∀ p, interpret_regex (env.pathEnv.paths (r1, r2)) p →
    PathReflectedInHeap rmap m.heap r1 r2 p

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

/-- A well-typed running state never produces a danglingRef error.
    This is the key progress lemma — it only needs the readRef and writeRef cases. -/
theorem no_danglingRef_progress (m : Machine) (env : TypeEnv) (lenv : LabelEnv)
    (retType : MoveType) (rmap : RefMap)
    (hwt : WellTypedState m env lenv retType rmap) :
    ∀ loc, step (.running m) ≠ .error (.danglingRef loc) := by
  sorry

-- ============================================================
-- Part 8: Preservation (sketch)
-- ============================================================

/-- Each step of execution preserves the well-typed state invariant.
    If a well-typed running state steps to another running state,
    then the new state is also well-typed (possibly with a different
    type environment and reference map). -/
theorem preservation (m m' : Machine) (env : TypeEnv) (lenv : LabelEnv)
    (retType : MoveType) (rmap : RefMap)
    (hwt : WellTypedState m env lenv retType rmap)
    (hstep : step (.running m) = .running m') :
    ∃ env' rmap', WellTypedState m' env' lenv retType rmap' := by
  sorry

-- ============================================================
-- Part 9: Main Theorem
-- ============================================================

/-- The main type soundness theorem: a well-typed function never produces
    a danglingRef error at runtime, regardless of fuel. -/
theorem type_soundness (f : FunDef) (lenv : LabelEnv) (funEnv : AssocMap Id FunDef)
    (args : List Value) (heap : Heap)
    (htyped : typecheck_fun f lenv) :
    -- TODO: add hypothesis that args match f.params types
    ∀ n loc, run n (initState f funEnv args heap) ≠ .error (.danglingRef loc) := by
  sorry

end LeanMove.Typing.TypeSoundness
