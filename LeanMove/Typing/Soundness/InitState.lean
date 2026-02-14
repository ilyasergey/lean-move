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

import LeanMove.Typing.Soundness.SafeExec

/-!
# Type Soundness: Initial State Safety

Proves that the initial state of a well-typed function satisfies `SafeExecState`.
Contains `SoundnessAssumptions` (packaging non-typedness prerequisites with
decidable checks) and the main `initState_safe` theorem.
-/

namespace LeanMove.Typing.TypeSoundness

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Typing
open LeanMove.Semantics
open AssocMap
open Regex

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

  /-- Non-member refs have no outgoing paths.
      `PathEnv.paths` is function-valued and cannot be enumerated without the decidable
      representation. Established by `check_fun_dec_lenv_non_member_from`. -/
  lenv_paths_from_non_member : ∀ l env, lookup lenv l = some env →
    ∀ u v p, u ∉ env.pathEnv.refs → u ≠ .root → u ≠ v →
    ¬interpret_regex (env.pathEnv.paths (u, v)) p

  /-- Non-member refs have no incoming paths.
      `PathEnv.paths` is function-valued and cannot be enumerated without the decidable
      representation. Established by `check_fun_dec_lenv_non_member_to`. -/
  lenv_paths_to_non_member : ∀ l env, lookup lenv l = some env →
    ∀ u v p, v ∉ env.pathEnv.refs → v ≠ .root → u ≠ v →
    ¬interpret_regex (env.pathEnv.paths (u, v)) p

  /-- Self-loops only accept the empty path.
      In the decidable representation, `toPathEnv.paths(u, u) = ε` always.
      Established by `check_fun_dec_lenv_self_loop`. -/
  lenv_self_loop : ∀ l env, lookup lenv l = some env →
    ∀ u p, interpret_regex (env.pathEnv.paths (u, u)) p → p = []

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
    (hlenv_from : ∀ l env, lookup lenv l = some env →
      ∀ u v p, u ∉ env.pathEnv.refs → u ≠ .root → u ≠ v →
      ¬interpret_regex (env.pathEnv.paths (u, v)) p)
    (hlenv_to : ∀ l env, lookup lenv l = some env →
      ∀ u v p, v ∉ env.pathEnv.refs → v ≠ .root → u ≠ v →
      ¬interpret_regex (env.pathEnv.paths (u, v)) p)
    (hlenv_self_loop : ∀ l env, lookup lenv l = some env →
      ∀ u p, interpret_regex (env.pathEnv.paths (u, u)) p → p = [])
    (hcheck : SoundnessAssumptions.checkDecidable f lenv heap = true) :
    SoundnessAssumptions f lenv heap where
  lenv_wf := hlenv_wf
  lenv_paths_from_non_member := hlenv_from
  lenv_paths_to_non_member := hlenv_to
  lenv_self_loop := hlenv_self_loop
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
          paths_from_non_member_empty :=
            ha.lenv_paths_from_non_member entryLabel blockEnv hlookup
          paths_to_non_member_empty :=
            ha.lenv_paths_to_non_member entryLabel blockEnv hlookup
          self_loop_only_empty :=
            ha.lenv_self_loop entryLabel blockEnv hlookup
        }
      · -- StackSafe [] none heap' = True
        simp only [StackSafe]


end LeanMove.Typing.TypeSoundness
