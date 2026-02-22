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
import LeanMove.Typing.Algorithmic.DecidableTypeEnv

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

/-- allocArgs provides store entries and heap values for each parameter. -/
lemma allocArgs_param_allocated (heap : Heap) (params : List (Var × MoveType))
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
-- Part 11b: hasType_bool decidable check
-- ============================================================

private lemma sizeOf_assocMap_eq (am : AssocMap K V) :
    sizeOf am = 1 + sizeOf am.entries := by
  rcases am with ⟨e⟩; simp [AssocMap.mk.sizeOf_spec]

private lemma sizeOf_lookup_le [BEq α] [SizeOf α] [SizeOf β]
    (l : List (α × β)) (a : α) :
    ∀ b, l.lookup a = some b → sizeOf b < sizeOf l := by
  induction l with
  | nil => intro b h; simp [List.lookup] at h
  | cons hd tl ih =>
    obtain ⟨k, v⟩ := hd
    intro b h
    simp only [List.lookup] at h
    split at h
    · simp only [Option.some.injEq] at h; subst h
      simp only [List.cons.sizeOf_spec, Prod.mk.sizeOf_spec]; omega
    · have := ih b h
      simp only [List.cons.sizeOf_spec]; omega

/-- Decidable check for `HasType`. Uses structural recursion on the type,
    with a `where`-clause helper for record field entries (same pattern as
    `BasicMoveType.beq`). -/
def hasType_bool : Value → BasicMoveType → Bool
  | .int _, .u64 => true
  | .bool _, .tbool => true
  | .unit, .tunit => true
  | .record fields, .trecord fentries =>
      checkFields fields fentries.entries &&
      fields.all (fun p => (List.lookup p.1 fentries.entries).isSome)
  | _, _ => false
where
  checkFields (fields : List (Field × Value)) : List (Field × BasicMoveType) → Bool
    | [] => true
    | (f, bt) :: rest =>
      match fields.lookup f with
      | some v => hasType_bool v bt && checkFields fields rest
      | none => false

-- Manual simp lemmas for hasType_bool (equational theorem generation
-- fails for where-clause mutual definitions in Lean 4.27)
@[simp] theorem hasType_bool_int_u64 (n) : hasType_bool (.int n) .u64 = true := rfl
@[simp] theorem hasType_bool_bool_tbool (b) : hasType_bool (.bool b) .tbool = true := rfl
@[simp] theorem hasType_bool_unit_tunit : hasType_bool .unit .tunit = true := rfl
@[simp] theorem hasType_bool_record_trecord (fields fentries) :
    hasType_bool (.record fields) (.trecord fentries) =
    (hasType_bool.checkFields fields fentries.entries &&
     fields.all (fun p => (List.lookup p.1 fentries.entries).isSome)) := rfl
@[simp] theorem hasType_bool_int_tbool (n) : hasType_bool (.int n) .tbool = false := rfl
@[simp] theorem hasType_bool_int_tunit (n) : hasType_bool (.int n) .tunit = false := rfl
@[simp] theorem hasType_bool_int_trecord (n m) : hasType_bool (.int n) (.trecord m) = false := rfl
@[simp] theorem hasType_bool_bool_u64 (b) : hasType_bool (.bool b) .u64 = false := rfl
@[simp] theorem hasType_bool_bool_tunit (b) : hasType_bool (.bool b) .tunit = false := rfl
@[simp] theorem hasType_bool_bool_trecord (b m) : hasType_bool (.bool b) (.trecord m) = false := rfl
@[simp] theorem hasType_bool_unit_u64 : hasType_bool .unit .u64 = false := rfl
@[simp] theorem hasType_bool_unit_tbool : hasType_bool .unit .tbool = false := rfl
@[simp] theorem hasType_bool_unit_trecord (m) : hasType_bool .unit (.trecord m) = false := rfl
@[simp] theorem hasType_bool_record_u64 (f) : hasType_bool (.record f) .u64 = false := rfl
@[simp] theorem hasType_bool_record_tbool (f) : hasType_bool (.record f) .tbool = false := rfl
@[simp] theorem hasType_bool_record_tunit (f) : hasType_bool (.record f) .tunit = false := rfl
@[simp] theorem hasType_bool_ref_u64 (l p) : hasType_bool (.ref l p) .u64 = false := rfl
@[simp] theorem hasType_bool_ref_tbool (l p) : hasType_bool (.ref l p) .tbool = false := rfl
@[simp] theorem hasType_bool_ref_tunit (l p) : hasType_bool (.ref l p) .tunit = false := rfl
@[simp] theorem hasType_bool_ref_trecord (l p m) : hasType_bool (.ref l p) (.trecord m) = false := rfl

/-- If fields.all checks that every value-field key exists in the type entries,
    then List.lookup on the value succeeding implies List.lookup on the type succeeds. -/
private theorem all_lookup_cover (fields : List (Field × Value)) (entries : List (Field × BasicMoveType))
    (hall : fields.all (fun p => (List.lookup p.1 entries).isSome) = true)
    (f : Field) (hne : fields.lookup f ≠ none) : List.lookup f entries ≠ none := by
  induction fields with
  | nil => simp [List.lookup] at hne
  | cons hd tl ih =>
    obtain ⟨k, v⟩ := hd
    simp only [List.all_cons, Bool.and_eq_true] at hall
    obtain ⟨hhd, htl⟩ := hall
    simp only [List.lookup] at hne
    by_cases hfk : f = k
    · subst hfk; simp only [Option.isSome_iff_ne_none] at hhd; exact hhd
    · simp only [show (f == k) = false from beq_eq_false_iff_ne.mpr hfk] at hne
      exact ih htl hne

mutual
  theorem hasType_bool_sound : ∀ (v : Value) (bt : BasicMoveType),
      hasType_bool v bt = true → HasType v bt
    | .int n, .u64, _ => HasType.int n
    | .bool b, .tbool, _ => HasType.bool b
    | .unit, .tunit, _ => HasType.unit
    | .record fields, .trecord fentries, h => by
        simp only [hasType_bool_record_trecord, Bool.and_eq_true] at h
        obtain ⟨hcheck, hcover⟩ := h
        exact HasType.record fields fentries
          (by
            intro f hne
            cases hf : lookup fentries f with
            | none => exact absurd hf hne
            | some bt' =>
              obtain ⟨v, hv, _⟩ := hasType_checkFields_sound fields fentries.entries hcheck f bt'
                (lookup_some fentries f bt' hf)
              rw [hv]; exact Option.some_ne_none _)
          (by
            intro f hne
            exact all_lookup_cover fields fentries.entries hcover f hne)
          (by
            intro f bt' v' hlookup hfield
            obtain ⟨v'', hv'', hht⟩ := hasType_checkFields_sound fields fentries.entries hcheck f bt'
              (lookup_some fentries f bt' hlookup)
            rw [hfield] at hv''; simp only [Option.some.injEq] at hv''; subst hv''
            exact hht)
    | .int _, .tbool, h => by simp at h
    | .int _, .tunit, h => by simp at h
    | .int _, .trecord _, h => by simp at h
    | .bool _, .u64, h => by simp at h
    | .bool _, .tunit, h => by simp at h
    | .bool _, .trecord _, h => by simp at h
    | .unit, .u64, h => by simp at h
    | .unit, .tbool, h => by simp at h
    | .unit, .trecord _, h => by simp at h
    | .record _, .u64, h => by simp at h
    | .record _, .tbool, h => by simp at h
    | .record _, .tunit, h => by simp at h
    | .ref _ _, .u64, h => by simp at h
    | .ref _ _, .tbool, h => by simp at h
    | .ref _ _, .tunit, h => by simp at h
    | .ref _ _, .trecord _, h => by simp at h
  termination_by v bt _ => sizeOf v + sizeOf bt
  decreasing_by all_goals (simp_wf; rcases fentries with ⟨e⟩; simp [AssocMap.mk.sizeOf_spec]; omega)

  theorem hasType_checkFields_sound : ∀ (fields : List (Field × Value))
      (entries : List (Field × BasicMoveType)),
      hasType_bool.checkFields fields entries = true →
      ∀ f bt, (f, bt) ∈ entries →
      ∃ v, fields.lookup f = some v ∧ HasType v bt
    | _, [], _, _, _, hmem => absurd hmem List.not_mem_nil
    | fields, (f', bt') :: rest, h, f, bt, hmem => by
        simp only [hasType_bool.checkFields] at h
        cases hv : fields.lookup f' with
        | none => rw [hv] at h; simp at h
        | some v' =>
          rw [hv] at h
          simp only [Bool.and_eq_true] at h
          simp only [List.mem_cons, Prod.mk.injEq] at hmem
          rcases hmem with ⟨rfl, rfl⟩ | hmem'
          · exact ⟨v', hv, hasType_bool_sound v' bt h.1⟩
          · exact hasType_checkFields_sound fields rest h.2 f bt hmem'
  termination_by fields entries _ _ bt _ => sizeOf fields + sizeOf entries
  decreasing_by all_goals (simp_wf; first | omega | (subst_vars; rcases (sizeOf_lookup_le fields f v' hv) with _; omega))
end

/-- Boolean check that all basic-typed arguments have matching types. -/
def checkArgsTyped (params : List (Var × MoveType)) (args : List Value) : Bool :=
  (params.zip args).all (fun ((_, τ), v) =>
    match τ with
    | .basic bt => hasType_bool v bt
    | _ => true)

/-- Boolean check that each argument matches its declared parameter type.
    For basic types: hasType_bool.
    For ref types: the arg is a .ref and the heap has a well-typed value there. -/
def checkArgsCompatible (params : List (Var × MoveType)) (args : List Value) (heap : Heap) : Bool :=
  (params.zip args).all (fun ((_, τ), v) =>
    match τ with
    | .basic bt => hasType_bool v bt
    | .ref bt _r _bk =>
      match v with
      | .ref loc path =>
        match heap.readRef loc path with
        | some val => hasType_bool val bt
        | none => false
      | _ => false)

-- ============================================================
-- Part 11b': Soundness Assumptions
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
structure SoundnessAssumptions (f : FunDef) (lenv : LabelEnv) (funEnv : AssocMap Id FunDef) (heap : Heap) (args : List Value) where
  /-- Every label environment entry is structurally well-formed.
      Not decidable without the decidable type-checking representation (`LabelEnvDec`),
      because `TypeEnv.WellFormed` involves `PathEnv.WellFormed` which constrains
      `PathEnv.paths : Aref × Aref → Regex`, a function that cannot be enumerated
      without the finite decidable representation.
      In practice, established by `check_fun_dec_sound`. -/
  lenv_wf : ∀ l env, lookup lenv l = some env → TypeEnv.WellFormed env

  /-- Valid var refs in lenv entries are tracked in pathEnv.refs -/
  lenv_var_tracked : ∀ l env, lookup lenv l = some env →
    ∀ x bt r bk ms, lookup env.varEnv x = some (.validVar, .ref bt r bk, ms) →
    r ∈ env.pathEnv.refs

  /-- No two distinct valid vars in an lenv entry share the same ref -/
  lenv_var_unique : ∀ l env, lookup lenv l = some env →
    ∀ r x y bt bt' bk bk' ms ms', x ≠ y →
    lookup env.varEnv x = some (.validVar, .ref bt r bk, ms) →
    lookup env.varEnv y = some (.validVar, .ref bt' r bk', ms') → False

  /-- All label environment entries have the same funEnv.
      Since funEnv never changes during execution or type checking, all environments
      in lenv should share the same function signature table. -/
  lenv_funEnv_consistent : ∀ l1 l2 env1 env2,
    lookup lenv l1 = some env1 → lookup lenv l2 = some env2 →
    env1.funEnv = env2.funEnv

  /-- Each argument matches its declared parameter type.
      For basic params: HasType v bt.
      For ref params: the arg is a .ref loc path, and the heap has a well-typed value there. -/
  args_compatible : ∀ x τ v, ((x, τ), v) ∈ (f.params.zip args) →
    match τ with
    | .basic bt => HasType v bt
    | .ref bt _r _bk => ∃ loc path, v = .ref loc path ∧
        (∃ val, heap.readRef loc path = some val ∧ HasType val bt)

  /-- Abstract refs in ref-typed params are pairwise distinct.
      Required for live_refs_unique at the initial state. -/
  param_refs_distinct : (f.params.filterMap (fun (_, τ) => match τ with
    | .ref _ r _ => some r | _ => none)).Nodup

  /-- No param ref is .root. Required for rmap_root_none at the initial state. -/
  param_refs_not_root : ∀ x bt r bk, (x, .ref bt r bk) ∈ f.params → r ≠ .root

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

  /-- Parameter names are unique. Required to connect `allocArgs` (first occurrence wins)
      with `init_fun_varEnv` (foldl, last occurrence wins) — they agree when names are unique. -/
  params_nodup : (f.params.map Prod.fst).Nodup

  /-- Entry block varEnv matches init_fun_varEnv exactly (not just MoveType.compatible).
      This ensures that the abstract refs in the entry block's var types are exactly
      the param refs, needed for rmap construction at the initial state.
      (MoveType.compatible allows different refids, which would break rmap.) -/
  entry_varEnv_exact : ∀ block env, f.blocks.head? = some block →
    lookup lenv block.label = some env → LookupEquiv env.varEnv (init_fun_varEnv f)

  /-- Every function signature in every label environment entry has a matching
      runtime function definition in `funEnv`. Required for `funEnv_sig_consistent`
      in `WellTypedState` and for the `call` preservation case. -/
  funEnv_sig : ∀ l env, lookup lenv l = some env →
    ∀ fname sig, lookup env.funEnv fname = some sig →
    ∃ fdef, lookup funEnv fname = some fdef ∧
            fdef.params.map (fun (_, τ) => τ.toParamType) = sig.params ∧
            fdef.returnType = sig.returnType

/-- Boolean check for all decidable hypotheses of type soundness.
    Includes `check_fun_dec` (function type-checks), `checkFunEnv`
    (function environment well-typed), and the decidable fields of
    `SoundnessAssumptions`. -/
def SoundnessAssumptions.checkDecidable (f : FunDef) (lenvDec : LabelEnvDec)
    (funEnv : AssocMap Id FunDef) (fte : FunTypingEnv)
    (heap : Heap) (args : List Value) : Bool :=
  -- check_fun_dec: function type checks + label env well-formedness
  check_fun_dec f lenvDec &&
  -- checkFunEnv: all functions in funEnv are well-typed
  checkFunEnv funEnv fte &&
  -- args_compatible: each argument matches its declared type (basic or ref)
  checkArgsCompatible f.params args heap &&
  -- param_refs_distinct: abstract refs in ref-typed params are pairwise distinct
  decide ((f.params.filterMap (fun (_, τ) => match τ with
    | .ref _ r _ => some r | _ => none)).Nodup) &&
  -- param_refs_not_root: no param ref is .root
  f.params.all (fun (_, τ) => match τ with | .ref _ .root _ => false | _ => true) &&
  -- heap_wf: all locations in heap store are below nextLoc
  heap.store.entries.all (fun (loc, _) => decide (loc < heap.nextLoc)) &&
  -- lenv_empty_sites: all siteEnvs in lenv entries are empty
  lenvDec.entries.all (fun (_, ted) => ted.siteEnv.isEmpty) &&
  -- lenv_complete: every block label appears in lenv
  f.blocks.all (fun block => lenvDec.entries.any (fun (l, _) => l == block.label)) &&
  -- lenv_allWellFormed: PathEnvDec well-formedness (enables non-member / self-loop properties)
  LabelEnvDec.allWellFormed_bool lenvDec &&
  -- lenv_varRefsTracked: all valid var refs tracked in pathEnv
  LabelEnvDec.allVarRefsTracked_bool lenvDec &&
  -- lenv_varRefsUnique: valid var refs are pairwise distinct
  LabelEnvDec.allVarRefsUnique_bool lenvDec &&
  -- params_nodup: parameter names are unique
  decide ((f.params.map Prod.fst).Nodup) &&
  -- entry_varEnv_exact: entry block varEnv matches init_fun_varEnv exactly
  (match f.blocks.head? with
   | some block =>
     match AssocMap.lookup lenvDec block.label with
     | some ted => lookup_equiv_bool ted.varEnv (init_fun_varEnv f)
     | none => true
   | none => true) &&
  -- lenv_funEnvConsistent: all lenv entries share the same funEnv
  LabelEnvDec.checkFunEnvConsistent lenvDec &&
  -- lenv_funEnvSigs: all lenv entries' funEnv matches runtime funEnv
  checkFunEnvSigs lenvDec funEnv

/-- Soundness: if checkFunEnv succeeds, every function in funEnv satisfies FunTypeSafe. -/
theorem checkFunEnv_sound (funEnv : AssocMap Id FunDef) (fte : FunTypingEnv) :
    checkFunEnv funEnv fte = true →
    ∀ fname fdef, lookup funEnv fname = some fdef →
      FunTypeSafe fdef funEnv := by
  intro hcheck fname fdef hlookup
  simp only [checkFunEnv, List.all_eq_true] at hcheck
  have hmem := lookup_some funEnv fname fdef hlookup
  have hentry := hcheck (fname, fdef) hmem
  split at hentry
  · next lenvDec _ =>
    -- Peel off 10 && conjuncts (11 total checks)
    rw [Bool.and_eq_true] at hentry; obtain ⟨hentry, heve⟩ := hentry
    rw [Bool.and_eq_true] at hentry; obtain ⟨hentry, hpnr⟩ := hentry
    rw [Bool.and_eq_true] at hentry; obtain ⟨hentry, hprd⟩ := hentry
    rw [Bool.and_eq_true] at hentry; obtain ⟨hentry, hpnd⟩ := hentry
    rw [Bool.and_eq_true] at hentry; obtain ⟨hentry, hsigs⟩ := hentry
    rw [Bool.and_eq_true] at hentry; obtain ⟨hentry, hfec⟩ := hentry
    rw [Bool.and_eq_true] at hentry; obtain ⟨hentry, hvru⟩ := hentry
    rw [Bool.and_eq_true] at hentry; obtain ⟨hentry, hvrt⟩ := hentry
    rw [Bool.and_eq_true] at hentry; obtain ⟨hentry, hcomp⟩ := hentry
    rw [Bool.and_eq_true] at hentry; obtain ⟨hcfd, hes⟩ := hentry
    exact ⟨lenvDec.toLabelEnv,
      check_fun_dec_sound fdef lenvDec hcfd,
      check_fun_dec_lenv_wf fdef lenvDec hcfd,
      -- empty siteEnv
      fun L envL hlookup s => by
        obtain ⟨ted, hted, rfl⟩ := toLabelEnv_lookup_some lenvDec L envL hlookup
        simp only [List.all_eq_true] at hes
        have hchk := hes (L, ted) (lookup_some lenvDec L ted hted)
        have hempty : ted.siteEnv.entries = [] := by
          cases h : ted.siteEnv.entries with
          | nil => rfl
          | cons _ _ => simp [AssocMap.isEmpty, h] at hchk
        show AssocMap.lookup ted.siteEnv s = none
        simp only [AssocMap.lookup, hempty, List.lookup],
      lenvDec_var_tracked lenvDec hvrt,
      lenvDec_var_unique lenvDec hvru,
      checkFunEnvSigs_sound lenvDec funEnv hsigs,
      -- lenv_complete
      fun b hmem => by
        simp only [List.all_eq_true] at hcomp
        have hany := hcomp b hmem
        obtain ⟨ted, hted⟩ := any_beq_implies_list_lookup lenvDec.entries b.label hany
        exact ⟨ted.toTypeEnv, by
          simp only [LabelEnvDec.toLabelEnv, lookup_mapValues]
          show (lookup lenvDec b.label).map TypeEnvDec.toTypeEnv = some ted.toTypeEnv
          rw [show lookup lenvDec b.label = some ted from hted]; rfl⟩,
      fun L envL L' envL' h1 h2 =>
        LabelEnvDec.checkFunEnvConsistent_sound lenvDec hfec L L' envL envL' h1 h2,
      check_fun_dec_lenv_non_member_from fdef lenvDec hcfd,
      check_fun_dec_lenv_non_member_to fdef lenvDec hcfd,
      check_fun_dec_lenv_self_loop fdef lenvDec hcfd,
      -- params_nodup
      by rw [decide_eq_true_eq] at hpnd; exact hpnd,
      -- param_refs_distinct
      by rw [decide_eq_true_eq] at hprd; exact hprd,
      -- param_refs_not_root
      by
        intro x bt r bk hmem hr
        subst hr
        simp only [List.all_eq_true] at hpnr
        have := hpnr (x, .ref bt .root bk) hmem
        simp at this,
      -- entry_varEnv_exact
      by
        intro block env hhead hlookup_env
        obtain ⟨ted, hted, rfl⟩ := toLabelEnv_lookup_some lenvDec block.label env hlookup_env
        show LookupEquiv ted.varEnv (init_fun_varEnv fdef)
        cases hbl : fdef.blocks.head? with
        | none => rw [hbl] at hhead; cases hhead
        | some block' =>
          rw [hbl] at hhead; cases hhead
          simp only [hbl] at heve
          simp only [hted] at heve
          exact lookup_equiv_bool_sound ted.varEnv (init_fun_varEnv fdef) heve⟩
  · next => simp at hentry

/-- Soundness of the decidable check: the boolean check yields the full
    `SoundnessAssumptions`. All properties are derived from `checkDecidable`. -/
theorem SoundnessAssumptions.of_check (f : FunDef) (lenvDec : LabelEnvDec)
    (funEnv : AssocMap Id FunDef) (fte : FunTypingEnv)
    (heap : Heap) (args : List Value)
    (hcheck : SoundnessAssumptions.checkDecidable f lenvDec funEnv fte heap args = true) :
    SoundnessAssumptions f lenvDec.toLabelEnv funEnv heap args where
  -- checkDecidable has 15 conjuncts (14 &&):
  -- 1:check_fun_dec 2:checkFunEnv 3:checkArgsCompatible 4:param_refs_distinct
  -- 5:param_refs_not_root 6:heap_wf 7:lenv_empty_sites 8:lenv_complete
  -- 9:allWellFormed_bool 10:allVarRefsTracked_bool 11:allVarRefsUnique_bool
  -- 12:params_nodup 13:entry_varEnv_exact 14:checkFunEnvConsistent 15:checkFunEnvSigs
  lenv_wf := by
    simp only [checkDecidable, Bool.and_eq_true] at hcheck
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hcfd, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := hcheck
    exact check_fun_dec_lenv_wf f lenvDec hcfd
  lenv_var_tracked := by
    simp only [checkDecidable, Bool.and_eq_true] at hcheck
    obtain ⟨⟨⟨⟨⟨⟨_, hvrt⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := hcheck
    exact lenvDec_var_tracked lenvDec hvrt
  lenv_var_unique := by
    simp only [checkDecidable, Bool.and_eq_true] at hcheck
    obtain ⟨⟨⟨⟨⟨_, hvru⟩, _⟩, _⟩, _⟩, _⟩ := hcheck
    exact lenvDec_var_unique lenvDec hvru
  lenv_funEnv_consistent := by
    simp only [checkDecidable, Bool.and_eq_true] at hcheck
    obtain ⟨⟨_, hfec⟩, _⟩ := hcheck
    exact LabelEnvDec.checkFunEnvConsistent_sound lenvDec hfec
  args_compatible := by
    simp only [checkDecidable, Bool.and_eq_true] at hcheck
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, hac⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := hcheck
    simp only [checkArgsCompatible, List.all_eq_true] at hac
    intro x τ v hmem
    have hentry := hac ((x, τ), v) hmem
    match τ with
    | .basic bt =>
      simp only at hentry
      exact hasType_bool_sound _ _ hentry
    | .ref bt _r _bk =>
      simp only at hentry
      match hv : v, hentry with
      | .ref loc path, hentry =>
        simp only at hentry
        match hr : heap.readRef loc path, hentry with
        | some val, hentry =>
          exact ⟨loc, path, rfl, val, hr, hasType_bool_sound _ _ hentry⟩
  param_refs_distinct := by
    simp only [checkDecidable, Bool.and_eq_true] at hcheck
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, hd⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := hcheck
    exact decide_eq_true_eq.mp hd
  param_refs_not_root := by
    simp only [checkDecidable, Bool.and_eq_true] at hcheck
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, hnr⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := hcheck
    simp only [List.all_eq_true] at hnr
    intro x bt r bk hmem
    have := hnr (x, .ref bt r bk) hmem
    cases r with
    | root => simp at this
    | refid _ => exact Aref.noConfusion
    | paramRef _ => exact Aref.noConfusion
  params_nodup := by
    simp only [checkDecidable, Bool.and_eq_true] at hcheck
    obtain ⟨⟨⟨⟨_, hnd⟩, _⟩, _⟩, _⟩ := hcheck
    exact decide_eq_true_eq.mp hnd
  entry_varEnv_exact := by
    simp only [checkDecidable, Bool.and_eq_true] at hcheck
    obtain ⟨⟨⟨_, heve⟩, _⟩, _⟩ := hcheck
    intro block env hhead hlookup
    obtain ⟨ted, hted, rfl⟩ := toLabelEnv_lookup_some lenvDec block.label env hlookup
    show LookupEquiv ted.varEnv (init_fun_varEnv f)
    apply lookup_equiv_bool_sound
    revert heve; rw [hhead]; dsimp; rw [hted]; exact id
  lenv_paths_from_non_member := by
    simp only [checkDecidable, Bool.and_eq_true] at hcheck
    obtain ⟨⟨⟨⟨⟨⟨⟨_, hwf⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := hcheck
    intro l env hlookup
    obtain ⟨ted, hted, rfl⟩ := toLabelEnv_lookup_some lenvDec l env hlookup
    simp only [LabelEnvDec.allWellFormed_bool, List.all_eq_true] at hwf
    have hwf_ted := hwf (l, ted) (lookup_some lenvDec l ted hted)
    simp only [TypeEnvDec.wellFormed_bool, Bool.and_eq_true] at hwf_ted
    exact PathEnvDec.toPathEnv_non_member_from ted.pathEnv hwf_ted.1.1
  lenv_paths_to_non_member := by
    simp only [checkDecidable, Bool.and_eq_true] at hcheck
    obtain ⟨⟨⟨⟨⟨⟨⟨_, hwf⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := hcheck
    intro l env hlookup
    obtain ⟨ted, hted, rfl⟩ := toLabelEnv_lookup_some lenvDec l env hlookup
    simp only [LabelEnvDec.allWellFormed_bool, List.all_eq_true] at hwf
    have hwf_ted := hwf (l, ted) (lookup_some lenvDec l ted hted)
    simp only [TypeEnvDec.wellFormed_bool, Bool.and_eq_true] at hwf_ted
    exact PathEnvDec.toPathEnv_non_member_to ted.pathEnv hwf_ted.1.1
  lenv_self_loop := by
    intro l env hlookup u p hp
    obtain ⟨ted, _, rfl⟩ := toLabelEnv_lookup_some lenvDec l env hlookup
    simp only [TypeEnvDec.toTypeEnv, PathEnvDec.toPathEnv] at hp
    simp only [↓reduceIte, interpret_regex] at hp
    exact hp
  heap_wf := by
    simp only [checkDecidable, Bool.and_eq_true] at hcheck
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, hh⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := hcheck
    simp only [List.all_eq_true] at hh
    intro loc hread
    unfold Heap.read at hread
    cases hlookup : lookup heap.store loc with
    | none => rw [hlookup] at hread; exact absurd rfl hread
    | some v =>
      exact decide_eq_true_eq.mp (hh (loc, v) (lookup_some heap.store loc v hlookup))
  lenv_empty_sites := by
    simp only [checkDecidable, Bool.and_eq_true] at hcheck
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨_, hs⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := hcheck
    simp only [List.all_eq_true] at hs
    intro l env hlookup s
    obtain ⟨ted, hted, rfl⟩ := toLabelEnv_lookup_some lenvDec l env hlookup
    have hchk := hs (l, ted) (lookup_some lenvDec l ted hted)
    have hempty : ted.siteEnv.entries = [] := by
      cases h : ted.siteEnv.entries with
      | nil => rfl
      | cons _ _ => simp [AssocMap.isEmpty, h] at hchk
    show AssocMap.lookup ted.siteEnv s = none
    simp only [AssocMap.lookup, hempty, List.lookup]
  lenv_complete := by
    simp only [checkDecidable, Bool.and_eq_true] at hcheck
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨_, hc⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := hcheck
    simp only [List.all_eq_true] at hc
    intro block hmem
    have hany := hc block hmem
    obtain ⟨ted, hted⟩ := any_beq_implies_list_lookup lenvDec.entries block.label hany
    exact ⟨ted.toTypeEnv, by
      simp only [LabelEnvDec.toLabelEnv, lookup_mapValues]
      show (lookup lenvDec block.label).map TypeEnvDec.toTypeEnv = some ted.toTypeEnv
      rw [show lookup lenvDec block.label = some ted from hted]; rfl⟩
  funEnv_sig := by
    simp only [checkDecidable, Bool.and_eq_true] at hcheck
    obtain ⟨_, hsigs⟩ := hcheck
    exact checkFunEnvSigs_sound lenvDec funEnv hsigs

-- ============================================================
-- Part 11c: allocArgs_param_has_type + initState_safe
-- ============================================================

/-- allocArgs stores each argument value at a fresh location, preserving HasType.
    If the params/args are zipped and each basic-typed entry has HasType,
    then for any param (x, .basic bt) in the params, the stored value has type bt. -/
lemma allocArgs_param_has_type (heap : Heap) (params : List (Var × MoveType))
    (args : List Value) (heap_out : Heap) (vs : VarStore)
    (hlb : ∀ loc, heap.read loc ≠ none → loc < heap.nextLoc)
    (halloc : allocArgs heap params args = some (heap_out, vs))
    (htyped : ∀ x τ v, ((x, τ), v) ∈ (params.zip args) →
      ∀ bt, τ = .basic bt → HasType v bt)
    (hnodup : (params.map Prod.fst).Nodup) :
    ∀ x bt, (x, MoveType.basic bt) ∈ params →
    ∃ loc v, lookup vs x = some (some loc) ∧ heap_out.read loc = some v ∧ HasType v bt := by
  induction params generalizing heap args heap_out vs with
  | nil => intro x bt hmem; nomatch hmem
  | cons p ps ih =>
    intro x bt hmem
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
        -- Extract nodup: y ∉ ps.map Prod.fst ∧ (ps.map Prod.fst).Nodup
        simp only [List.map, List.nodup_cons] at hnodup
        obtain ⟨hy_notin, hnodup_ps⟩ := hnodup
        simp only [List.mem_cons, Prod.mk.injEq] at hmem
        rcases hmem with ⟨rfl, rfl⟩ | hmem_rest
        · -- head case: x = y, τ_y = .basic bt
          refine ⟨(heap.alloc a).2, a, lookup_insert_same _ _ _, ?_, ?_⟩
          · have hloc : (heap.alloc a).2 < (heap.alloc a).1.nextLoc := by
              simp [Heap.alloc]
            rw [allocArgs_preserves_old_read (heap.alloc a).1 ps as' h' vs' hrec
                (heap.alloc a).2 hloc]
            exact heap_alloc_read_same heap a
          · exact htyped x (.basic bt) a List.mem_cons_self bt rfl
        · -- tail case: (x, .basic bt) ∈ ps
          -- By nodup, x ≠ y (since x ∈ ps.map Prod.fst but y ∉ ps.map Prod.fst)
          have hx_in_ps : x ∈ ps.map Prod.fst :=
            List.mem_map_of_mem hmem_rest
          have heq : x ≠ y := fun h => hy_notin (h ▸ hx_in_ps)
          have ⟨loc, v, hlookup, hread, hht⟩ := ih (heap.alloc a).1 as' h' vs'
            (heap_alloc_preserves_bound heap a hlb) hrec
            (fun x' τ' v' hmem' bt' hbt' =>
              htyped x' τ' v' (List.mem_cons_of_mem _ hmem') bt' hbt')
            hnodup_ps x bt hmem_rest
          exact ⟨loc, v, by rw [lookup_insert_ne _ _ _ _ heq]; exact hlookup, hread, hht⟩

/-- The initial state of a well-typed function is safe.
    Requires that the function type-checks. If initState produces a .running state,
    it is well-typed; if it produces an error, it is not danglingRef. -/
theorem initState_safe (f : FunDef) (lenv : LabelEnv) (funEnv : AssocMap Id FunDef)
    (args : List Value) (heap : Heap)
    (htyped : typecheck_fun f lenv)
    (hfunEnv : ∀ fname fdef, lookup funEnv fname = some fdef → FunTypeSafe fdef funEnv)
    (ha : SoundnessAssumptions f lenv funEnv heap args) :
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
      -- Construct rmap from ref-typed params and their argument values
      let paramRefEntries := (f.params.zip args).filterMap (fun ((_, τ), v) =>
        match τ, v with
        | .ref _ r _, .ref loc path => some (r, (loc, path))
        | _, _ => none)
      let rmap : RefMap := { map := fun r => List.lookup r paramRefEntries }
      -- Destructure equiv into components
      have hequiv_unf := hequiv
      unfold TypeEnv.equiv at hequiv_unf
      obtain ⟨_, hvar_compat, hrefs_equiv, hpaths_equiv⟩ := hequiv_unf
      -- Key fact: blockEnv.varEnv = init_fun_varEnv f (exact, from entry_varEnv_exact)
      have hvarEnv_exact : LookupEquiv blockEnv.varEnv (init_fun_varEnv f) :=
        ha.entry_varEnv_exact ⟨entryLabel, entryBody⟩ blockEnv hhead hlookup
      -- Key facts used in multiple fields
      have hrefs_eq : blockEnv.pathEnv.refs = (init_fun_pathEnv f).refs := by
        rw [hpathEnv] at hrefs_equiv; exact hrefs_equiv
      have hsiteEnv_empty : ∀ s, lookup blockEnv.siteEnv s = none :=
        ha.lenv_empty_sites entryLabel blockEnv hlookup
      -- Helper: from blockEnv valid var lookup, get the exact init type and param membership
      have hvar_init_exact : ∀ x τ ms, lookup blockEnv.varEnv x = some (.validVar, τ, ms) →
          lookup (init_fun_varEnv f) x = some (.validVar, τ, ms) ∧ (x, τ) ∈ f.params := by
        intro x τ ms hlookup_var
        have := hvarEnv_exact x
        rw [hlookup_var] at this
        have hlookup_init := this.symm
        exact ⟨hlookup_init, init_fun_varEnv_valid_in_params f x τ ms hlookup_init⟩
      -- Helper: List.lookup reverse direction
      have list_lookup_mem : ∀ {K V : Type} [inst : BEq K] [inst2 : LawfulBEq K]
          {l : List (K × V)} {k : K} {v : V},
          l.lookup k = some v → (k, v) ∈ l := by
        intro K V _ _ l k v h
        induction l with
        | nil => simp [List.lookup] at h
        | cons hd tl ih =>
          simp only [List.lookup] at h
          split at h
          · rename_i heq
            have hk : k = hd.1 := beq_iff_eq.mp heq
            have hv : hd.2 = v := by injection h
            subst hk; subst hv; exact List.mem_cons_self ..
          · exact List.mem_cons_of_mem _ (ih h)
      -- Helper: rmap.map r = some (loc, path) implies membership in params.zip args
      have hrmap_mem : ∀ r loc path, rmap.map r = some (loc, path) →
          ∃ x bt bk, ((x, .ref bt r bk), .ref loc path) ∈ f.params.zip args := by
        intro r loc path hrmap_eq
        have hmem_entries : (r, (loc, path)) ∈ paramRefEntries :=
          list_lookup_mem hrmap_eq
        simp only [paramRefEntries, List.mem_filterMap] at hmem_entries
        obtain ⟨⟨⟨x, τ⟩, v⟩, hmem_zip, hfm⟩ := hmem_entries
        -- hfm : (match τ, v with | .ref _ r' _, .ref loc' path' => some ... | _, _ => none) = some ...
        -- Only the .ref/.ref case produces `some`, all others give `none`
        revert hfm
        cases τ with
        | basic _ => simp
        | ref bt r' bk =>
          cases v with
          | int _ => simp
          | bool _ => simp
          | unit => simp
          | record _ => simp
          | ref loc' path' =>
            intro hfm
            simp only [Option.some.injEq, Prod.mk.injEq] at hfm
            obtain ⟨rfl, rfl, rfl⟩ := hfm
            exact ⟨x, bt, bk, hmem_zip⟩
      -- Helper: ref param with arg → rmap maps it
      have hrmap_of_param : ∀ x bt r bk loc path,
          ((x, .ref bt r bk), .ref loc path) ∈ f.params.zip args →
          rmap.map r = some (loc, path) := by
        intro x bt r bk loc path hmem_zip
        show List.lookup r paramRefEntries = some (loc, path)
        have hmem_pre : (r, (loc, path)) ∈ paramRefEntries := by
          simp only [paramRefEntries, List.mem_filterMap]
          exact ⟨((x, .ref bt r bk), .ref loc path), hmem_zip, by simp⟩
        have hkeys_nodup : (paramRefEntries.map Prod.fst).Nodup := by
          have hmf : paramRefEntries.map Prod.fst =
            (f.params.zip args).filterMap (fun ((_, τ), v) =>
              match τ, v with | .ref _ r' _, .ref _ _ => some r' | _, _ => none) := by
            simp only [paramRefEntries, List.map_filterMap]
            congr 1
            ext ⟨⟨_, τ⟩, v⟩
            cases τ with
            | basic _ => simp
            | ref _ _ _ => cases v <;> simp
          rw [hmf]
          exact (paramRefKeys_sublist f.params args).nodup ha.param_refs_distinct
        exact list_lookup_of_mem_nodup hmem_pre hkeys_nodup
      -- Helper: allocArgs gives length equality + zip membership
      have hlen_eq : f.params.length = args.length :=
        allocArgs_length_eq heap f.params args heap' paramVarStore hallocArgs
      have hmem_zip_of_param : ∀ x τ, (x, τ) ∈ f.params → ∃ v, ((x, τ), v) ∈ f.params.zip args :=
        fun x τ h => exists_mem_zip_right hlen_eq h
      -- Helper: .root ∈ (init_fun_pathEnv f).refs
      have hroot_in_init : Aref.root ∈ (init_fun_pathEnv f).refs := by
        simp only [init_fun_pathEnv]; exact List.Mem.head _
      -- Helper: .root ∈ blockEnv.pathEnv.refs
      have hroot_in_block : Aref.root ∈ blockEnv.pathEnv.refs :=
        hrefs_eq ▸ hroot_in_init
      -- Helper: heap'.readRef = heap.readRef for locations referenced by rmap
      have hreadRef_preserved : ∀ r loc path, rmap.map r = some (loc, path) →
          heap'.readRef loc path = heap.readRef loc path := by
        intro r loc path hrmap_eq
        obtain ⟨x, bt, bk, hmem_zip⟩ := hrmap_mem r loc path hrmap_eq
        have hcompat := ha.args_compatible x (.ref bt r bk) (.ref loc path) hmem_zip
        obtain ⟨_, _, hveq, _, hreadref, _⟩ := hcompat
        cases hveq
        have hread_ne : heap.read loc ≠ none := by
          intro h; unfold Heap.readRef at hreadref; simp [h] at hreadref
        have hloc := ha.heap_wf loc hread_ne
        have hpreserve := allocArgs_preserves_old_read heap f.params args heap' paramVarStore
          hallocArgs loc hloc
        unfold Heap.readRef; rw [hpreserve]
      refine ⟨blockEnv, lenv, f.returnType, rmap, ?_, ?_⟩
      · -- WellTypedState
        exact {
          env_wf := hblockEnv_wf
          stmt_typed := htyped_entry
          var_consistent := by
            intro x isv τ ms hlookup_var
            have hlookup_init' : lookup (init_fun_varEnv f) x = some (isv, τ, ms) := by
              rw [← hvarEnv_exact x]; exact hlookup_var
            cases isv with
            | validVar =>
              have hparam := init_fun_varEnv_valid_in_params f x τ ms hlookup_init'
              have hnot_local := init_fun_varEnv_valid_not_local f x τ ms hlookup_init'
              -- Get corresponding arg via zip membership
              have ⟨arg_v, hmem_zip⟩ := hmem_zip_of_param x τ hparam
              -- allocArgs stores this exact arg at some location
              have ⟨alloc_loc, hstore, hread⟩ :=
                allocArgs_param_stores_arg heap f.params args heap' paramVarStore
                  ha.heap_wf hallocArgs ha.params_nodup x τ arg_v hmem_zip
              have hlookup_vs : lookup (addLocals paramVarStore f.locals) x = some (some alloc_loc) := by
                rw [addLocals_preserves_lookup paramVarStore f.locals x hnot_local]
                exact hstore
              cases τ with
              | basic bt =>
                have hht := ha.args_compatible x (.basic bt) arg_v hmem_zip
                exact ⟨alloc_loc, arg_v, hlookup_vs, hread, hht⟩
              | ref bt r bk =>
                have hcompat := ha.args_compatible x (.ref bt r bk) arg_v hmem_zip
                obtain ⟨loc, path, hveq, val, hreadref, hht⟩ := hcompat
                subst hveq
                have hrmap_r := hrmap_of_param x bt r bk loc path hmem_zip
                exact ⟨alloc_loc, .ref loc path, hlookup_vs, hread, loc, path, rfl, hrmap_r⟩
            | invalidVar =>
              have hlocal := init_fun_varEnv_invalid_is_local f x τ ms hlookup_init'
              exact Or.inl (addLocals_local_some_none paramVarStore f.locals x hlocal)
          site_consistent := by
            intro s τ hlookup_s
            rw [hsiteEnv_empty s] at hlookup_s; cases hlookup_s
          rmap_live := by
            intro r loc path hrmap_eq
            obtain ⟨x, bt, bk, hmem_zip⟩ := hrmap_mem r loc path hrmap_eq
            have hcompat := ha.args_compatible x (.ref bt r bk) (.ref loc path) hmem_zip
            obtain ⟨_, _, hveq, val, hreadref, _⟩ := hcompat
            cases hveq
            rw [hreadRef_preserved r loc path hrmap_eq, hreadref]
            exact fun h => nomatch h
          rmap_paths := by
            intro r1 r2 hr1 hr2 p hp
            have hpaths_init := hpaths_equiv r1 r2 hr1 hr2
            rw [hpathEnv] at hpaths_init
            by_cases heq : r1 = r2
            · subst heq
              have hself : blockEnv.pathEnv.paths (r1, r1) = Regex.ε := by
                rw [hpaths_init]; simp [init_fun_pathEnv]
              rw [hself] at hp
              have hp_nil := ha.lenv_self_loop entryLabel blockEnv hlookup r1 p (by rw [hself]; exact hp)
              subst hp_nil
              -- PathReflectedInHeap rmap heap' r1 r1 []
              unfold PathReflectedInHeap
              cases hrm : rmap.map r1 with
              | none => exact True.intro
              | some pair =>
                obtain ⟨loc, path⟩ := pair
                intro _
                obtain ⟨x, bt, bk, hmz⟩ := hrmap_mem r1 loc path hrm
                have hcompat : ∃ loc' path', Value.ref loc path = .ref loc' path' ∧
                    (∃ val, heap.readRef loc' path' = some val ∧ HasType val bt) :=
                  ha.args_compatible x (.ref bt r1 bk) (.ref loc path) hmz
                obtain ⟨_, _, hveq, val, hrf, _⟩ := hcompat
                cases hveq
                refine ⟨(List.append_nil path).symm, ?_⟩
                rw [hreadRef_preserved r1 loc path hrm, hrf]
                exact fun h => nomatch h
            · have hempty : blockEnv.pathEnv.paths (r1, r2) = Regex.empty := by
                rw [hpaths_init]; simp [init_fun_pathEnv, heq]
              rw [hempty] at hp; exact absurd hp id
          blocks_typed := by
            intro b hmem benv hlookup_b
            exact hblocks_typed b hmem benv hlookup_b
          lenv_empty_siteEnv := ha.lenv_empty_sites
          lenv_wf := ha.lenv_wf
          lenv_var_tracked := ha.lenv_var_tracked
          lenv_var_unique := ha.lenv_var_unique
          lenv_funEnv_eq := fun L envL h => ha.lenv_funEnv_consistent L entryLabel envL blockEnv h hlookup
          funEnv_typed := hfunEnv
          heap_loc_bound :=
            allocArgs_heap_loc_bound' heap f.params args heap' paramVarStore
              hallocArgs ha.heap_wf
          varEnv_refs_in_pathEnv := by
            intro x bt r bk ms hlookup_var
            have ⟨_, hparam⟩ := hvar_init_exact x (.ref bt r bk) ms hlookup_var
            have hr_in_init : r ∈ (init_fun_pathEnv f).refs := by
              simp only [init_fun_pathEnv]
              apply List.mem_cons_of_mem
              simp only [List.mem_filterMap]
              exact ⟨(x, .ref bt r bk), hparam, by simp⟩
            exact hrefs_eq ▸ hr_in_init
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
            · -- var-var: from param_refs_distinct
              intro x y bt bt' bk bk' ms ms' hne hlookup_x hlookup_y
              have ⟨_, hpx⟩ := hvar_init_exact x (.ref bt r bk) ms hlookup_x
              have ⟨_, hpy⟩ := hvar_init_exact y (.ref bt' r bk') ms' hlookup_y
              exact absurd (nodup_filterMap_params_same_ref f.params ha.params_nodup
                ha.param_refs_distinct hpx hpy) hne
          rmap_root_none := by
            show rmap.map Aref.root = none
            by_contra h
            have ⟨pair, hpair⟩ := Option.ne_none_iff_exists'.mp h
            obtain ⟨rloc, rpath⟩ := pair
            obtain ⟨x, bt, bk, hmem_zip⟩ := hrmap_mem Aref.root rloc rpath hpair
            exact ha.param_refs_not_root x bt Aref.root bk (List.of_mem_zip hmem_zip).1 rfl
          no_paths_to_root := by
            intro u p hp
            by_cases hu : u = Aref.root
            · constructor
              · exact hu
              · have hpaths : blockEnv.pathEnv.paths (.root, .root) = Regex.ε := by
                  have h := hpaths_equiv .root .root hroot_in_block hroot_in_block
                  rw [hpathEnv] at h; simp [init_fun_pathEnv] at h; exact h
                rw [hu, hpaths] at hp; exact hp
            · have hpaths_empty : blockEnv.pathEnv.paths (u, .root) = Regex.empty := by
                by_cases hu_in : u ∈ blockEnv.pathEnv.refs
                · have h := hpaths_equiv u .root hu_in hroot_in_block
                  rw [hpathEnv] at h
                  simp only [init_fun_pathEnv, hu, ↓reduceIte] at h
                  exact h
                · exact hblockEnv_wf.pathEnv_wf.from_untracked_to_root_empty u hu_in hu
              rw [hpaths_empty] at hp; exact hp.elim
          root_path_coherence := by
            intro v y rest hv_in hp loc_v path_v hrmap_v loc_y hlookup_y
            -- paths(.root, v) from init_fun_pathEnv is .empty for v ≠ .root, ε for v = .root
            -- ε only matches p = [], not (.root_to_var y :: rest)
            by_cases hv : v = Aref.root
            · -- v = .root: paths(.root, .root) = ε, only matches []
              subst hv
              have hpaths : blockEnv.pathEnv.paths (.root, .root) = Regex.ε := by
                have h := hpaths_equiv .root .root hroot_in_block hroot_in_block
                rw [hpathEnv] at h; simp [init_fun_pathEnv] at h; exact h
              rw [hpaths] at hp
              -- hp : interpret_regex ε (.root_to_var y :: rest) = False for non-empty path
              have := ha.lenv_self_loop entryLabel blockEnv hlookup .root
                (.root_to_var y :: rest) (by rw [hpaths]; exact hp)
              exact absurd this (by simp)
            · -- v ≠ .root: paths(.root, v) = .empty
              have hpaths_empty : blockEnv.pathEnv.paths (.root, v) = Regex.empty := by
                by_cases hv_in' : v ∈ blockEnv.pathEnv.refs
                · have h := hpaths_equiv .root v hroot_in_block hv_in'
                  rw [hpathEnv] at h
                  have hroot_ne_v : Aref.root ≠ v := fun heq => hv heq.symm
                  simp only [init_fun_pathEnv, show ¬(Aref.root = v) from hroot_ne_v, ite_false] at h
                  exact h
                · exact hblockEnv_wf.pathEnv_wf.refs_complete v hv_in'
              rw [hpaths_empty] at hp; exact hp.elim
          paths_from_non_member_empty :=
            ha.lenv_paths_from_non_member entryLabel blockEnv hlookup
          paths_to_non_member_empty :=
            ha.lenv_paths_to_non_member entryLabel blockEnv hlookup
          self_loop_only_empty :=
            ha.lenv_self_loop entryLabel blockEnv hlookup
          rmap_has_type := by
            intro r bt loc path hrmap_eq hor
            rcases hor with ⟨x, bk, ms, hlookup_x⟩ | ⟨s, bk, hlookup_s⟩
            · have ⟨_, hparam⟩ := hvar_init_exact x (.ref bt r bk) ms hlookup_x
              have ⟨arg_v, hmem_zip⟩ := hmem_zip_of_param x (.ref bt r bk) hparam
              have hcompat : ∃ loc' path', arg_v = .ref loc' path' ∧
                  (∃ val, heap.readRef loc' path' = some val ∧ HasType val bt) :=
                ha.args_compatible x (.ref bt r bk) arg_v hmem_zip
              obtain ⟨loc', path', hveq, val, hreadref, hht⟩ := hcompat
              subst hveq
              have hrmap_r := hrmap_of_param x bt r bk loc' path' hmem_zip
              rw [hrmap_eq] at hrmap_r; cases hrmap_r
              rw [hreadRef_preserved r loc path hrmap_eq]
              exact ⟨val, hreadref, hht⟩
            · rw [hsiteEnv_empty s] at hlookup_s; cases hlookup_s
          funEnv_sig_consistent := by
            intro fname sig hlookup_fe
            exact ha.funEnv_sig entryLabel blockEnv hlookup fname sig hlookup_fe
          refs_tracked_mapped := by
            intro ref href
            rw [hrefs_eq] at href
            simp only [init_fun_pathEnv, List.mem_cons] at href
            rcases href with rfl | href_param
            · exact Or.inl rfl
            · right
              simp only [List.mem_filterMap] at href_param
              obtain ⟨⟨x, τ⟩, hparam, hfm⟩ := href_param
              cases τ with
              | basic _ => simp at hfm
              | ref bt r' bk =>
                simp only [Option.some.injEq] at hfm
                rw [← hfm]
                obtain ⟨v, hmem_zip⟩ := hmem_zip_of_param x (.ref bt r' bk) hparam
                have hcompat := ha.args_compatible x (.ref bt r' bk) v hmem_zip
                obtain ⟨loc, path, hveq, _⟩ := hcompat
                subst hveq
                have hrmap := hrmap_of_param x bt r' bk loc path hmem_zip
                rw [hrmap]; simp
        }
      · -- StackSafe [] none heap' = True
        simp only [StackSafe]


end LeanMove.Typing.TypeSoundness
