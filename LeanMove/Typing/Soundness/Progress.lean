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

import LeanMove.Typing.Soundness.Defs

/-!
# Type Soundness: Progress

A well-typed running state never produces a `danglingRef` error.
The proof proceeds by showing that `danglingRef` errors only arise from
`readRef` and `writeRef`, and that both succeed when the state is well-typed.
-/

namespace LeanMove.Typing.TypeSoundness

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Typing
open LeanMove.Semantics
open AssocMap
open Regex

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
    (retTypes : List ParamType) (rmap : RefMap)
    (hwt : WellTypedState m env lenv retTypes rmap)
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
    (retTypes : List ParamType) (rmap : RefMap)
    (hwt : WellTypedState m env lenv retTypes rmap)
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
    (retTypes : List ParamType) (rmap : RefMap)
    (hwt : WellTypedState m env lenv retTypes rmap) :
    ∀ loc, step (.running m) ≠ .error (.danglingRef loc) := by
  intro loc habs
  -- Extract which case of step produced the danglingRef
  have hcases := step_danglingRef_source m loc habs
  cases hcases with
  | inl hread =>
    obtain ⟨s, src, cont, hstmt, path, hsrc, hheap⟩ := hread
    exact no_danglingRef_readRef m env lenv retTypes rmap hwt s src cont hstmt loc path hsrc hheap
  | inr hwrite =>
    obtain ⟨dst, val, cont, hstmt, path, v, hdst, hval, hheap⟩ := hwrite
    exact no_danglingRef_writeRef m env lenv retTypes rmap hwt dst val cont hstmt loc path v hdst hval hheap

-- ============================================================
-- Part 8: Helper lemmas for step_error_is_acceptable
-- ============================================================

/-- If a block with label `L` is in the list, `findBlock` succeeds. -/
private theorem findBlock_some_of_mem (blocks : List Block) (L : Label)
    (b : Block) (hmem : b ∈ blocks) (hlabel : b.label = L) :
    ∃ block, findBlock blocks L = some block := by
  induction blocks with
  | nil => simp at hmem
  | cons hd tl ih =>
    simp only [findBlock, List.find?]
    by_cases heq : hd.label == L
    · exact ⟨hd, by simp [heq]⟩
    · rcases List.mem_cons.mp hmem with rfl | htl
      · exfalso; simp [hlabel] at heq
      · simp only [heq]; exact ih htl

/-- A valid variable in the typing environment always has a runtime value via readVar.
    Uses var_consistent from WellTypedState. -/
private theorem readVar_some_of_validVar {m : Machine} {env : TypeEnv}
    {lenv : LabelEnv} {retTypes : List ParamType} {rmap : RefMap}
    {x : Var} {τ : MoveType} {ms : Mut}
    (hwt : WellTypedState m env lenv retTypes rmap)
    (hlookup : lookup env.varEnv x = some (IsValid.validVar, τ, ms)) :
    ∃ v, readVar m x = some v := by
  have h := hwt.var_consistent x IsValid.validVar τ ms hlookup
  obtain ⟨loc, v, hstore, hread, _⟩ := h
  refine ⟨v, ?_⟩
  show readVar m x = some v
  unfold readVar
  simp only [bind, Option.bind, hstore, hread]

/-- A valid variable in the typing environment has a heap location via getVarLoc.
    Uses var_consistent from WellTypedState. -/
private theorem getVarLoc_some_of_validVar {m : Machine} {env : TypeEnv}
    {lenv : LabelEnv} {retTypes : List ParamType} {rmap : RefMap}
    {x : Var} {τ : MoveType} {ms : Mut}
    (hwt : WellTypedState m env lenv retTypes rmap)
    (hlookup : lookup env.varEnv x = some (IsValid.validVar, τ, ms)) :
    ∃ loc, getVarLoc m x = some loc := by
  have h := hwt.var_consistent x IsValid.validVar τ ms hlookup
  obtain ⟨loc, _, hstore, _, _⟩ := h
  refine ⟨loc, ?_⟩
  show getVarLoc m x = some loc
  unfold getVarLoc
  simp only [bind, Option.bind, hstore]

/-- A typed site always has a runtime value via readSite.
    Uses site_consistent from WellTypedState. -/
private theorem readSite_some_of_typed {m : Machine} {env : TypeEnv}
    {lenv : LabelEnv} {retTypes : List ParamType} {rmap : RefMap}
    {s : Site} {τ : MoveType}
    (hwt : WellTypedState m env lenv retTypes rmap)
    (hlookup : lookup env.siteEnv s = some τ) :
    ∃ v, readSite m s = some v := by
  have ⟨v, hv, _⟩ := hwt.site_consistent s τ hlookup
  exact ⟨v, by simp [readSite]; exact hv⟩

/-- If HasType v .tbool, then v is a boolean. -/
private theorem HasType_tbool_is_bool {v : Value} :
    HasType v .tbool → ∃ b, v = .bool b := by
  intro h; cases h with | bool b => exact ⟨b, rfl⟩

/-- If HasType v .u64, then v is an integer. -/
private theorem HasType_u64_is_int {v : Value} :
    HasType v .u64 → ∃ n, v = .int n := by
  intro h; cases h with | int n => exact ⟨n, rfl⟩

/-- If HasType v (.trecord fentries), then v is a record. -/
private theorem HasType_trecord_is_record {v : Value} {fentries : AssocMap Field BasicMoveType} :
    HasType v (.trecord fentries) → ∃ fields, v = .record fields := by
  intro h; cases h with | record fields _ _ _ _ => exact ⟨fields, rfl⟩

/-- If ValueMatchesType v (.ref bt r bk) rmap, then v is a ref value. -/
private theorem ValueMatchesType_ref_is_ref {v : Value} {bt : BasicMoveType}
    {r : Aref} {bk : BorrowingKind} {rmap : RefMap} :
    ValueMatchesType v (.ref bt r bk) rmap → ∃ loc path, v = .ref loc path := by
  intro h
  simp only [ValueMatchesType] at h
  obtain ⟨loc, path, hveq, _⟩ := h
  exact ⟨loc, path, hveq⟩

/-- If ValueMatchesType v (.basic bt) rmap, then HasType v bt. -/
private theorem ValueMatchesType_basic_is_hasType {v : Value} {bt : BasicMoveType} {rmap : RefMap} :
    ValueMatchesType v (.basic bt) rmap → HasType v bt := by
  intro h; exact h

/-- A well-typed function has at least one block. -/
private theorem typecheck_fun_blocks_ne_nil {fdef : FunDef} {lenv : LabelEnv} :
    typecheck_fun fdef lenv → fdef.blocks ≠ [] := by
  intro h; cases h with | fun_ok _ _ _ _ hne _ _ => exact hne

/-- If binop_type returns tbool for bool inputs, evalBinopBool always succeeds. -/
private theorem evalBinopBool_some_of_binop_type_tbool {bop : Binop} {bt3 : BasicMoveType} :
    binop_type bop .tbool .tbool = some bt3 →
    ∀ ba bb, ∃ v, evalBinopBool bop ba bb = some v := by
  intro hbt
  cases bop <;> simp [binop_type] at hbt <;> intro ba bb
  · -- eq
    exact ⟨.bool (ba == bb), rfl⟩
  · -- nand
    exact ⟨.bool (!(ba && bb)), rfl⟩

/-- collectSiteValues succeeds when every site in the list has a value in the store. -/
private theorem collectSiteValues_some (siteStore : SiteStore) (sites : List Site) :
    (∀ s, s ∈ sites → ∃ v, lookup siteStore s = some v) →
    ∃ vals, collectSiteValues siteStore sites = some vals := by
  induction sites with
  | nil => intro _; exact ⟨[], rfl⟩
  | cons s rest ih =>
    intro hall
    have ⟨v, hv⟩ := hall s (List.mem_cons_self ..)
    have ⟨vs, hvs⟩ := ih (fun s' hs' => hall s' (List.mem_cons_of_mem _ hs'))
    exact ⟨v :: vs, by simp [collectSiteValues, hv, hvs, bind, Option.bind]⟩

/-- collectSiteValues preserves the length of the site list. -/
private theorem collectSiteValues_length (siteStore : SiteStore) (sites : List Site) (vals : List Value) :
    collectSiteValues siteStore sites = some vals → vals.length = sites.length := by
  induction sites generalizing vals with
  | nil =>
    intro h; simp [collectSiteValues] at h; subst h; rfl
  | cons s rest ih =>
    intro h; simp [collectSiteValues, bind, Option.bind] at h
    cases hs : lookup siteStore s with
    | none => simp [hs] at h
    | some v =>
      simp [hs] at h
      cases hrs : collectSiteValues siteStore rest with
      | none => simp [hrs] at h
      | some vs =>
        simp [hrs] at h; subst h
        simp [ih vs hrs]

/-- collectPackFields succeeds when every site in the field list has a value in the store. -/
private theorem collectPackFields_some (siteStore : SiteStore) (fields : List (Field × Site)) :
    (∀ f s, (f, s) ∈ fields → ∃ v, lookup siteStore s = some v) →
    ∃ vals, collectPackFields siteStore fields = some vals := by
  induction fields with
  | nil => intro _; exact ⟨[], rfl⟩
  | cons p rest ih =>
    obtain ⟨f, s⟩ := p
    intro hall
    have ⟨v, hv⟩ := hall f s (List.mem_cons_self ..)
    have ⟨vs, hvs⟩ := ih (fun f' s' hs' => hall f' s' (List.mem_cons_of_mem _ hs'))
    exact ⟨(f, v) :: vs, by simp [collectPackFields, hv, hvs, bind, Option.bind]⟩

/-- types_conform implies sites have types in siteEnv. -/
private theorem types_conform_sites_typed {siteEnv : SiteEnv}
    {sites : List Site} {paramTypes : List ParamType} :
    types_conform siteEnv sites paramTypes →
    ∀ s, s ∈ sites → ∃ τ, lookup siteEnv s = some τ := by
  induction sites generalizing paramTypes with
  | nil => intro _ s hs; simp at hs
  | cons s rest ih =>
    intro hconf s' hs'
    cases paramTypes with
    | nil => simp [types_conform] at hconf
    | cons pt pts =>
      simp only [types_conform] at hconf
      cases hlook : lookup siteEnv s with
      | none => simp [hlook] at hconf
      | some τ =>
        simp [hlook] at hconf
        rcases List.mem_cons.mp hs' with rfl | hmem
        · exact ⟨τ, hlook⟩
        · -- Need to extract types_conform for rest from hconf
          cases pt with
          | mk bt isRefMut =>
            cases isRefMut with
            | none =>
              cases τ with
              | basic bt' => exact ih hconf.2 s' hmem
              | ref _ _ _ => simp at hconf
            | some b =>
              cases τ with
              | basic _ => simp at hconf
              | ref bt' r bk => exact ih hconf.2.2 s' hmem

/-- types_conform implies equal lengths. -/
private theorem types_conform_length {siteEnv : SiteEnv}
    {sites : List Site} {paramTypes : List ParamType} :
    types_conform siteEnv sites paramTypes →
    sites.length = paramTypes.length := by
  induction sites generalizing paramTypes with
  | nil =>
    intro h; cases paramTypes with
    | nil => rfl
    | cons _ _ => simp [types_conform] at h
  | cons s rest ih =>
    intro h; cases paramTypes with
    | nil => simp [types_conform] at h
    | cons pt pts =>
      simp only [types_conform] at h
      cases hlook : lookup siteEnv s with
      | none => simp [hlook] at h
      | some τ =>
        simp [hlook] at h
        simp only [List.length_cons]
        cases pt with
        | mk bt isRefMut =>
          cases isRefMut with
          | none =>
            cases τ with
            | basic bt' => exact congr_arg (· + 1) (ih h.2)
            | ref _ _ _ => simp at h
          | some b =>
            cases τ with
            | basic _ => simp at h
            | ref bt' r bk => exact congr_arg (· + 1) (ih h.2.2)

/-- bindReturnValues succeeds when the two lists have equal length. -/
private theorem bindReturnValues_some (siteStore : SiteStore) (sites : List Site) (vals : List Value) :
    sites.length = vals.length →
    ∃ store, bindReturnValues siteStore sites vals = some store := by
  induction sites generalizing vals siteStore with
  | nil =>
    intro h; cases vals with
    | nil => exact ⟨siteStore, rfl⟩
    | cons _ _ => simp at h
  | cons s rest ih =>
    intro h; cases vals with
    | nil => simp at h
    | cons v vs =>
      simp only [List.length_cons] at h
      have hlen : rest.length = vs.length := by omega
      have ⟨store, hstore⟩ := ih (insert siteStore s v) vs hlen
      exact ⟨store, by simp [bindReturnValues, hstore]⟩

/-- allocArgs succeeds when the two lists have equal length. -/
private theorem allocArgs_some (heap : Heap) (params : List (Var × MoveType)) (args : List Value) :
    params.length = args.length →
    ∃ heap' vs, allocArgs heap params args = some (heap', vs) := by
  induction params generalizing args heap with
  | nil =>
    intro h; cases args with
    | nil => exact ⟨heap, AssocMap.empty, rfl⟩
    | cons _ _ => simp at h
  | cons p rest ih =>
    obtain ⟨v, τ⟩ := p
    intro h; cases args with
    | nil => simp at h
    | cons a as' =>
      simp only [List.length_cons] at h
      have hlen : rest.length = as'.length := by omega
      have ⟨heap', vs, hvs⟩ := ih (heap.alloc a).1 as' hlen
      exact ⟨heap', insert vs v (some (heap.alloc a).2),
             by simp [allocArgs, bind, Option.bind, hvs]⟩

/-- collectSiteValues succeeds when all sites are typed and site_consistent holds. -/
private theorem collectSiteValues_some_of_typed {m : Machine} {env : TypeEnv}
    {lenv : LabelEnv} {retTypes : List ParamType} {rmap : RefMap}
    (hwt : WellTypedState m env lenv retTypes rmap)
    (sites : List Site) (paramTypes : List ParamType)
    (hconf : types_conform env.siteEnv sites paramTypes) :
    ∃ vals, collectSiteValues m.frame.siteStore sites = some vals := by
  apply collectSiteValues_some
  intro s hs
  have ⟨τ, hτ⟩ := types_conform_sites_typed hconf s hs
  have ⟨v, hv, _⟩ := hwt.site_consistent s τ hτ
  exact ⟨v, hv⟩

-- ============================================================
-- Part 9: The main progress theorem
-- ============================================================

/-- A well-typed running state steps only to acceptable errors.
    This is the generalized progress theorem: any error produced by `step`
    from a well-typed state must be `divisionByZero`, `outOfFuel`, or `aborted`. -/
theorem step_error_is_acceptable (m : Machine) (env : TypeEnv) (lenv : LabelEnv)
    (retTypes : List ParamType) (rmap : RefMap)
    (hwt : WellTypedState m env lenv retTypes rmap)
    (hss : StackSafe m.stack m.frame.returnInfo m.heap retTypes)
    (e : RuntimeError)
    (hstep : step (.running m) = .error e) :
    e.isAcceptable := by
  -- Case analysis on the current statement
  cases hs : m.frame.stmt with

  -- ========================================
  -- skip: only produces .aborted (acceptable)
  -- ========================================
  | skip =>
    simp only [step, hs] at hstep
    split at hstep
    · simp at hstep
    · simp only [ExecState.error.injEq] at hstep; subst hstep; simp

  -- ========================================
  -- abort: always produces .aborted (acceptable)
  -- ========================================
  | abort msg =>
    simp only [step, hs] at hstep
    simp only [ExecState.error.injEq] at hstep; subst hstep; simp

  -- ========================================
  -- release: always succeeds (no error)
  -- ========================================
  | release site cont =>
    simp only [step, hs] at hstep; cases hstep

  -- ========================================
  -- jump L: only error is unknownLabel, contradicted by lenv
  -- ========================================
  | jump label =>
    have hst := hwt.stmt_typed
    rw [hs] at hst
    simp only [step, hs] at hstep
    cases hst
    next _ hlookup =>
      have ⟨block, hmem, hlbl⟩ := hwt.lenv_labels_in_blocks label _ hlookup
      have ⟨_, hfb⟩ := findBlock_some_of_mem m.frame.blocks label block hmem hlbl
      rw [hfb] at hstep; cases hstep

  -- ========================================
  -- branch condSite l1 l2
  -- ========================================
  | branch condSite l1 l2 =>
    have hst := hwt.stmt_typed
    rw [hs] at hst
    simp only [step, hs] at hstep
    -- next order: hcond, hsub1, hsub2, hlookup1, hlookup2
    cases hst
    next hcond _ _ hlookup1 hlookup2 =>
      have ⟨vv, hvv, hmatch⟩ := hwt.site_consistent condSite (.basic .tbool) hcond
      have ⟨b, hb⟩ := HasType_tbool_is_bool (ValueMatchesType_basic_is_hasType hmatch)
      subst hb
      change lookup m.frame.siteStore condSite = some _ at hvv
      simp only [readSite, hvv] at hstep
      cases b with
      | true =>
        have ⟨block1, hmem1, hlbl1⟩ := hwt.lenv_labels_in_blocks l1 _ hlookup1
        have ⟨_, hfb1⟩ := findBlock_some_of_mem m.frame.blocks l1 block1 hmem1 hlbl1
        rw [hfb1] at hstep; cases hstep
      | false =>
        have ⟨block2, hmem2, hlbl2⟩ := hwt.lenv_labels_in_blocks l2 _ hlookup2
        have ⟨_, hfb2⟩ := findBlock_some_of_mem m.frame.blocks l2 block2 hmem2 hlbl2
        rw [hfb2] at hstep; cases hstep

  -- ========================================
  -- ret sites
  -- ========================================
  | ret sites =>
    have hst := hwt.stmt_typed
    rw [hs] at hst
    simp only [step, hs] at hstep
    -- next order: a1=nolocal, a2=write, a3=noalias, a4=types_conform
    cases hst
    next _ _ _ hconf =>
      -- collectSiteValues succeeds
      have ⟨vals, hvals⟩ := collectSiteValues_some_of_typed hwt sites retTypes hconf
      rw [hvals] at hstep
      simp only at hstep
      -- Case split on stack
      cases hstack : m.stack with
      | nil => rw [hstack] at hstep; simp at hstep
      | cons callerFrame rest =>
        rw [hstack] at hstep
        simp only at hstep
        -- returnInfo must be some (from has_return_info)
        have hri_some := hwt.has_return_info (by rw [hstack]; simp)
        cases hri : m.frame.returnInfo with
        | none =>
          rw [hri] at hri_some; simp at hri_some
        | some ri =>
          rw [hri] at hstep
          simp only at hstep
          -- From StackSafe, extract types_conform for caller's result sites
          rw [hstack, hri] at hss
          simp only [StackSafe] at hss
          obtain ⟨_, _, _, _, hbig, _⟩ := hss
          -- types_conform is the very last conjunct in hbig
          have hconf_caller := hbig.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
          have hlen_sites := types_conform_length hconf
          have hlen_vals := collectSiteValues_length m.frame.siteStore sites vals hvals
          have hlen_ri := types_conform_length hconf_caller
          have hlen_eq : ri.resultSites.length = vals.length := by
            rw [hlen_vals, hlen_sites]; exact hlen_ri
          have ⟨store, hstore⟩ := bindReturnValues_some callerFrame.siteStore ri.resultSites vals hlen_eq
          rw [hstore] at hstep; cases hstep

  -- ========================================
  -- assign x site cont
  -- ========================================
  | assign x site cont =>
    have hst := hwt.stmt_typed
    rw [hs] at hst
    simp only [step, hs] at hstep
    cases hst
    -- var_assign_valid: a8=hvar, try a9 as hsite
    next _ _ _ _ _ _ _ _ hsite _ =>
      have ⟨v, hv, _⟩ := hwt.site_consistent site _ hsite
      change lookup m.frame.siteStore site = some v at hv
      simp only [readSite, hv] at hstep; cases hstep
    -- var_assign_invalid: a4=hvar_invalid, try a5 as hsite
    next _ _ _ _ hsite _ =>
      have ⟨v, hv, _⟩ := hwt.site_consistent site _ hsite
      change lookup m.frame.siteStore site = some v at hv
      simp only [readSite, hv] at hstep; cases hstep

  -- ========================================
  -- unpack fieldSites src cont
  -- ========================================
  | unpack fieldSites src cont =>
    have hst := hwt.stmt_typed
    rw [hs] at hst
    simp only [step, hs] at hstep
    cases hst
    -- unpack: fentries, hsrc, hfresh, hnodup, htyped, hcont (6 things)
    next fentries a2 a3 a4 a5 a6 =>
      -- Try a5 as hsrc (lookup siteEnv b = some (.basic (.trecord fentries)))
      have ⟨vv, hvv, hmatch⟩ := hwt.site_consistent src (.basic (.trecord fentries)) a5
      have ⟨fields, hfields⟩ := HasType_trecord_is_record (ValueMatchesType_basic_is_hasType hmatch)
      subst hfields
      change lookup m.frame.siteStore src = some _ at hvv
      simp only [readSite, hvv] at hstep; cases hstep

  -- ========================================
  -- writeRef dst val cont
  -- ========================================
  | writeRef dst val cont =>
    have hst := hwt.stmt_typed
    rw [hs] at hst
    simp only [step, hs] at hstep
    cases hst
    -- write_ref: a1=τ, a2=r, a3=check_outbound, a4=hlookup_dst, a5=hlookup_val, a6=hcont
    next τ_bt r_ref _ hlookup_dst hlookup_val _ =>
      have ⟨vd, hvd, hmatchd⟩ := hwt.site_consistent dst (.ref τ_bt r_ref .siteBorrowMut) hlookup_dst
      have ⟨loc, path, hvd_eq⟩ := ValueMatchesType_ref_is_ref hmatchd
      have ⟨vv, hvv, _⟩ := hwt.site_consistent val (.basic τ_bt) hlookup_val
      change lookup m.frame.siteStore dst = some vd at hvd
      change lookup m.frame.siteStore val = some vv at hvv
      subst hvd_eq
      simp only [readSite, hvd, hvv] at hstep
      have hwrite := no_danglingRef_writeRef m env lenv retTypes rmap hwt
        dst val cont hs loc path vv
        (by simp [readSite, hvd])
        (by simp [readSite, hvv])
      cases hw : m.heap.writeRef loc path vv with
      | none => exact absurd hw hwrite
      | some heap' => rw [hw] at hstep; cases hstep

  -- ========================================
  -- call resultSites fname argSites cont
  -- ========================================
  | call resultSites fname argSites cont =>
    have hst := hwt.stmt_typed
    rw [hs] at hst
    simp only [step, hs] at hstep
    cases hst
    -- call: a1=params, a2=rets, a3=outRefs, a4=env', a10=hfun_sig, a11=hconf_in
    next params rets _ _ _ _ _ _ _ hfun_sig hconf_in _ _ =>
      -- lookup funEnv fname succeeds
      have ⟨fdef, hfdef, hparams_eq, _⟩ := hwt.funEnv_sig_consistent fname ⟨params, rets⟩ hfun_sig
      change lookup m.frame.funEnv fname = some fdef at hfdef
      rw [hfdef] at hstep
      simp only at hstep
      -- collectSiteValues for args succeeds
      have ⟨argVals, hargVals⟩ := collectSiteValues_some_of_typed hwt argSites params hconf_in
      rw [hargVals] at hstep
      simp only at hstep
      -- allocArgs succeeds
      have hlen_params : fdef.params.length = argVals.length := by
        have hlen1 := types_conform_length hconf_in
        have hlen2 := collectSiteValues_length m.frame.siteStore argSites argVals hargVals
        have hlen3 : fdef.params.length = params.length := by
          have := congr_arg List.length hparams_eq
          simp only [List.length_map] at this; exact this
        omega
      have ⟨heap', vs, hvs⟩ := allocArgs_some m.heap fdef.params argVals hlen_params
      rw [hvs] at hstep
      simp only at hstep
      -- fdef.blocks.head? succeeds (from funEnv_typed -> typecheck_fun -> blocks ≠ [])
      have hfts := hwt.funEnv_typed fname fdef hfdef
      obtain ⟨_, htf, _⟩ := hfts
      have hne := typecheck_fun_blocks_ne_nil htf
      cases hblocks : fdef.blocks with
      | nil => exact absurd hblocks hne
      | cons b bs =>
        rw [hblocks] at hstep; simp only [List.head?] at hstep
        cases hstep

  -- ========================================
  -- letBind s expr cont: case analysis on expr
  -- ========================================
  | letBind s expr cont =>
    have hst := hwt.stmt_typed
    rw [hs] at hst
    cases expr with

    -- ---- intLit: always succeeds ----
    | intLit n =>
      simp only [step, hs] at hstep; cases hstep

    -- ---- usage u: case analysis on u ----
    | usage u =>
      cases u with
      | copy x =>
        simp only [step, hs] at hstep
        cases hst
        -- let_bind_copy_val: bt, ms, hnotin, hlookup_var, hcont
        next _ _ _ hvar _ =>
          have ⟨v, hv⟩ := readVar_some_of_validVar hwt hvar
          rw [hv] at hstep; cases hstep
        -- let_bind_copy_ref: τ, ms, s, t, isBor, hfresh, hnotin, hlookup_var, hcont
        next _ _ _ _ _ _ _ hvar _ =>
          have ⟨v, hv⟩ := readVar_some_of_validVar hwt hvar
          rw [hv] at hstep; cases hstep

      | move x =>
        simp only [step, hs] at hstep
        cases hst
        next _ _ _ hvar _ _ =>
          have ⟨v, hv⟩ := readVar_some_of_validVar hwt hvar
          rw [hv] at hstep; cases hstep

      | borrowImm x =>
        simp only [step, hs] at hstep
        cases hst
        next _ _ _ _ _ hvar _ =>
          have ⟨loc, hloc⟩ := getVarLoc_some_of_validVar hwt hvar
          rw [hloc] at hstep; cases hstep

      | borrowMut x =>
        simp only [step, hs] at hstep
        cases hst
        next _ _ _ _ _ _ hvar _ =>
          have ⟨loc, hloc⟩ := getVarLoc_some_of_validVar hwt hvar
          rw [hloc] at hstep; cases hstep

    -- ---- borrowField src bt field ----
    -- Constructor: bt', isBor, fentries, s, rf + 6 premises: hsrc, hbt_eq, hfield, hnotin, hfresh, hcont
    -- Total 11 non-index args. Need hsrc (lookup siteEnv)
    | borrowField src bt field =>
      simp only [step, hs] at hstep
      cases hst
      next _ _ _ _ _ _ hsrc _ _ =>
        have ⟨vv, hvv, hmatch⟩ := hwt.site_consistent src _ hsrc
        have ⟨loc, path, hvv_eq⟩ := ValueMatchesType_ref_is_ref hmatch
        subst hvv_eq
        change lookup m.frame.siteStore src = some _ at hvv
        simp only [readSite, hvv] at hstep; cases hstep

    | borrowMutField src bt field =>
      simp only [step, hs] at hstep
      cases hst
      next _ _ _ _ _ _ hsrc _ _ =>
        have ⟨vv, hvv, hmatch⟩ := hwt.site_consistent src _ hsrc
        have ⟨loc, path, hvv_eq⟩ := ValueMatchesType_ref_is_ref hmatch
        subst hvv_eq
        change lookup m.frame.siteStore src = some _ at hvv
        simp only [readSite, hvv] at hstep; cases hstep

    | readRef src =>
      simp only [step, hs] at hstep
      cases hst
      next r_ref τ_bt isBor_ref _ hsrc _ =>
        have ⟨vv, hvv, hmatch⟩ := hwt.site_consistent src (.ref τ_bt r_ref isBor_ref) hsrc
        have ⟨loc, path, hvv_eq⟩ := ValueMatchesType_ref_is_ref hmatch
        subst hvv_eq
        change lookup m.frame.siteStore src = some _ at hvv
        simp only [readSite, hvv] at hstep
        have hread := no_danglingRef_readRef m env lenv retTypes rmap hwt
          s src cont hs loc path
          (by simp [readSite, hvv])
        cases hr : m.heap.readRef loc path with
        | none => exact absurd hr hread
        | some v => rw [hr] at hstep; cases hstep

    | freeze src =>
      simp only [step, hs] at hstep
      cases hst
      next _ _ _ _ _ _ hsrc _ =>
        have ⟨v, hv, _⟩ := hwt.site_consistent src _ hsrc
        change lookup m.frame.siteStore src = some v at hv
        simp only [readSite, hv] at hstep; cases hstep

    | pack name fieldSites =>
      simp only [step, hs] at hstep
      cases hst
      next a1 a2 a3 a4 a5 a6 =>
        -- a2=notIn, a3=hcoverage. Try a5 for hfields_typed
        have hcpf := collectPackFields_some m.frame.siteStore fieldSites (by
          intro f s_site hmem
          have ⟨bt, hbt, _⟩ := a5 f s_site hmem
          have ⟨v, hv, _⟩ := hwt.site_consistent s_site (.basic bt) hbt
          exact ⟨v, hv⟩)
        obtain ⟨vals, hvals⟩ := hcpf
        rw [hvals] at hstep; cases hstep

    | binop op a b =>
      simp only [step, hs] at hstep
      cases hst
      -- a1=bt1, a2=bt2, a3=bt3, a4=?, a5=binop_type, a6=ha, a7=hb, a8=hcont
      next bt1 bt2 bt3 _ hbinop ha hb _ =>
        have ⟨va, hva, hma⟩ := hwt.site_consistent a (.basic bt1) ha
        have ⟨vb, hvb, hmb⟩ := hwt.site_consistent b (.basic bt2) hb
        have hta : HasType va bt1 := ValueMatchesType_basic_is_hasType hma
        have htb : HasType vb bt2 := ValueMatchesType_basic_is_hasType hmb
        change lookup m.frame.siteStore a = some va at hva
        change lookup m.frame.siteStore b = some vb at hvb
        simp only [readSite, hva, hvb] at hstep
        cases bt1 with
        | u64 =>
          have ⟨na, hna⟩ := HasType_u64_is_int hta
          subst hna
          cases bt2 with
          | u64 =>
            have ⟨nb, hnb⟩ := HasType_u64_is_int htb
            subst hnb
            dsimp only at hstep
            cases hev : evalBinop op na nb with
            | none =>
              rw [hev] at hstep
              simp only [ExecState.error.injEq] at hstep
              subst hstep; simp
            | some v =>
              rw [hev] at hstep
              cases hstep
          | tbool =>
            have ⟨nb, hnb⟩ := HasType_tbool_is_bool htb
            subst hnb
            cases op <;> simp [binop_type] at hbinop
          | tunit =>
            cases htb
            cases op <;> simp [binop_type] at hbinop
          | trecord _ => cases op <;> simp [binop_type] at hbinop
        | tbool =>
          have ⟨ba, hba⟩ := HasType_tbool_is_bool hta
          subst hba
          cases bt2 with
          | tbool =>
            have ⟨bb, hbb⟩ := HasType_tbool_is_bool htb
            subst hbb
            dsimp only at hstep
            have ⟨v, hv⟩ := evalBinopBool_some_of_binop_type_tbool hbinop ba bb
            rw [hv] at hstep
            cases hstep
          | u64 =>
            have ⟨nb, hnb⟩ := HasType_u64_is_int htb
            subst hnb
            cases op <;> simp [binop_type] at hbinop
          | tunit =>
            cases htb
            cases op <;> simp [binop_type] at hbinop
          | trecord _ =>
            have ⟨flds, hf⟩ := HasType_trecord_is_record htb
            subst hf
            cases op <;> simp [binop_type] at hbinop
        | tunit =>
          cases hta
          cases op <;> (cases bt2 <;> simp [binop_type] at hbinop)
        | trecord _ =>
          have ⟨flds, hf⟩ := HasType_trecord_is_record hta
          subst hf
          cases op <;> (cases bt2 <;> simp [binop_type] at hbinop)

end LeanMove.Typing.TypeSoundness
