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
# Type Soundness: Preservation

Each `step` of the small-step interpreter preserves `WellTypedState`.
Contains typing inversion lemmas, individual preservation case proofs,
and the main preservation dispatcher.
-/

namespace LeanMove.Typing.TypeSoundness

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Typing
open LeanMove.Semantics
open AssocMap
open Regex

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

/-- When siteEnv gets a `.basic` type inserted, any ref lookup at the new site contradicts,
    so existing siteEnv_refs_in_pathEnv is preserved. -/
private lemma siteEnv_refs_in_pathEnv_insert_basic
    {m : Machine} {env : TypeEnv} {lenv : LabelEnv} {retType : MoveType} {rmap : RefMap}
    (hwt : WellTypedState m env lenv retType rmap) (s : Site) (bt : BasicMoveType) :
    ∀ s' bt' r bk,
      lookup (insert env.siteEnv s (.basic bt)) s' = some (.ref bt' r bk) →
      r ∈ env.pathEnv.refs := by
  intro s' bt' r bk hl
  by_cases heq : s' = s
  · subst heq; simp [lookup_insert_same] at hl
  · rw [lookup_insert_ne _ s s' _ heq] at hl
    exact hwt.siteEnv_refs_in_pathEnv s' bt' r bk hl

/-- When siteEnv gets a `.basic` type inserted and varEnv is unchanged,
    live_refs_unique is preserved (new site can't have a ref type). -/
private lemma live_refs_unique_insert_basic
    {m : Machine} {env : TypeEnv} {lenv : LabelEnv} {retType : MoveType} {rmap : RefMap}
    (hwt : WellTypedState m env lenv retType rmap) (s : Site) (bt : BasicMoveType) :
    ∀ r', (∀ x bt' bk ms s' bt'' bk',
             lookup env.varEnv x = some (.validVar, .ref bt' r' bk, ms) →
             lookup (insert env.siteEnv s (.basic bt)) s' = some (.ref bt'' r' bk') → False) ∧
           (∀ s1 s2 bt1 bt2 bk1 bk2, s1 ≠ s2 →
             lookup (insert env.siteEnv s (.basic bt)) s1 = some (.ref bt1 r' bk1) →
             lookup (insert env.siteEnv s (.basic bt)) s2 = some (.ref bt2 r' bk2) → False) ∧
           (∀ x y bt1 bt2 bk1 bk2 ms1 ms2, x ≠ y →
             lookup env.varEnv x = some (.validVar, .ref bt1 r' bk1, ms1) →
             lookup env.varEnv y = some (.validVar, .ref bt2 r' bk2, ms2) → False) := by
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
    siteEnv_refs_in_pathEnv := siteEnv_refs_in_pathEnv_insert_basic hwt s .u64
    live_refs_unique := live_refs_unique_insert_basic hwt s .u64
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
    siteEnv_refs_in_pathEnv := siteEnv_refs_in_pathEnv_insert_basic hwt s bt
    live_refs_unique := live_refs_unique_insert_basic hwt s bt
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

/-- When rmap is extended by a fresh ref t, var_consistent is preserved
    (since t can't appear in any existing varEnv entry by freshness). -/
private lemma var_consistent_extend_rmap_fresh
    {m : Machine} {env : TypeEnv} {lenv : LabelEnv} {retType : MoveType} {rmap : RefMap}
    (hwt : WellTypedState m env lenv retType rmap)
    (t : Aref) (loc_t : Loc) (path_t : List Field)
    (hfresh : freshRefInEnvBool t env) :
    let rmap' : RefMap := { map := fun r => if r = t then some (loc_t, path_t) else rmap.map r }
    ∀ y isv τ ms,
      lookup env.varEnv y = some (isv, τ, ms) →
      match isv with
      | .validVar =>
        ∃ loc v, lookup m.frame.varStore y = some (some loc) ∧
                 m.heap.read loc = some v ∧ ValueMatchesType v τ rmap'
      | .invalidVar =>
        lookup m.frame.varStore y = some none ∨
        ∃ loc, lookup m.frame.varStore y = some (some loc) := by
  intro rmap' y isv τ ms hvy
  have hold := hwt.var_consistent y isv τ ms hvy
  cases isv with
  | invalidVar => exact hold
  | validVar =>
    obtain ⟨l, v, hl, hr, hm⟩ := hold
    refine ⟨l, v, hl, hr, ?_⟩
    cases τ with
    | basic _ => exact trivial
    | ref bt r_y bk =>
      obtain ⟨loc_v, path_v, hv_eq, hrmap_r⟩ := hm
      by_cases hrt : r_y = t
      · exact absurd hrt.symm (freshRefInEnvBool_ne_varEnv_ref t env y .validVar bt r_y bk ms hfresh hvy)
      · refine ⟨loc_v, path_v, hv_eq, ?_⟩
        show (if r_y = t then some (loc_t, path_t) else rmap.map r_y) = some (loc_v, path_v)
        rw [if_neg hrt]; exact hrmap_r

/-- When rmap is extended by a fresh ref t, site_consistent is preserved
    for old siteEnv entries (whose refs aren't t). -/
private lemma site_consistent_old_entry_extend_rmap
    {m : Machine} {env : TypeEnv} {lenv : LabelEnv} {retType : MoveType} {rmap : RefMap}
    (hwt : WellTypedState m env lenv retType rmap)
    (t : Aref) (loc_t : Loc) (path_t : List Field)
    (hfresh : freshRefInEnvBool t env)
    (s' : Site) (τ' : MoveType) (hl : lookup env.siteEnv s' = some τ') :
    let rmap' : RefMap := { map := fun r => if r = t then some (loc_t, path_t) else rmap.map r }
    ∃ v', lookup m.frame.siteStore s' = some v' ∧ ValueMatchesType v' τ' rmap' := by
  intro rmap'
  obtain ⟨v', hv', hm⟩ := hwt.site_consistent s' τ' hl
  refine ⟨v', hv', ?_⟩
  cases τ' with
  | basic _ => exact trivial
  | ref bt r_s bk =>
    obtain ⟨loc_v, path_v, hv_eq', hrmap_r⟩ := hm
    by_cases hrt : r_s = t
    · exact absurd hrt.symm (freshRefInEnvBool_ne_siteEnv_ref t env s' bt r_s bk hfresh (hrt ▸ hl))
    · refine ⟨loc_v, path_v, hv_eq', ?_⟩
      show (if r_s = t then some (loc_t, path_t) else rmap.map r_s) = some (loc_v, path_v)
      rw [if_neg hrt]; exact hrmap_r

/-- When rmap is extended by a fresh ref t mapped to (loc_t, path_t),
    rmap_live is preserved if readRef at (loc_t, path_t) is live. -/
private lemma rmap_live_extend_fresh
    {m : Machine} {env : TypeEnv} {lenv : LabelEnv} {retType : MoveType} {rmap : RefMap}
    (hwt : WellTypedState m env lenv retType rmap)
    (t : Aref) (loc_t : Loc) (path_t : List Field)
    (hlive_t : m.heap.readRef loc_t path_t ≠ none) :
    let rmap' : RefMap := { map := fun r => if r = t then some (loc_t, path_t) else rmap.map r }
    ∀ r' loc path, rmap'.map r' = some (loc, path) → m.heap.readRef loc path ≠ none := by
  intro rmap' r' loc path hrmap_r'
  by_cases hrt : r' = t
  · subst hrt
    simp only [rmap', ite_true] at hrmap_r'
    have h := Option.some.inj hrmap_r'
    have ⟨h1, h2⟩ := Prod.mk.inj h
    subst h1; subst h2
    exact hlive_t
  · simp only [rmap', if_neg hrt] at hrmap_r'
    exact hwt.rmap_live r' loc path hrmap_r'

/-- When rmap is extended by a fresh non-root ref t, rmap_root_none is preserved. -/
private lemma rmap_root_none_extend_fresh
    {rmap : RefMap}
    (hwt_root : rmap.map .root = none)
    (t : Aref) (loc_t : Loc) (path_t : List Field)
    (ht_not_root : t ≠ .root) :
    let rmap' : RefMap := { map := fun r => if r = t then some (loc_t, path_t) else rmap.map r }
    rmap'.map .root = none := by
  intro rmap'
  simp only [rmap', if_neg (Ne.symm ht_not_root)]
  exact hwt_root

/-- When a fresh ref t is inserted into siteEnv at site s (with a type containing t),
    live_refs_unique is preserved. Uses freshness contradictions. -/
private lemma live_refs_unique_insert_fresh_ref
    {m : Machine} {env : TypeEnv} {lenv : LabelEnv} {retType : MoveType} {rmap : RefMap}
    (hwt : WellTypedState m env lenv retType rmap)
    (s : Site) (τ_site : MoveType) (t : Aref)
    (hfresh_pe : t ∉ env.pathEnv.refs)
    (hsite_has_ref_t : ∀ bt r bk, τ_site = .ref bt r bk → r = t) :
    ∀ r',
      (∀ x bt bk ms s' bt' bk',
        lookup env.varEnv x = some (.validVar, .ref bt r' bk, ms) →
        lookup (insert env.siteEnv s τ_site) s' = some (.ref bt' r' bk') → False) ∧
      (∀ s1 s2 bt1 bt2 bk1 bk2, s1 ≠ s2 →
        lookup (insert env.siteEnv s τ_site) s1 = some (.ref bt1 r' bk1) →
        lookup (insert env.siteEnv s τ_site) s2 = some (.ref bt2 r' bk2) → False) ∧
      (∀ x y bt1 bt2 bk1 bk2 ms1 ms2, x ≠ y →
        lookup env.varEnv x = some (.validVar, .ref bt1 r' bk1, ms1) →
        lookup env.varEnv y = some (.validVar, .ref bt2 r' bk2, ms2) → False) := by
  intro r'
  refine ⟨fun x' bt' bk' ms' s' bt'' bk'' hv hs => ?_,
          fun s1 s2 bt1 bt2 bk1 bk2 hne hs1 hs2 => ?_,
          fun x' y bt1 bt2 bk1 bk2 ms1 ms2 hne hx hy =>
            (hwt.live_refs_unique r').2.2 x' y bt1 bt2 bk1 bk2 ms1 ms2 hne hx hy⟩
  · -- var-site: if s' = s, extract t from τ_site, contradiction via freshness
    by_cases heqs : s' = s
    · subst heqs; rw [lookup_insert_same] at hs
      have hr_eq := hsite_has_ref_t bt'' r' bk'' (Option.some.inj hs)
      rw [hr_eq] at hv
      exact absurd (hwt.varEnv_refs_in_pathEnv x' bt' t bk' ms' hv) hfresh_pe
    · rw [lookup_insert_ne _ s s' _ heqs] at hs
      exact (hwt.live_refs_unique r').1 x' bt' bk' ms' s' bt'' bk'' hv hs
  · -- site-site
    by_cases heq1 : s1 = s
    · rw [heq1, lookup_insert_same] at hs1
      have hr_eq := hsite_has_ref_t bt1 r' bk1 (Option.some.inj hs1)
      have hne2 : s2 ≠ s := by rw [← heq1]; exact hne.symm
      rw [lookup_insert_ne _ s s2 _ hne2] at hs2
      rw [hr_eq] at hs2
      exact absurd (hwt.siteEnv_refs_in_pathEnv s2 bt2 t bk2 hs2) hfresh_pe
    · by_cases heq2 : s2 = s
      · rw [heq2, lookup_insert_same] at hs2
        have hr_eq := hsite_has_ref_t bt2 r' bk2 (Option.some.inj hs2)
        rw [lookup_insert_ne _ s s1 _ heq1] at hs1
        rw [hr_eq] at hs1
        exact absurd (hwt.siteEnv_refs_in_pathEnv s1 bt1 t bk1 hs1) hfresh_pe
      · rw [lookup_insert_ne _ s s1 _ heq1] at hs1
        rw [lookup_insert_ne _ s s2 _ heq2] at hs2
        exact (hwt.live_refs_unique r').2.1 s1 s2 bt1 bt2 bk1 bk2 hne hs1 hs2

/-- A ref that is fresh in the pathEnv cannot be .root, because .root ∈ pathEnv.refs
    by well-formedness. Used by copy_ref, borrowImm, and borrow cases. -/
private lemma freshRef_not_root
    {env : TypeEnv}
    (hpe_wf : env.pathEnv.WellFormed)
    (t : Aref)
    (hfresh : freshRefBool t env.pathEnv) :
    t ≠ Aref.root := by
  intro hcontra; subst hcontra
  have := (freshRef_iff_freshRefBool Aref.root env.pathEnv).mpr hfresh
  unfold freshRef at this
  exact this hpe_wf.root_in_refs

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
  have ht_not_root : t ≠ Aref.root := freshRef_not_root hwt.env_wf.pathEnv_wf t hfresh_t_pathEnv
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
    var_consistent := var_consistent_extend_rmap_fresh hwt t loc' path hfresh_t
    site_consistent := by
      intro s'' τ' hl
      by_cases heq : s'' = s
      · subst heq
        rw [lookup_insert_same] at hl; injection hl with hl; subst hl
        refine ⟨val, lookup_insert_same _ _ _, loc', path, hval_eq, ?_⟩
        show (if t = t then some (loc', path) else rmap.map t) = some (loc', path)
        rw [if_pos rfl]
      · rw [lookup_insert_ne _ s s'' _ heq] at hl
        have ⟨v', hv', hm⟩ := site_consistent_old_entry_extend_rmap hwt t loc' path hfresh_t s'' τ' hl
        exact ⟨v', by rw [lookup_insert_ne _ s s'' _ heq]; exact hv', hm⟩
    rmap_live := rmap_live_extend_fresh hwt t loc' path
        (hwt.rmap_live s_orig loc' path hrmap_s_orig)
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
    live_refs_unique :=
      have ht_fresh_pe := (freshRef_iff_freshRefBool t env.pathEnv).mpr hfresh_t_pathEnv
      live_refs_unique_insert_fresh_ref hwt s (.ref τ_ref t isBor) t ht_fresh_pe
        (fun _ _ _ h => by simp only [MoveType.ref.injEq] at h; exact h.2.1.symm)
    blocks_typed := hwt.blocks_typed
    lenv_empty_siteEnv := hwt.lenv_empty_siteEnv
    funEnv_typed := hwt.funEnv_typed
    heap_loc_bound := hwt.heap_loc_bound
    rmap_root_none := rmap_root_none_extend_fresh hwt.rmap_root_none t loc' path ht_not_root
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
  have hr_not_root : r ≠ Aref.root := freshRef_not_root hwt.env_wf.pathEnv_wf r hfresh_pathEnv
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
    var_consistent := var_consistent_extend_rmap_fresh hwt r loc [] hfresh
    site_consistent := by
      intro s'' τ' hl
      by_cases heq : s'' = s
      · subst heq
        rw [lookup_insert_same] at hl; injection hl with hl; subst hl
        refine ⟨Value.ref loc [], lookup_insert_same _ _ _, loc, [], rfl, ?_⟩
        show (if r = r then some (loc, []) else rmap.map r) = some (loc, [])
        rw [if_pos rfl]
      · rw [lookup_insert_ne _ s s'' _ heq] at hl
        have ⟨v', hv', hm⟩ := site_consistent_old_entry_extend_rmap hwt r loc [] hfresh s'' τ' hl
        exact ⟨v', by rw [lookup_insert_ne _ s s'' _ heq]; exact hv', hm⟩
    rmap_live := rmap_live_extend_fresh hwt r loc [] hreadref
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
    live_refs_unique := live_refs_unique_insert_fresh_ref hwt s (.ref τ r .siteBorrowImm) r
      hr_fresh_pe (fun _ r' _ h => by simp only [MoveType.ref.injEq] at h; exact h.2.1.symm)
    blocks_typed := hwt.blocks_typed
    lenv_empty_siteEnv := hwt.lenv_empty_siteEnv
    funEnv_typed := hwt.funEnv_typed
    heap_loc_bound := hwt.heap_loc_bound
    rmap_root_none := rmap_root_none_extend_fresh hwt.rmap_root_none r loc [] hr_not_root
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

/-- After delete_ref_node, no_paths_to_root is preserved. -/
private lemma no_paths_to_root_delete_ref_node'
    {m : Machine} {env : TypeEnv} {lenv : LabelEnv} {retType : MoveType} {rmap : RefMap}
    (hwt : WellTypedState m env lenv retType rmap)
    (r : Aref) (hr_not_root : r ≠ .root) :
    ∀ u p, interpret_regex ((delete_ref_node env.pathEnv r).paths (u, .root)) p →
      u = .root ∧ p = [] := by
  intro u p hp
  simp only [delete_ref_node] at hp
  by_cases hu : u = r
  · subst hu; simp only [true_or, ↓reduceIte, interpret_regex] at hp
  · by_cases hr' : Aref.root = r
    · exact absurd hr'.symm hr_not_root
    · simp only [hu, hr', or_false, ↓reduceIte] at hp
      exact hwt.no_paths_to_root u p hp

/-- After delete_ref_node, root_path_coherence is preserved. -/
private lemma root_path_coherence_delete_ref_node'
    {m : Machine} {env : TypeEnv} {lenv : LabelEnv} {retType : MoveType} {rmap : RefMap}
    (hwt : WellTypedState m env lenv retType rmap)
    (r : Aref) (hr_not_root : r ≠ .root) :
    ∀ v y rest,
      v ∈ (delete_ref_node env.pathEnv r).refs →
      interpret_regex ((delete_ref_node env.pathEnv r).paths (.root, v)) (.root_to_var y :: rest) →
      ∀ loc_v path_v, rmap.map v = some (loc_v, path_v) →
      ∀ loc_y, lookup m.frame.varStore y = some (some loc_y) →
      loc_v = loc_y → path_v = fieldPathOf rest := by
  intro v y rest hv_mem hp loc_v path_v hrmap loc_y hloc heq
  simp only [delete_ref_node_refs, List.mem_filter, decide_eq_true_eq] at hv_mem
  obtain ⟨hv_in, hv_ne⟩ := hv_mem
  simp only [delete_ref_node] at hp
  have hroot_ne : Aref.root ≠ r := Ne.symm hr_not_root
  simp only [hroot_ne, hv_ne, or_false, ↓reduceIte] at hp
  exact hwt.root_path_coherence v y rest hv_in hp loc_v path_v hrmap loc_y hloc heq

/-- After deleting a site, site_consistent is preserved for remaining sites. -/
private lemma site_consistent_delete_site
    {m : Machine} {env : TypeEnv} {lenv : LabelEnv} {retType : MoveType} {rmap : RefMap}
    (hwt : WellTypedState m env lenv retType rmap)
    (site : Site) :
    ∀ s' τ',
      lookup (delete env.siteEnv site) s' = some τ' →
      ∃ v', lookup m.frame.siteStore s' = some v' ∧ ValueMatchesType v' τ' rmap := by
  intro s' τ' hl
  have hne : s' ≠ site := by
    intro heq; subst heq; rw [lookup_delete_same] at hl; simp at hl
  rw [lookup_delete_ne env.siteEnv site s' hne] at hl
  exact hwt.site_consistent s' τ' hl

/-- After delete_ref_node r, varEnv refs remain in the filtered pathEnv.refs.
    Uses live_refs_unique to show any varEnv ref r' ≠ r. -/
private lemma varEnv_refs_in_pathEnv_delete_ref_node
    {m : Machine} {env : TypeEnv} {lenv : LabelEnv} {retType : MoveType} {rmap : RefMap}
    (hwt : WellTypedState m env lenv retType rmap)
    (r : Aref) (site : Site) (τ : BasicMoveType) (isBor : BorrowingKind)
    (hsite : lookup env.siteEnv site = some (.ref τ r isBor)) :
    ∀ x bt r' bk ms,
      lookup env.varEnv x = some (.validVar, .ref bt r' bk, ms) →
      r' ∈ (delete_ref_node env.pathEnv r).refs := by
  intro x' bt r' bk ms hvar'
  have hr'_in := hwt.varEnv_refs_in_pathEnv x' bt r' bk ms hvar'
  have hr'_ne : r' ≠ r := by
    intro heq; rw [heq] at hvar'
    exact (hwt.live_refs_unique r).1 x' bt bk ms site τ isBor hvar' hsite
  simp only [delete_ref_node_refs, List.mem_filter, decide_eq_true_eq]
  exact ⟨hr'_in, hr'_ne⟩

/-- After deleting a site and applying delete_ref_node, siteEnv refs remain
    in the filtered pathEnv.refs. Uses live_refs_unique (site-site part). -/
private lemma siteEnv_refs_in_pathEnv_delete_ref_node
    {m : Machine} {env : TypeEnv} {lenv : LabelEnv} {retType : MoveType} {rmap : RefMap}
    (hwt : WellTypedState m env lenv retType rmap)
    (r : Aref) (site : Site) (τ : BasicMoveType) (isBor : BorrowingKind)
    (hsite : lookup env.siteEnv site = some (.ref τ r isBor)) :
    ∀ s' bt r' bk,
      lookup (delete env.siteEnv site) s' = some (.ref bt r' bk) →
      r' ∈ (delete_ref_node env.pathEnv r).refs := by
  intro s' bt r' bk hl
  have hne : s' ≠ site := by
    intro h; subst h; rw [lookup_delete_same] at hl; simp at hl
  rw [lookup_delete_ne _ site s' hne] at hl
  have hr'_in := hwt.siteEnv_refs_in_pathEnv s' bt r' bk hl
  have hr'_ne : r' ≠ r := by
    intro heq; rw [heq] at hl
    exact (hwt.live_refs_unique r).2.1 site s' τ bt isBor bk (Ne.symm hne) hsite hl
  simp only [delete_ref_node_refs, List.mem_filter, decide_eq_true_eq]
  exact ⟨hr'_in, hr'_ne⟩

/-- After deleting a site, live_refs_unique is preserved (since varEnv is unchanged
    and siteEnv only lost an entry). -/
private lemma live_refs_unique_delete_site
    {m : Machine} {env : TypeEnv} {lenv : LabelEnv} {retType : MoveType} {rmap : RefMap}
    (hwt : WellTypedState m env lenv retType rmap)
    (site : Site) :
    ∀ r',
      (∀ x bt bk ms s' bt' bk',
        lookup env.varEnv x = some (.validVar, .ref bt r' bk, ms) →
        lookup (delete env.siteEnv site) s' = some (.ref bt' r' bk') → False) ∧
      (∀ s1 s2 bt1 bt2 bk1 bk2, s1 ≠ s2 →
        lookup (delete env.siteEnv site) s1 = some (.ref bt1 r' bk1) →
        lookup (delete env.siteEnv site) s2 = some (.ref bt2 r' bk2) → False) ∧
      (∀ x y bt1 bt2 bk1 bk2 ms1 ms2, x ≠ y →
        lookup env.varEnv x = some (.validVar, .ref bt1 r' bk1, ms1) →
        lookup env.varEnv y = some (.validVar, .ref bt2 r' bk2, ms2) → False) := by
  intro r'
  refine ⟨fun x' bt bk ms' s' bt' bk' hvar' hs' => ?_,
          fun s1 s2 bt1 bt2 bk1 bk2 hne hs1 hs2 => ?_,
          fun x1 x2 bt1 bt2 bk1 bk2 ms1 ms2 hne hx1 hx2 =>
            (hwt.live_refs_unique r').2.2 x1 x2 bt1 bt2 bk1 bk2 ms1 ms2 hne hx1 hx2⟩
  · have hne : s' ≠ site := by
      intro h; subst h; rw [lookup_delete_same] at hs'; simp at hs'
    rw [lookup_delete_ne _ site s' hne] at hs'
    exact (hwt.live_refs_unique r').1 x' bt bk ms' s' bt' bk' hvar' hs'
  · have hne1 : s1 ≠ site := by
      intro h; subst h; rw [lookup_delete_same] at hs1; simp at hs1
    have hne2 : s2 ≠ site := by
      intro h; subst h; rw [lookup_delete_same] at hs2; simp at hs2
    rw [lookup_delete_ne _ site s1 hne1] at hs1
    rw [lookup_delete_ne _ site s2 hne2] at hs2
    exact (hwt.live_refs_unique r').2.1 s1 s2 bt1 bt2 bk1 bk2 hne hs1 hs2

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
      varEnv_refs_in_pathEnv :=
        varEnv_refs_in_pathEnv_delete_ref_node hwt r src τ isBor hlookup
      siteEnv_refs_in_pathEnv := by
        intro s' bt r' bk hl
        by_cases heqs : s' = s
        · subst heqs; rw [lookup_insert_same] at hl; simp at hl
        · rw [lookup_insert_ne _ s s' _ heqs] at hl
          exact siteEnv_refs_in_pathEnv_delete_ref_node hwt r src τ isBor hlookup s' bt r' bk hl
      live_refs_unique := by
        intro r'
        refine ⟨fun x' bt bk ms' s' bt' bk' hvar' hs' => ?_,
                fun s1 s2 bt1 bt2 bk1 bk2 hne hs1 hs2 => ?_,
                fun x1 x2 bt1 bt2 bk1 bk2 ms1 ms2 hne hx1 hx2 =>
                  (hwt.live_refs_unique r').2.2 x1 x2 bt1 bt2 bk1 bk2 ms1 ms2 hne hx1 hx2⟩
        · -- var-site: peel off insert, then use delete_site lemma
          by_cases heqs : s' = s
          · subst heqs; rw [lookup_insert_same] at hs'; simp at hs'
          · rw [lookup_insert_ne _ s s' _ heqs] at hs'
            exact (live_refs_unique_delete_site hwt src r').1 x' bt bk ms' s' bt' bk' hvar' hs'
        · -- site-site: peel off insert, then use delete_site lemma
          by_cases heq1 : s1 = s
          · subst heq1; rw [lookup_insert_same] at hs1; simp at hs1
          · by_cases heq2 : s2 = s
            · subst heq2; rw [lookup_insert_same] at hs2; simp at hs2
            · rw [lookup_insert_ne _ s s1 _ heq1] at hs1
              rw [lookup_insert_ne _ s s2 _ heq2] at hs2
              exact (live_refs_unique_delete_site hwt src r').2.1 s1 s2 bt1 bt2 bk1 bk2 hne hs1 hs2
      blocks_typed := hwt.blocks_typed
      lenv_empty_siteEnv := hwt.lenv_empty_siteEnv
      funEnv_typed := hwt.funEnv_typed
      heap_loc_bound := hwt.heap_loc_bound
      rmap_root_none := hwt.rmap_root_none
      no_paths_to_root := no_paths_to_root_delete_ref_node' hwt r hr_not_root
      root_path_coherence := root_path_coherence_delete_ref_node' hwt r hr_not_root
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
  refine ⟨{env with siteEnv := delete env.siteEnv site,
                     pathEnv := delete_ref_node env.pathEnv r},
          lenv, retType, rmap, ?_, hss⟩
  exact {
    env_wf := ⟨delete_ref_node_wellformed env.pathEnv r hwt.env_wf.pathEnv_wf hr_not_root,
               SiteEnv.delete_refs_not_root env.siteEnv site hwt.env_wf.siteEnv_wf,
               hwt.env_wf.varEnv_wf⟩
    stmt_typed := hcont
    var_consistent := hwt.var_consistent
    site_consistent := site_consistent_delete_site hwt site
    rmap_live := hwt.rmap_live
    rmap_paths := rmap_paths_delete_ref_node env m rmap r hwt.rmap_paths
    varEnv_refs_in_pathEnv :=
      varEnv_refs_in_pathEnv_delete_ref_node hwt r site τ isBor hlookup
    siteEnv_refs_in_pathEnv :=
      siteEnv_refs_in_pathEnv_delete_ref_node hwt r site τ isBor hlookup
    live_refs_unique := live_refs_unique_delete_site hwt site
    blocks_typed := hwt.blocks_typed
    lenv_empty_siteEnv := hwt.lenv_empty_siteEnv
    funEnv_typed := hwt.funEnv_typed
    heap_loc_bound := hwt.heap_loc_bound
    rmap_root_none := hwt.rmap_root_none
    no_paths_to_root := no_paths_to_root_delete_ref_node' hwt r hr_not_root
    root_path_coherence := root_path_coherence_delete_ref_node' hwt r hr_not_root
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


end LeanMove.Typing.TypeSoundness
