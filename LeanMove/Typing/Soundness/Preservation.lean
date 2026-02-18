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
import LeanMove.Typing.Soundness.Weakening

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
      (∀ f a, (f, a) ∈ fieldSites →
        ∃ bt, lookup env.siteEnv a = some (.basic bt) ∧ lookup fentries f = some bt) ∧
      (∀ f, lookup fentries f ≠ none → ∃ a, (f, a) ∈ fieldSites) ∧
      typecheck_stmt lenv
        {env with siteEnv := insert (deleteAll env.siteEnv (fieldSites.map Prod.snd)) b
                                (.basic (.trecord fentries))}
        cont retType :=
  match h with
  | .let_bind_pack _ _ _ _ _ fentries _ _ _ hfields hcomplete _ hcont =>
    ⟨fentries, hfields, hcomplete, hcont⟩

private theorem inv_borrowField
    (h : typecheck_stmt lenv env (.letBind af (.borrowField src bt field) cont) retType) :
    ∃ bt' isBor fentries s rf,
      lookup env.siteEnv src = some (.ref bt s isBor) ∧
      bt = .trecord fentries ∧
      lookup fentries field = some bt' ∧
      freshRefInEnv rf env ∧
      (∀ v, rf ≠ .varRef v) ∧
      typecheck_stmt lenv
        {env with siteEnv := insert (delete env.siteEnv src) af (.ref bt' rf isBor)
                  pathEnv := update_with_extension rf s [.field field] env.pathEnv}
        cont retType :=
  match h with
  | .let_bind_borrowField _ _ _ _ _ _ bt' isBor fentries s rf _ _ hlookup hbt hf _ hfresh hnv hcont =>
    ⟨bt', isBor, fentries, s, rf, hlookup, hbt, hf, hfresh, hnv, hcont⟩

private theorem inv_borrowMutField
    (h : typecheck_stmt lenv env (.letBind af (.borrowMutField src bt field) cont) retType) :
    ∃ btf fentries s rf,
      lookup env.siteEnv src = some (.ref bt s .siteBorrowMut) ∧
      bt = .trecord fentries ∧
      lookup fentries field = some btf ∧
      freshRefInEnv rf env ∧
      (∀ v, rf ≠ .varRef v) ∧
      typecheck_stmt lenv
        {env with siteEnv := insert (delete env.siteEnv src) af (.ref btf rf .siteBorrowMut)
                  pathEnv := update_with_extension rf s [.field field] env.pathEnv}
        cont retType :=
  match h with
  | .let_bind_borrowMutField _ _ _ _ _ _ btf fentries s rf _ _ hlookup hbt hf _ hfresh hnv hcont =>
    ⟨btf, fentries, s, rf, hlookup, hbt, hf, hfresh, hnv, hcont⟩

private theorem inv_writeRef
    (h : typecheck_stmt lenv env (.writeRef dst val cont) retType) :
    ∃ τ r,
      lookup env.siteEnv dst = some (.ref τ r .siteBorrowMut) ∧
      lookup env.siteEnv val = some (.basic τ) ∧
      check_outbound env.pathEnv r (fun re => only_matches_empty (simplify re)) ∧
      typecheck_stmt lenv
        {env with siteEnv := delete (delete env.siteEnv val) dst
                  pathEnv := garbage_collect env.pathEnv r}
        cont retType :=
  match h with
  | .write_ref _ _ _ _ τ r _ _ hdst hval hcheck hcont => ⟨τ, r, hdst, hval, hcheck, hcont⟩

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
    ∃ params rets outRefs env',
      lookup env.funEnv fname = some ⟨params, rets⟩ ∧
      populate_call_outputs env results rets outRefs = some env' ∧
      typecheck_stmt lenv (call_connect_inputs_outputs env' results args) cont retType :=
  match h with
  | .call _ _ _ _ _ params rets outRefs env' _ _ hfun _ _ _ _ _ hpop _ hcont =>
    ⟨params, rets, outRefs, env', hfun, hpop, hcont⟩

private theorem inv_unpack
    (h : typecheck_stmt lenv env (.unpack fields src cont) retType) :
    ∃ fentries,
      lookup env.siteEnv src = some (.basic (.trecord fentries)) ∧
      (∀ f a, (f, a) ∈ fields → AssocMap.notIn env.siteEnv a) ∧
      (∀ a₁ a₂, (∃ f₁ f₂, (f₁, a₁) ∈ fields ∧ (f₂, a₂) ∈ fields ∧ f₁ ≠ f₂) → a₁ ≠ a₂) ∧
      (∀ f a, (f, a) ∈ fields → ∃ bt, lookup fentries f = some bt) ∧
      typecheck_stmt lenv
        {env with siteEnv := addFieldSites fentries (delete env.siteEnv src) fields}
        cont retType :=
  match h with
  | .unpack _ _ _ _ fentries _ _ hlookup hfresh hdistinct hfields hcont =>
    ⟨fentries, hlookup, hfresh, hdistinct, hfields, hcont⟩

private theorem inv_assign
    (h : typecheck_stmt lenv env (.assign x a cont) retType) :
    (∃ ax τ ms r,
      lookup env.varEnv x = some (.validVar, .basic τ, ms) ∧
      lookup env.siteEnv a = some (.basic τ) ∧
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
  | .var_assign_valid _ _ _ _ ax τ ms r _ _ _ hlookup ha_type hnotin hfresh hnv hcont =>
    .inl ⟨ax, τ, ms, r, hlookup, ha_type, hnv, hfresh, hnotin, hcont⟩
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
        (.basic .u64) hwt.site_consistent (HasType.int n)
    rmap_live := hwt.rmap_live
    rmap_paths := hwt.rmap_paths
    varEnv_refs_in_pathEnv := hwt.varEnv_refs_in_pathEnv
    siteEnv_refs_in_pathEnv := siteEnv_refs_in_pathEnv_insert_basic hwt s .u64
    live_refs_unique := live_refs_unique_insert_basic hwt s .u64
    blocks_typed := hwt.blocks_typed
    lenv_empty_siteEnv := hwt.lenv_empty_siteEnv
    lenv_wf := hwt.lenv_wf
    lenv_var_tracked := hwt.lenv_var_tracked
    lenv_var_unique := hwt.lenv_var_unique
    lenv_funEnv_eq := hwt.lenv_funEnv_eq
    funEnv_typed := hwt.funEnv_typed
    heap_loc_bound := hwt.heap_loc_bound
    rmap_root_none := hwt.rmap_root_none
    no_paths_to_root := hwt.no_paths_to_root
    root_path_coherence := hwt.root_path_coherence
    paths_from_non_member_empty := hwt.paths_from_non_member_empty
    paths_to_non_member_empty := hwt.paths_to_non_member_empty
    self_loop_only_empty := hwt.self_loop_only_empty
    rmap_has_type := by
      intro r bt loc path hrmap hcond
      apply hwt.rmap_has_type r bt loc path hrmap
      rcases hcond with ⟨x, bk, ms, hvar⟩ | ⟨s', bk, hsite⟩
      · exact Or.inl ⟨x, bk, ms, hvar⟩
      · by_cases heq : s' = s
        · subst heq; simp [lookup_insert_same] at hsite
        · exact Or.inr ⟨s', bk, by rw [lookup_insert_ne _ s s' _ heq] at hsite; exact hsite⟩
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
  obtain ⟨loc, val, hloc, hread, hht_val⟩ := hwt.var_consistent x .validVar (.basic bt) ms hvar
  have hrv : readVar m x = some val := by unfold readVar; simp [hloc, hread]
  simp only [step, hstmt, hrv, ExecState.running.injEq] at hstep; subst hstep
  refine ⟨{env with siteEnv := insert env.siteEnv s (.basic bt)},
          lenv, retType, rmap, ?_, hss⟩
  exact {
    env_wf := TypeEnv.insert_siteEnv_wf env s (.basic bt) hwt.env_wf trivial
    stmt_typed := hcont
    var_consistent := hwt.var_consistent
    site_consistent := site_consistent_insert_basic m env rmap s val
        (.basic bt) hwt.site_consistent hht_val
    rmap_live := hwt.rmap_live
    rmap_paths := hwt.rmap_paths
    varEnv_refs_in_pathEnv := hwt.varEnv_refs_in_pathEnv
    siteEnv_refs_in_pathEnv := siteEnv_refs_in_pathEnv_insert_basic hwt s bt
    live_refs_unique := live_refs_unique_insert_basic hwt s bt
    blocks_typed := hwt.blocks_typed
    lenv_empty_siteEnv := hwt.lenv_empty_siteEnv
    lenv_wf := hwt.lenv_wf
    lenv_var_tracked := hwt.lenv_var_tracked
    lenv_var_unique := hwt.lenv_var_unique
    lenv_funEnv_eq := hwt.lenv_funEnv_eq
    funEnv_typed := hwt.funEnv_typed
    heap_loc_bound := hwt.heap_loc_bound
    rmap_root_none := hwt.rmap_root_none
    no_paths_to_root := hwt.no_paths_to_root
    root_path_coherence := hwt.root_path_coherence
    paths_from_non_member_empty := hwt.paths_from_non_member_empty
    paths_to_non_member_empty := hwt.paths_to_non_member_empty
    self_loop_only_empty := hwt.self_loop_only_empty
    rmap_has_type := by
      intro r bt' loc path hrmap hcond
      apply hwt.rmap_has_type r bt' loc path hrmap
      rcases hcond with ⟨x, bk, ms', hvar⟩ | ⟨s', bk, hsite⟩
      · exact Or.inl ⟨x, bk, ms', hvar⟩
      · by_cases heq : s' = s
        · subst heq; simp [lookup_insert_same] at hsite
        · exact Or.inr ⟨s', bk, by rw [lookup_insert_ne _ s s' _ heq] at hsite; exact hsite⟩
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
    | basic _ => exact hm
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
  | basic _ => exact hm
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
  -- 5. Get s_orig ≠ root from well-formedness
  have hs_not_root : s_orig ≠ Aref.root :=
    hwt.env_wf.varEnv_wf x (.validVar, .ref τ_ref s_orig isBor, ms) hvar
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
        ht_not_root
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
    lenv_wf := hwt.lenv_wf
    lenv_var_tracked := hwt.lenv_var_tracked
    lenv_var_unique := hwt.lenv_var_unique
    lenv_funEnv_eq := hwt.lenv_funEnv_eq
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
    paths_from_non_member_empty := by
      unfold update_with_epsilon
      exact update_with_extension_paths_from_non_member t s_orig [] env.pathEnv
        hwt.paths_from_non_member_empty
        (Or.inl (hwt.varEnv_refs_in_pathEnv x τ_ref s_orig isBor ms hvar))
    paths_to_non_member_empty := by
      unfold update_with_epsilon
      exact update_with_extension_paths_to_non_member t s_orig [] env.pathEnv
        hwt.paths_to_non_member_empty
        (Or.inl (hwt.varEnv_refs_in_pathEnv x τ_ref s_orig isBor ms hvar))
    self_loop_only_empty := by
      intro u p hp
      unfold update_with_epsilon update_with_extension at hp
      by_cases hu : u = t
      · subst hu; simp only [↓reduceIte] at hp; exact hp
      · simp only [show ¬(u = t) from hu, and_false, ↓reduceIte] at hp
        exact hwt.self_loop_only_empty u p hp
    rmap_has_type := by
      intro r bt loc_r path_r hrmap_r hcond
      by_cases hrt : r = t
      · -- r = t: rmap'(t) = (loc', path), condition gives bt = τ_ref
        simp only [rmap', hrt, ite_true] at hrmap_r
        obtain ⟨h1, h2⟩ := Prod.mk.inj (Option.some.inj hrmap_r)
        -- h1 : loc' = loc_r, h2 : path = path_r
        rw [← h1, ← h2]
        -- From old state: x has .ref τ_ref s_orig isBor, rmap(s_orig) = (loc', path)
        apply hwt.rmap_has_type s_orig bt loc' path hrmap_s_orig
        -- Need to show s_orig has type bt in old env
        rcases hcond with ⟨x', bk, ms', hvar'⟩ | ⟨s', bk, hsite⟩
        · -- varEnv unchanged, r = t is fresh in pathEnv → contradiction
          rw [hrt] at hvar'
          exact absurd (hwt.varEnv_refs_in_pathEnv x' bt t bk ms' hvar')
            ((freshRef_iff_freshRefBool t env.pathEnv).mpr hfresh_t_pathEnv)
        · -- siteEnv: s' has .ref bt r bk, with r = t
          by_cases heqs : s' = s
          · subst heqs; rw [lookup_insert_same] at hsite
            simp only [Option.some.injEq, MoveType.ref.injEq] at hsite
            rw [← hsite.1]; exact Or.inl ⟨x, isBor, ms, hvar⟩
          · rw [lookup_insert_ne _ s s' _ heqs] at hsite
            rw [hrt] at hsite
            exact absurd (hwt.siteEnv_refs_in_pathEnv s' bt t bk hsite)
              ((freshRef_iff_freshRefBool t env.pathEnv).mpr hfresh_t_pathEnv)
      · -- r ≠ t: rmap'(r) = rmap(r), delegate to old
        simp only [rmap', if_neg hrt] at hrmap_r
        apply hwt.rmap_has_type r bt loc_r path_r hrmap_r
        rcases hcond with ⟨x', bk, ms', hvar'⟩ | ⟨s', bk, hsite⟩
        · exact Or.inl ⟨x', bk, ms', hvar'⟩
        · by_cases heqs : s' = s
          · subst heqs; rw [lookup_insert_same] at hsite
            simp only [Option.some.injEq, MoveType.ref.injEq] at hsite
            -- r = t from hsite, contradiction
            exact absurd hsite.2.1.symm hrt
          · rw [lookup_insert_ne _ s s' _ heqs] at hsite
            exact Or.inr ⟨s', bk, hsite⟩
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
  have hfresh : moveTypeRefNotRoot τ := hwt.env_wf.varEnv_wf x (.validVar, τ, ms) hvar
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
        | ref _ r _ => exact hfresh
      · exact VarEnv.update_refs_not_root env.varEnv x (.invalidVar, τ, ms)
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
    lenv_wf := hwt.lenv_wf
    lenv_var_tracked := hwt.lenv_var_tracked
    lenv_var_unique := hwt.lenv_var_unique
    lenv_funEnv_eq := hwt.lenv_funEnv_eq
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
    paths_from_non_member_empty := hwt.paths_from_non_member_empty
    paths_to_non_member_empty := hwt.paths_to_non_member_empty
    self_loop_only_empty := hwt.self_loop_only_empty
    rmap_has_type := by
      intro r bt loc path hrmap hcond
      apply hwt.rmap_has_type r bt loc path hrmap
      rcases hcond with ⟨y, bk, ms', hvy⟩ | ⟨s', bk, hsite⟩
      · -- varEnv: y has validVar in updated env
        have hvy' : lookup (insert env.varEnv x (.invalidVar, τ, ms)) y =
            some (.validVar, .ref bt r bk, ms') := hvy
        have hne : y ≠ x := by
          intro h; subst h; rw [lookup_insert_same] at hvy'; simp at hvy'
        rw [lookup_insert_ne _ x y _ hne] at hvy'
        exact Or.inl ⟨y, bk, ms', hvy'⟩
      · -- siteEnv: s' has ref in insert env.siteEnv s τ
        by_cases heq : s' = s
        · subst heq; rw [lookup_insert_same] at hsite
          -- τ = .ref bt r bk, which came from x in old varEnv
          cases τ with
          | basic _ => simp [Option.some.injEq] at hsite
          | ref bt' r' bk' =>
            simp only [Option.some.injEq, MoveType.ref.injEq] at hsite
            rw [← hsite.1, ← hsite.2.1]
            exact Or.inl ⟨x, bk', ms, hvar⟩
        · rw [lookup_insert_ne _ s s' _ heq] at hsite
          exact Or.inr ⟨s', bk, hsite⟩
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

/-- Unified preservation for borrowImm/borrowMut of a basic-typed variable.
    Both borrow kinds have identical runtime semantics (allocate ref to var's location)
    and identical proof structure — only the BorrowingKind in siteEnv differs.
    Parameters: inversion results (τ, r, hfresh, hnv, hcont) and
    var_consistent results (loc, val, hloc, hread) are pre-computed by the wrappers. -/
private theorem preservation_borrow (m : Machine) (env : TypeEnv) (lenv : LabelEnv)
    (retType : MoveType) (rmap : RefMap)
    (hwt : WellTypedState m env lenv retType rmap)
    (hss : StackSafe m.stack m.frame.returnInfo m.heap)
    (s : Site) (x : Var) (cont : Stmt) (bk : BorrowingKind)
    -- Inversion results
    (τ : BasicMoveType) (r : Aref)
    (hfresh : freshRefInEnvBool r env)
    (hnv : ∀ v, r ≠ .varRef v)
    (hcont : typecheck_stmt lenv
      {env with siteEnv := insert env.siteEnv s (.ref τ r bk),
                pathEnv := update_with_extension r .root [.root_to_var x]
                            (update_with_epsilon r r env.pathEnv)}
      cont retType)
    -- Var consistent results
    (loc : Loc) (val : Value)
    (hloc : lookup m.frame.varStore x = some (some loc))
    (hread : m.heap.read loc = some val)
    (hht : HasType val τ) :
    let m' : Machine := { m with frame := { m.frame with
                siteStore := insert m.frame.siteStore s (Value.ref loc []),
                stmt := cont } }
    ∃ env' lenv' retType' rmap',
      WellTypedState m' env' lenv' retType' rmap' ∧
      StackSafe m'.stack m'.frame.returnInfo m'.heap := by
  intro m'
  -- 1. Define the new rmap extending with r → (loc, [])
  let rmap' : RefMap := { map := fun r' => if r' = r then some (loc, []) else rmap.map r' }
  -- 2. Freshness facts
  have hfresh_pathEnv : freshRefBool r env.pathEnv :=
    freshRefInEnvBool_implies_freshRefBool r env hfresh
  have hr_not_root : r ≠ Aref.root := freshRef_not_root hwt.env_wf.pathEnv_wf r hfresh_pathEnv
  have hr_fresh_pe : r ∉ env.pathEnv.refs :=
    (freshRef_iff_freshRefBool r env.pathEnv).mpr hfresh_pathEnv
  -- 3. readRef loc [] is live (heap.read loc ≠ none)
  have hreadref : m.heap.readRef loc [] ≠ none := by
    unfold Heap.readRef; simp [hread, readPath]
  -- 4. Abbreviation for the new pathEnv
  let pe' := update_with_extension r .root [.root_to_var x]
               (update_with_epsilon r r env.pathEnv)
  -- 5. Show pe'.refs = r :: env.pathEnv.refs
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
  -- 6. Construct WellTypedState
  refine ⟨{env with siteEnv := insert env.siteEnv s (.ref τ r bk),
                     pathEnv := pe'},
          lenv, retType, rmap', ?_, hss⟩
  exact {
    env_wf := by
      have hpe_eps := update_with_epsilon_wellformed r r env.pathEnv hwt.env_wf.pathEnv_wf
        hr_not_root
      have hpe' := update_with_extension_wellformed r .root [.root_to_var x]
        (update_with_epsilon r r env.pathEnv) hpe_eps hr_not_root
      exact TypeEnv.insert_pathEnv_wf env s (.ref τ r bk) _ hwt.env_wf hpe' hr_not_root
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
    live_refs_unique := live_refs_unique_insert_fresh_ref hwt s (.ref τ r bk) r
      hr_fresh_pe (fun _ r' _ h => by simp only [MoveType.ref.injEq] at h; exact h.2.1.symm)
    blocks_typed := hwt.blocks_typed
    lenv_empty_siteEnv := hwt.lenv_empty_siteEnv
    lenv_wf := hwt.lenv_wf
    lenv_var_tracked := hwt.lenv_var_tracked
    lenv_var_unique := hwt.lenv_var_unique
    lenv_funEnv_eq := hwt.lenv_funEnv_eq
    funEnv_typed := hwt.funEnv_typed
    heap_loc_bound := hwt.heap_loc_bound
    rmap_root_none := rmap_root_none_extend_fresh hwt.rmap_root_none r loc [] hr_not_root
    no_paths_to_root := by
      have hroot_ne_r : ¬(Aref.root = r) := Ne.symm hr_not_root
      intro u p hp
      have hp : interpret_regex (pe'.paths (u, Aref.root)) p := hp
      by_cases hu : u = r
      · rw [hu] at hp
        unfold pe' update_with_extension at hp
        simp only [hroot_ne_r, and_false, ite_false, ite_true] at hp
        unfold update_with_epsilon update_with_extension at hp
        simp only [hroot_ne_r, and_false, ite_false] at hp
        simp only [der, List.foldl] at hp
        have hp' : interpret_regex (env.pathEnv.paths (Aref.root, Aref.root))
            (PathElement.root_to_var x :: p) := hp
        exact absurd (hwt.no_paths_to_root .root _ hp').2 (List.cons_ne_nil _ _)
      · unfold pe' update_with_extension at hp
        simp only [hu, hroot_ne_r, ite_false] at hp
        unfold update_with_epsilon update_with_extension at hp
        simp only [hu, hroot_ne_r, false_and, ite_false] at hp
        exact hwt.no_paths_to_root u p hp
    root_path_coherence := by
      have hroot_ne_r : ¬(Aref.root = r) := Ne.symm hr_not_root
      intro v' y rest hv_mem hp loc_v path_v hrmap loc_y hloc' heq
      rw [hrefs_eq] at hv_mem
      simp only [List.mem_cons] at hv_mem
      have hp : interpret_regex (pe'.paths (Aref.root, v')) (PathElement.root_to_var y :: rest) := hp
      rcases hv_mem with hv_eq | hv_in
      · rw [hv_eq] at hp hrmap
        unfold pe' update_with_extension at hp
        simp only [hroot_ne_r, false_and, ite_false, ite_true] at hp
        unfold update_with_epsilon update_with_extension at hp
        simp only [hroot_ne_r, false_and, ite_false] at hp
        simp only [extend, List.foldl, interpret_regex] at hp
        obtain ⟨s1, s2, heq', hinterp, hs2_eq⟩ := hp
        have ⟨_, hs1_nil⟩ := hwt.no_paths_to_root .root s1 hinterp
        subst hs1_nil; subst hs2_eq
        simp only [List.nil_append, List.cons.injEq] at heq'
        obtain ⟨_, hrest_nil⟩ := heq'
        subst hrest_nil
        simp only [rmap', ite_true] at hrmap
        obtain ⟨h1, h2⟩ := Prod.mk.inj (Option.some.inj hrmap)
        subst h1; subst h2
        rfl
      · have hv_ne : ¬(v' = r) := fun h => by subst h; exact absurd hv_in hr_fresh_pe
        unfold pe' update_with_extension at hp
        simp only [hroot_ne_r, hv_ne, false_and, ite_false] at hp
        unfold update_with_epsilon update_with_extension at hp
        simp only [hroot_ne_r, hv_ne, false_and, ite_false] at hp
        simp only [rmap', if_neg hv_ne] at hrmap
        exact hwt.root_path_coherence v' y rest hv_in hp loc_v path_v hrmap loc_y hloc' heq
    paths_from_non_member_empty := by
      have h_root_in_mid : Aref.root ∈ (update_with_epsilon r r env.pathEnv).refs :=
        hpe_mid_refs ▸ List.mem_cons_of_mem _ hwt.env_wf.pathEnv_wf.root_in_refs
      exact update_with_extension_paths_from_non_member r .root [.root_to_var x] _
        (by unfold update_with_epsilon
            exact update_with_extension_paths_from_non_member r r [] env.pathEnv
              hwt.paths_from_non_member_empty (Or.inr rfl))
        (Or.inl h_root_in_mid)
    paths_to_non_member_empty := by
      have h_root_in_mid : Aref.root ∈ (update_with_epsilon r r env.pathEnv).refs :=
        hpe_mid_refs ▸ List.mem_cons_of_mem _ hwt.env_wf.pathEnv_wf.root_in_refs
      exact update_with_extension_paths_to_non_member r .root [.root_to_var x] _
        (by unfold update_with_epsilon
            exact update_with_extension_paths_to_non_member r r [] env.pathEnv
              hwt.paths_to_non_member_empty (Or.inr rfl))
        (Or.inl h_root_in_mid)
    self_loop_only_empty := by
      intro u p hp
      unfold pe' update_with_extension at hp
      by_cases hu : u = r
      · subst hu; simp only [↓reduceIte] at hp; exact hp
      · simp only [show ¬(u = r) from hu, and_false, ↓reduceIte] at hp
        unfold update_with_epsilon update_with_extension at hp
        simp only [show ¬(u = r) from hu, and_false, ↓reduceIte] at hp
        exact hwt.self_loop_only_empty u p hp
    rmap_has_type := by
      intro r' bt loc_r path_r hrmap hcond
      by_cases hrt : r' = r
      · -- r' = r: rmap'(r) = some (loc, []), need HasType val τ
        subst hrt
        simp only [rmap', ite_true] at hrmap
        obtain ⟨h1, h2⟩ := Prod.mk.inj (Option.some.inj hrmap)
        subst h1; subst h2
        -- Extract bt = τ from hcond: r' is fresh, so varEnv case impossible,
        -- siteEnv case gives the unique entry (s, .ref τ r' bk)
        have hbt_eq : bt = τ := by
          rcases hcond with ⟨x', bk', ms', hvar'⟩ | ⟨s', bk', hsite'⟩
          · exact absurd (hwt.varEnv_refs_in_pathEnv x' bt r' bk' ms' hvar') hr_fresh_pe
          · by_cases heqs : s' = s
            · subst heqs; rw [lookup_insert_same] at hsite'
              simp only [Option.some.injEq, MoveType.ref.injEq] at hsite'
              exact hsite'.1.symm
            · rw [lookup_insert_ne _ s s' _ heqs] at hsite'
              exact absurd (hwt.siteEnv_refs_in_pathEnv s' bt r' bk' hsite') hr_fresh_pe
        subst hbt_eq
        refine ⟨val, ?_, hht⟩
        show m.heap.readRef loc [] = some val
        unfold Heap.readRef; simp [hread, readPath]
      · -- r' ≠ r: rmap'(r') = rmap(r'), delegate to old
        simp only [rmap', if_neg hrt] at hrmap
        apply hwt.rmap_has_type r' bt loc_r path_r hrmap
        rcases hcond with ⟨x', bk', ms', hvar'⟩ | ⟨s', bk', hsite'⟩
        · exact Or.inl ⟨x', bk', ms', hvar'⟩
        · by_cases heqs : s' = s
          · subst heqs; rw [lookup_insert_same] at hsite'
            simp only [Option.some.injEq, MoveType.ref.injEq] at hsite'
            exact absurd hsite'.2.1.symm hrt
          · rw [lookup_insert_ne _ s s' _ heqs] at hsite'
            exact Or.inr ⟨s', bk', hsite'⟩
  }

/-- Preservation for borrowImm: thin wrapper around preservation_borrow. -/
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
  obtain ⟨τ, ms, r, hlookup, hfresh, hnv, hcont⟩ :=
    inv_borrowImm (by rw [← hstmt]; exact hwt.stmt_typed)
  obtain ⟨loc, val, hloc, hread, hht_val⟩ :=
    hwt.var_consistent x .validVar (.basic τ) ms hlookup
  have hgl : getVarLoc m x = some loc := by unfold getVarLoc; simp [hloc]
  simp only [step, hstmt, hgl, ExecState.running.injEq] at hstep; subst hstep
  exact preservation_borrow m env lenv retType rmap hwt hss s x cont .siteBorrowImm
    τ r hfresh hnv hcont loc val hloc hread hht_val

/-- Preservation for borrowMut: thin wrapper around preservation_borrow. -/
private theorem preservation_borrowMut (m m' : Machine) (env : TypeEnv) (lenv : LabelEnv)
    (retType : MoveType) (rmap : RefMap)
    (hwt : WellTypedState m env lenv retType rmap)
    (hss : StackSafe m.stack m.frame.returnInfo m.heap)
    (s : Site) (x : Var) (cont : Stmt)
    (hstmt : m.frame.stmt = .letBind s (.usage (.borrowMut x)) cont)
    (hstep : step (.running m) = .running m') :
    ∃ env' lenv' retType' rmap',
      WellTypedState m' env' lenv' retType' rmap' ∧
      StackSafe m'.stack m'.frame.returnInfo m'.heap := by
  obtain ⟨τ, ms, r, hlookup, hfresh, hnv, hcont⟩ :=
    inv_borrowMut (by rw [← hstmt]; exact hwt.stmt_typed)
  obtain ⟨loc, val, hloc, hread, hht_val⟩ :=
    hwt.var_consistent x .validVar (.basic τ) ms hlookup
  have hgl : getVarLoc m x = some loc := by unfold getVarLoc; simp [hloc]
  simp only [step, hstmt, hgl, ExecState.running.injEq] at hstep; subst hstep
  exact preservation_borrow m env lenv retType rmap hwt hss s x cont .siteBorrowMut
    τ r hfresh hnv hcont loc val hloc hread hht_val

/-- fieldPathOf distributes over append. -/
private theorem fieldPathOf_append (l₁ l₂ : List PathElement) :
    fieldPathOf (l₁ ++ l₂) = fieldPathOf l₁ ++ fieldPathOf l₂ := by
  induction l₁ with
  | nil => simp [fieldPathOf]
  | cons hd tl ih =>
    cases hd with
    | field f => simp [fieldPathOf, ih]
    | root_to_var y => simp [fieldPathOf, ih]

/-- Unified preservation for borrowField/borrowMutField.
    Both have identical runtime semantics (extend ref with field) and identical
    proof structure — only the BorrowingKind differs.
    The source site is deleted and a new site is created with a fresh ref rf
    pointing to (loc, path ++ [field]) where (loc, path) is the source ref's rmap entry.
    rmap_live for the new ref rf requires heap.readRef loc (path ++ [field]) ≠ none,
    which follows from the rmap_has_type invariant on the parent ref s. -/
private theorem preservation_borrowField (m : Machine) (env : TypeEnv) (lenv : LabelEnv)
    (retType : MoveType) (rmap : RefMap)
    (hwt : WellTypedState m env lenv retType rmap)
    (hss : StackSafe m.stack m.frame.returnInfo m.heap)
    (af src : Site) (field : Field) (cont : Stmt) (bk : BorrowingKind)
    -- Inversion results
    (bt' : BasicMoveType) (fentries : AssocMap Field BasicMoveType) (s rf : Aref)
    (hlookup_src : lookup env.siteEnv src = some (.ref (.trecord fentries) s bk))
    (hfield : lookup fentries field = some bt')
    (hfresh : freshRefInEnv rf env)
    (hnv : ∀ v, rf ≠ .varRef v)
    (hcont : typecheck_stmt lenv
      {env with siteEnv := insert (delete env.siteEnv src) af (.ref bt' rf bk),
                pathEnv := update_with_extension rf s [.field field] env.pathEnv}
      cont retType)
    -- Site consistent results
    (loc : Loc) (path : List Field)
    (hrmap_s : rmap.map s = some (loc, path)) :
    let m' : Machine := { m with frame := { m.frame with
                siteStore := insert m.frame.siteStore af (Value.ref loc (path ++ [field])),
                stmt := cont } }
    ∃ env' lenv' retType' rmap',
      WellTypedState m' env' lenv' retType' rmap' ∧
      StackSafe m'.stack m'.frame.returnInfo m'.heap := by
  intro m'
  -- 1. Freshness facts
  have hfresh_bool : freshRefInEnvBool rf env = true :=
    (freshRefInEnv_iff_freshRefInEnvBool rf env).mp hfresh
  have hfresh_pathEnv : freshRefBool rf env.pathEnv :=
    freshRefInEnvBool_implies_freshRefBool rf env hfresh_bool
  have hrf_not_root : rf ≠ Aref.root := freshRef_not_root hwt.env_wf.pathEnv_wf rf hfresh_pathEnv
  have hrf_fresh_pe : rf ∉ env.pathEnv.refs :=
    (freshRef_iff_freshRefBool rf env.pathEnv).mpr hfresh_pathEnv
  have hs_not_root : s ≠ .root := hwt.env_wf.siteEnv_wf src (.ref (.trecord fentries) s bk) hlookup_src
  have hs_in_refs : s ∈ env.pathEnv.refs := hwt.siteEnv_refs_in_pathEnv src (.trecord fentries) s bk hlookup_src
  have hrf_ne_s : rf ≠ s := fun h => hrf_fresh_pe (h ▸ hs_in_refs)
  -- 2. Define the new rmap extending with rf → (loc, path ++ [field])
  let rmap' : RefMap := { map := fun r => if r = rf then some (loc, path ++ [field]) else rmap.map r }
  -- 3. Heap liveness for the new mapping
  have hlive_s : m.heap.readRef loc path ≠ none := hwt.rmap_live s loc path hrmap_s
  have hreadref_field : m.heap.readRef loc (path ++ [field]) ≠ none :=
    HasType.readRef_field_ne_none m.heap loc path field
      (hwt.rmap_has_type s (.trecord fentries) loc path hrmap_s (Or.inr ⟨src, bk, hlookup_src⟩))
      hfield
  -- 4. Abbreviation for the new pathEnv
  let pe' := update_with_extension rf s [.field field] env.pathEnv
  -- 5. Show pe'.refs = rf :: env.pathEnv.refs
  have hrefs_eq : pe'.refs = rf :: env.pathEnv.refs := by
    simp only [pe', update_with_extension]
    simp only [show ¬rf ∈ env.pathEnv.refs from hrf_fresh_pe, not_false_eq_true, ↓reduceIte]
  -- 6. Construct WellTypedState
  refine ⟨{env with siteEnv := insert (delete env.siteEnv src) af (.ref bt' rf bk),
                     pathEnv := pe'},
          lenv, retType, rmap', ?_, hss⟩
  exact {
    env_wf := TypeEnv.delete_insert_pathEnv_wf env src af (.ref bt' rf bk) pe' hwt.env_wf
      (update_with_extension_wellformed rf s [.field field] env.pathEnv hwt.env_wf.pathEnv_wf
        hrf_not_root) hrf_not_root
    stmt_typed := hcont
    var_consistent := var_consistent_extend_rmap_fresh hwt rf loc (path ++ [field]) hfresh_bool
    site_consistent := by
      intro s' τ' hl
      by_cases heq : s' = af
      · subst heq; rw [lookup_insert_same] at hl; injection hl with hl; subst hl
        refine ⟨Value.ref loc (path ++ [field]), lookup_insert_same _ _ _, loc, path ++ [field], rfl, ?_⟩
        show (if rf = rf then some (loc, path ++ [field]) else rmap.map rf) = some (loc, path ++ [field])
        rw [if_pos rfl]
      · rw [lookup_insert_ne _ af s' _ heq] at hl
        have hne_src : s' ≠ src := by
          intro h; subst h; rw [lookup_delete_same] at hl; simp at hl
        rw [lookup_delete_ne _ src s' hne_src] at hl
        have ⟨v', hv', hm⟩ := site_consistent_old_entry_extend_rmap hwt rf loc (path ++ [field]) hfresh_bool s' τ' hl
        exact ⟨v', by rw [lookup_insert_ne _ af s' _ heq]; exact hv', hm⟩
    rmap_live := rmap_live_extend_fresh hwt rf loc (path ++ [field]) hreadref_field
    rmap_paths := by
      intro r1 r2 hr1 hr2 p hp
      -- Helpers for rmap' lookup
      have hrmap'_rf : rmap'.map rf = some (loc, path ++ [field]) := by simp [rmap']
      have hrmap'_ne : ∀ r, r ≠ rf → rmap'.map r = rmap.map r := by
        intro r hr; simp [rmap', hr]
      rw [hrefs_eq] at hr1 hr2
      simp only [List.mem_cons] at hr1 hr2
      rcases hr1 with h1eq | hr1_mem <;> rcases hr2 with h2eq | hr2_mem
      · -- (rf, rf): self-loop ε
        rw [h1eq, h2eq] at hp ⊢
        unfold pe' update_with_extension at hp
        simp only [↓reduceIte] at hp; subst hp
        unfold PathReflectedInHeap; simp only [hrmap'_rf]
        intro _; exact ⟨by simp [fieldPathOf], hreadref_field⟩
      · -- (rf, r2): pe'.paths(rf, r2) = der(pe.paths(s, r2), [.field field])
        rw [h1eq] at hp ⊢
        have hr2_ne : r2 ≠ rf := fun h => hrf_fresh_pe (h ▸ hr2_mem)
        unfold pe' update_with_extension at hp
        simp only [hr2_ne, and_false, ite_false, ite_true] at hp
        -- hp : interpret_regex (der (env.pathEnv.paths (s, r2)) [.field field]) p
        simp only [der, List.foldl] at hp
        -- hp : interpret_regex (env.pathEnv.paths (s, r2)) (.field field :: p)
        have hold := hwt.rmap_paths s r2 hs_in_refs hr2_mem (.field field :: p) hp
        unfold PathReflectedInHeap at hold ⊢
        rw [hrmap'_rf, hrmap'_ne r2 hr2_ne]
        cases hrmap_r2 : rmap.map r2 with
        | none => simp
        | some lr2 =>
          obtain ⟨loc2, path2⟩ := lr2
          simp only [hrmap_s] at hold; simp only [hrmap_r2] at hold ⊢
          intro heq_loc
          obtain ⟨hpath, hlive⟩ := hold heq_loc
          refine ⟨?_, hlive⟩
          simp only [fieldPathOf] at hpath
          rw [hpath]; simp [List.append_assoc]
      · -- (r1, rf): pe'.paths(r1, rf) = extend(pe.paths(r1, s), [.field field])
        rw [h2eq] at hp ⊢
        have hr1_ne : r1 ≠ rf := fun h => hrf_fresh_pe (h ▸ hr1_mem)
        unfold pe' update_with_extension at hp
        simp only [hr1_ne, false_and, ite_false, ite_true] at hp
        -- hp : interpret_regex (extend (env.pathEnv.paths (r1, s)) [.field field]) p
        simp only [extend, List.foldl, interpret_regex] at hp
        obtain ⟨s1, s2, heq_p, hinterp1, hs2_eq⟩ := hp
        -- s2 matches char(.field field): s2 = [.field field]
        subst hs2_eq
        -- heq_p : p = s1 ++ [.field field]
        -- hinterp1 : interpret_regex (env.pathEnv.paths (r1, s)) s1
        have hold := hwt.rmap_paths r1 s hr1_mem hs_in_refs s1 hinterp1
        unfold PathReflectedInHeap at hold ⊢
        rw [hrmap'_ne r1 hr1_ne, hrmap'_rf]
        cases hrmap_r1 : rmap.map r1 with
        | none => simp
        | some lr1 =>
          obtain ⟨loc1, path1⟩ := lr1
          simp only [hrmap_s] at hold; simp only [hrmap_r1] at hold ⊢
          intro heq_loc
          obtain ⟨hpath1, _⟩ := hold heq_loc
          constructor
          · -- path ++ [field] = path1 ++ fieldPathOf (s1 ++ [.field field])
            rw [heq_p, fieldPathOf_append, hpath1]
            simp [fieldPathOf, List.append_assoc]
          · exact hreadref_field
      · -- (r1, r2): both old, paths unchanged
        have hr1_ne : r1 ≠ rf := fun h => hrf_fresh_pe (h ▸ hr1_mem)
        have hr2_ne : r2 ≠ rf := fun h => hrf_fresh_pe (h ▸ hr2_mem)
        unfold pe' update_with_extension at hp
        simp only [hr1_ne, hr2_ne, false_and, ite_false] at hp
        have hold := hwt.rmap_paths r1 r2 hr1_mem hr2_mem p hp
        unfold PathReflectedInHeap at hold ⊢
        rw [hrmap'_ne r1 hr1_ne, hrmap'_ne r2 hr2_ne]
        exact hold
    varEnv_refs_in_pathEnv := by
      intro x bt r_v bk_v ms hv
      have hold := hwt.varEnv_refs_in_pathEnv x bt r_v bk_v ms hv
      show r_v ∈ pe'.refs
      rw [hrefs_eq]
      exact List.mem_cons_of_mem rf hold
    siteEnv_refs_in_pathEnv := by
      intro s' bt_s r_s bk_s hl
      show r_s ∈ pe'.refs
      rw [hrefs_eq]
      by_cases heq : s' = af
      · subst heq; rw [lookup_insert_same] at hl
        have hrf_eq : r_s = rf := by
          simp only [Option.some.injEq, MoveType.ref.injEq] at hl; exact hl.2.1.symm
        rw [hrf_eq]; exact .head _
      · rw [lookup_insert_ne _ af s' _ heq] at hl
        have hne_src : s' ≠ src := by
          intro h; subst h; rw [lookup_delete_same] at hl; simp at hl
        rw [lookup_delete_ne _ src s' hne_src] at hl
        exact List.mem_cons_of_mem rf (hwt.siteEnv_refs_in_pathEnv s' bt_s r_s bk_s hl)
    live_refs_unique := by
      intro r_u
      refine ⟨fun x bt_x bk_x ms s' bt_s bk_s hvar hs => ?_,
              fun s1 s2 bt1 bt2 bk1 bk2 hne hs1 hs2 => ?_,
              fun x y bt1 bt2 bk1 bk2 ms1 ms2 hne hx hy =>
                (hwt.live_refs_unique r_u).2.2 x y bt1 bt2 bk1 bk2 ms1 ms2 hne hx hy⟩
      · -- var-site
        by_cases heqs : s' = af
        · subst heqs; rw [lookup_insert_same] at hs
          simp only [Option.some.injEq, MoveType.ref.injEq] at hs
          rw [← hs.2.1] at hvar
          exact absurd (hwt.varEnv_refs_in_pathEnv x bt_x rf bk_x ms hvar) hrf_fresh_pe
        · rw [lookup_insert_ne _ af s' _ heqs] at hs
          have hne_src : s' ≠ src := by
            intro h; subst h; rw [lookup_delete_same] at hs; simp at hs
          rw [lookup_delete_ne _ src s' hne_src] at hs
          exact (hwt.live_refs_unique r_u).1 x bt_x bk_x ms s' bt_s bk_s hvar hs
      · -- site-site
        by_cases heq1 : s1 = af
        · subst heq1; rw [lookup_insert_same] at hs1
          simp only [Option.some.injEq, MoveType.ref.injEq] at hs1
          rw [lookup_insert_ne _ s1 s2 _ hne.symm] at hs2
          have hne_src2 : s2 ≠ src := by
            intro h; subst h; rw [lookup_delete_same] at hs2; simp at hs2
          rw [lookup_delete_ne _ src s2 hne_src2] at hs2
          rw [← hs1.2.1] at hs2
          exact absurd (hwt.siteEnv_refs_in_pathEnv s2 bt2 rf bk2 hs2) hrf_fresh_pe
        · by_cases heq2 : s2 = af
          · subst heq2; rw [lookup_insert_same] at hs2
            simp only [Option.some.injEq, MoveType.ref.injEq] at hs2
            rw [lookup_insert_ne _ s2 s1 _ hne] at hs1
            have hne_src1 : s1 ≠ src := by
              intro h; subst h; rw [lookup_delete_same] at hs1; simp at hs1
            rw [lookup_delete_ne _ src s1 hne_src1] at hs1
            rw [← hs2.2.1] at hs1
            exact absurd (hwt.siteEnv_refs_in_pathEnv s1 bt1 rf bk1 hs1) hrf_fresh_pe
          · rw [lookup_insert_ne _ af s1 _ heq1] at hs1
            rw [lookup_insert_ne _ af s2 _ heq2] at hs2
            have hne_src1 : s1 ≠ src := by
              intro h; subst h; rw [lookup_delete_same] at hs1; simp at hs1
            have hne_src2 : s2 ≠ src := by
              intro h; subst h; rw [lookup_delete_same] at hs2; simp at hs2
            rw [lookup_delete_ne _ src s1 hne_src1] at hs1
            rw [lookup_delete_ne _ src s2 hne_src2] at hs2
            exact (hwt.live_refs_unique r_u).2.1 s1 s2 bt1 bt2 bk1 bk2 hne hs1 hs2
    blocks_typed := hwt.blocks_typed
    lenv_empty_siteEnv := hwt.lenv_empty_siteEnv
    lenv_wf := hwt.lenv_wf
    lenv_var_tracked := hwt.lenv_var_tracked
    lenv_var_unique := hwt.lenv_var_unique
    lenv_funEnv_eq := hwt.lenv_funEnv_eq
    funEnv_typed := hwt.funEnv_typed
    heap_loc_bound := hwt.heap_loc_bound
    rmap_root_none := by
      show (if Aref.root = rf then some (loc, path ++ [field]) else rmap.map .root) = none
      rw [if_neg (Ne.symm hrf_not_root)]; exact hwt.rmap_root_none
    no_paths_to_root := by
      have hroot_ne_rf : ¬(Aref.root = rf) := Ne.symm hrf_not_root
      intro u p hp
      have hp : interpret_regex (pe'.paths (u, Aref.root)) p := hp
      by_cases hu : u = rf
      · rw [hu] at hp
        unfold pe' update_with_extension at hp
        simp only [hroot_ne_rf, and_false, ite_false, ite_true] at hp
        -- hp : interpret_regex (der (env.pathEnv.paths (s, .root)) [.field field]) p
        simp only [der, List.foldl] at hp
        have hp' : interpret_regex (env.pathEnv.paths (s, Aref.root)) (.field field :: p) := hp
        have ⟨hueq, _⟩ := hwt.no_paths_to_root s _ hp'
        exact absurd hueq hs_not_root
      · unfold pe' update_with_extension at hp
        simp only [hu, hroot_ne_rf, ite_false] at hp
        exact hwt.no_paths_to_root u p hp
    root_path_coherence := by
      have hroot_ne_rf : ¬(Aref.root = rf) := Ne.symm hrf_not_root
      intro v' y rest hv_mem hp loc_v path_v hrmap_v loc_y hloc heq
      rw [hrefs_eq] at hv_mem
      simp only [List.mem_cons] at hv_mem
      have hp : interpret_regex (pe'.paths (Aref.root, v')) (PathElement.root_to_var y :: rest) := hp
      rcases hv_mem with hv_eq | hv_in
      · -- v' = rf
        rw [hv_eq] at hp hrmap_v
        unfold pe' update_with_extension at hp
        simp only [hroot_ne_rf, false_and, ite_false, ite_true] at hp
        -- hp : interpret_regex (extend(pe.paths(.root, s), [.field field])) (.root_to_var y :: rest)
        simp only [extend, List.foldl, interpret_regex] at hp
        obtain ⟨s1, s2, heq_p, hinterp, hs2_eq⟩ := hp
        subst hs2_eq
        -- heq_p : .root_to_var y :: rest = s1 ++ [.field field]
        -- hinterp : interpret_regex (env.pathEnv.paths (.root, s)) s1
        -- rmap'(rf) = some (loc, path ++ [field])
        simp only [rmap', ite_true] at hrmap_v
        obtain ⟨h1, h2⟩ := Prod.mk.inj (Option.some.inj hrmap_v)
        subst h1; subst h2
        -- Need: loc = loc_y → fieldPathOf rest = path ++ [field]
        -- But we know path_v = path ++ [field], and need to show it = fieldPathOf (.root_to_var y :: rest)
        -- Actually goal is: loc_v = loc_y → path_v = fieldPathOf rest
        -- path_v = path ++ [field], rest is part of s1 ++ [.field field]
        -- From hinterp: pe.paths(.root, s) accepts s1, s ∈ env.pathEnv.refs
        -- From root_path_coherence on s with s1: rmap.map s = some (loc, path) →
        --   loc = loc_y → path = fieldPathOf (tail of s1 after .root_to_var y)
        -- s1 starts with .root_to_var y, rest_s1 = tail, then heq_p says:
        --   .root_to_var y :: rest = s1 ++ [.field field]
        -- So s1 = .root_to_var y :: (rest without last elem), and last of rest = .field field
        -- This is complex. Let me use init/last decomposition.
        -- Actually: .root_to_var y :: rest = s1 ++ [.field field]
        -- So s1 = (.root_to_var y :: rest).dropLast and .field field = (.root_to_var y :: rest).getLast
        -- More simply: rest ends with .field field
        -- s1 = .root_to_var y :: rest.dropLast
        -- Then from root_path_coherence with s1:
        --   rmap.map s = some (loc, path) →
        --   loc = loc_y → path = fieldPathOf (rest.dropLast)
        -- Then path_v = path ++ [field] = fieldPathOf(rest.dropLast) ++ [field]
        -- And fieldPathOf(rest) = fieldPathOf(rest.dropLast) ++ fieldPathOf([.field field])
        --                       = fieldPathOf(rest.dropLast) ++ [field]
        -- So path_v = fieldPathOf(rest). ✓
        -- Let me decompose s1 from heq_p
        have hcons_eq := heq_p
        -- .root_to_var y :: rest = s1 ++ [.field field]
        -- So s1 ++ [.field field] starts with .root_to_var y
        -- Case split on s1
        cases hs1 : s1 with
        | nil =>
          -- s1 = [] → .root_to_var y :: rest = [.field field] → contradiction
          rw [hs1] at hcons_eq; simp at hcons_eq
        | cons s1_hd s1_tl =>
          rw [hs1] at hcons_eq hinterp
          -- hcons_eq : .root_to_var y :: rest = s1_hd :: s1_tl ++ [.field field]
          simp only [List.cons_append, List.cons.injEq] at hcons_eq
          obtain ⟨hhd_eq, hrest_eq⟩ := hcons_eq
          rw [← hhd_eq] at hinterp
          -- hinterp : pe.paths(.root, s) accepts .root_to_var y :: s1_tl
          -- Use root_path_coherence from old state
          have hrpc := hwt.root_path_coherence s y s1_tl hs_in_refs hinterp loc path hrmap_s loc_y hloc heq
          -- hrpc : path = fieldPathOf s1_tl
          -- rest = s1_tl ++ [.field field], so fieldPathOf rest = fieldPathOf s1_tl ++ [field]
          rw [hrest_eq]; simp [fieldPathOf_append, fieldPathOf, hrpc]
      · -- v' ≠ rf (v' ∈ env.pathEnv.refs): paths(.root, v') unchanged
        have hv_ne : ¬(v' = rf) := fun h => by subst h; exact absurd hv_in hrf_fresh_pe
        unfold pe' update_with_extension at hp
        simp only [hroot_ne_rf, hv_ne, false_and, ite_false] at hp
        -- rmap'(v') = rmap(v') since v' ≠ rf
        simp only [rmap', if_neg hv_ne] at hrmap_v
        exact hwt.root_path_coherence v' y rest hv_in hp loc_v path_v hrmap_v loc_y hloc heq
    paths_from_non_member_empty := by
      exact update_with_extension_paths_from_non_member rf s [.field field] env.pathEnv
        hwt.paths_from_non_member_empty (Or.inl hs_in_refs)
    paths_to_non_member_empty := by
      exact update_with_extension_paths_to_non_member rf s [.field field] env.pathEnv
        hwt.paths_to_non_member_empty (Or.inl hs_in_refs)
    self_loop_only_empty := by
      intro u p hp
      unfold pe' update_with_extension at hp
      by_cases hu : u = rf
      · subst hu; simp only [↓reduceIte] at hp; exact hp
      · simp only [show ¬(u = rf) from hu, and_false, ↓reduceIte] at hp
        exact hwt.self_loop_only_empty u p hp
    rmap_has_type := by
      intro r_arg bt_r loc_r path_r hrmap_r hcond
      by_cases hrt : r_arg = rf
      · -- r_arg = rf: rmap'(rf) = (loc, path ++ [field])
        simp only [rmap', hrt, ite_true] at hrmap_r
        obtain ⟨h1, h2⟩ := Prod.mk.inj (Option.some.inj hrmap_r)
        rw [← h1, ← h2]
        -- From old state: src has .ref (.trecord fentries) s bk, rmap(s) = (loc, path)
        obtain ⟨v_parent, hread_parent, hht_parent⟩ :=
          hwt.rmap_has_type s (.trecord fentries) loc path hrmap_s (Or.inr ⟨src, bk, hlookup_src⟩)
        -- Extract that v_parent is a record
        obtain ⟨fields, hveq⟩ := hht_parent.record_fields
        subst hveq
        -- From HasType.readPath_field
        obtain ⟨vf, hread_field_val, hht_field⟩ := hht_parent.readPath_field hfield
        -- Need to extract bt_r = bt' from condition
        rcases hcond with ⟨x', bk', ms', hvar'⟩ | ⟨s', bk', hsite'⟩
        · -- varEnv unchanged, rf is fresh → contradiction
          rw [hrt] at hvar'
          exact absurd (hwt.varEnv_refs_in_pathEnv x' bt_r rf bk' ms' hvar') hrf_fresh_pe
        · by_cases heqs : s' = af
          · subst heqs; rw [lookup_insert_same] at hsite'
            simp only [Option.some.injEq, MoveType.ref.injEq] at hsite'
            rw [hrt] at hsite'
            rw [← hsite'.1]
            refine ⟨vf, ?_, hht_field⟩
            -- readRef loc (path ++ [field]) = some vf
            -- readPath (.record fields) [field] = some vf from hread_field_val
            -- readPath (.record fields) path = some (.record fields) from hread_parent
            -- readRef loc (path ++ [field]) via readPath_append
            -- Goal: m.heap.readRef loc (path ++ [field]) = some vf
            -- hread_parent : m.heap.readRef loc path = some (.record fields)
            -- hread_field_val : readPath (.record fields) [field] = some vf
            have hreadref_eq : m.heap.readRef loc (path ++ [field]) =
                (m.heap.readRef loc path).bind (readPath · [field]) := by
              unfold Heap.readRef
              cases hr : Heap.read m.heap loc with
              | none => simp [bind, Option.bind]
              | some v0 => simp only [bind, Option.bind]; exact readPath_append v0 path [field]
            rw [hreadref_eq, hread_parent]
            simp only [Option.bind]
            exact hread_field_val
          · rw [lookup_insert_ne _ af s' _ heqs] at hsite'
            have hne_src : s' ≠ src := by
              intro h; subst h; rw [lookup_delete_same] at hsite'; simp at hsite'
            rw [lookup_delete_ne _ src s' hne_src] at hsite'
            rw [hrt] at hsite'
            exact absurd (hwt.siteEnv_refs_in_pathEnv s' bt_r rf bk' hsite') hrf_fresh_pe
      · -- r_arg ≠ rf: rmap'(r_arg) = rmap(r_arg), delegate to old
        simp only [rmap', if_neg hrt] at hrmap_r
        apply hwt.rmap_has_type r_arg bt_r loc_r path_r hrmap_r
        rcases hcond with ⟨x', bk', ms', hvar'⟩ | ⟨s', bk', hsite'⟩
        · exact Or.inl ⟨x', bk', ms', hvar'⟩
        · by_cases heqs : s' = af
          · subst heqs; rw [lookup_insert_same] at hsite'
            simp only [Option.some.injEq, MoveType.ref.injEq] at hsite'
            exact absurd hsite'.2.1.symm hrt
          · rw [lookup_insert_ne _ af s' _ heqs] at hsite'
            have hne_src : s' ≠ src := by
              intro h; subst h; rw [lookup_delete_same] at hsite'; simp at hsite'
            rw [lookup_delete_ne _ src s' hne_src] at hsite'
            exact Or.inr ⟨s', bk', hsite'⟩
  }

/-- Preservation for borrowField: thin wrapper around preservation_borrowField. -/
private theorem preservation_borrowFieldImm (m m' : Machine) (env : TypeEnv) (lenv : LabelEnv)
    (retType : MoveType) (rmap : RefMap)
    (hwt : WellTypedState m env lenv retType rmap)
    (hss : StackSafe m.stack m.frame.returnInfo m.heap)
    (af : Site) (src : Site) (bt : BasicMoveType) (field : Field) (cont : Stmt)
    (hstmt : m.frame.stmt = .letBind af (.borrowField src bt field) cont)
    (hstep : step (.running m) = .running m') :
    ∃ env' lenv' retType' rmap',
      WellTypedState m' env' lenv' retType' rmap' ∧
      StackSafe m'.stack m'.frame.returnInfo m'.heap := by
  obtain ⟨bt', isBor, fentries, s, rf, hlookup_src, hbt, hfield, hfresh, hnv, hcont⟩ :=
    inv_borrowField (by rw [← hstmt]; exact hwt.stmt_typed)
  subst hbt
  obtain ⟨vref, hvref, hmatch⟩ := hwt.site_consistent src (.ref (.trecord fentries) s isBor) hlookup_src
  obtain ⟨loc, path, hveq, hrmap_s⟩ := hmatch
  have hrs : readSite m src = some vref := hvref
  rw [hveq] at hrs
  simp only [step, hstmt, hrs, ExecState.running.injEq] at hstep; subst hstep
  exact preservation_borrowField m env lenv retType rmap hwt hss af src field cont isBor
    bt' fentries s rf hlookup_src hfield hfresh hnv hcont loc path hrmap_s

/-- Preservation for borrowMutField: thin wrapper around preservation_borrowField. -/
private theorem preservation_borrowMutField (m m' : Machine) (env : TypeEnv) (lenv : LabelEnv)
    (retType : MoveType) (rmap : RefMap)
    (hwt : WellTypedState m env lenv retType rmap)
    (hss : StackSafe m.stack m.frame.returnInfo m.heap)
    (af : Site) (src : Site) (bt : BasicMoveType) (field : Field) (cont : Stmt)
    (hstmt : m.frame.stmt = .letBind af (.borrowMutField src bt field) cont)
    (hstep : step (.running m) = .running m') :
    ∃ env' lenv' retType' rmap',
      WellTypedState m' env' lenv' retType' rmap' ∧
      StackSafe m'.stack m'.frame.returnInfo m'.heap := by
  obtain ⟨btf, fentries, s, rf, hlookup_src, hbt, hfield, hfresh, hnv, hcont⟩ :=
    inv_borrowMutField (by rw [← hstmt]; exact hwt.stmt_typed)
  subst hbt
  obtain ⟨vref, hvref, hmatch⟩ := hwt.site_consistent src (.ref (.trecord fentries) s .siteBorrowMut) hlookup_src
  obtain ⟨loc, path, hveq, hrmap_s⟩ := hmatch
  have hrs : readSite m src = some vref := hvref
  rw [hveq] at hrs
  simp only [step, hstmt, hrs, ExecState.running.injEq] at hstep; subst hstep
  exact preservation_borrowField m env lenv retType rmap hwt hss af src field cont .siteBorrowMut
    btf fentries s rf hlookup_src hfield hfresh hnv hcont loc path hrmap_s

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
    lenv_wf := hwt.lenv_wf
    lenv_var_tracked := hwt.lenv_var_tracked
    lenv_var_unique := hwt.lenv_var_unique
    lenv_funEnv_eq := hwt.lenv_funEnv_eq
    funEnv_typed := hwt.funEnv_typed
    heap_loc_bound := heap_loc_bound_after_alloc heap v hlb
    rmap_root_none := hwt.rmap_root_none
    no_paths_to_root := hwt.no_paths_to_root
    root_path_coherence := hwt.root_path_coherence
    paths_from_non_member_empty := hwt.paths_from_non_member_empty
    paths_to_non_member_empty := hwt.paths_to_non_member_empty
    self_loop_only_empty := hwt.self_loop_only_empty
    rmap_has_type := by
      intro r bt loc path hrmap hcond
      obtain ⟨val, hread, hht⟩ := hwt.rmap_has_type r bt loc path hrmap hcond
      have hlt := hlb loc (readRef_implies_read heap loc path (hwt.rmap_live r loc path hrmap))
      have hne : loc ≠ heap.nextLoc := by intro h; subst h; exact Nat.lt_irrefl _ hlt
      rw [heap_alloc_preserves_readRef heap v loc path hne]
      exact ⟨val, hread, hht⟩
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

/-- WellTypedState is preserved under heap.writeRef.
    The write at (loc, wpath) changes the root value at loc from baseVal to
    writePath baseVal wpath vval. All WellTypedState invariants are preserved because:
    - For locations ≠ loc: heap reads unchanged
    - For loc with basic-typed vars: writePath_preserves_HasType_general + HasType_transfer
    - For loc with ref-typed vars: impossible (ref can't coexist with writePath success)
    - For rmap_live/rmap_paths: heap_writeRef_preserves_readRef_same_loc + suffix transfer
    - For rmap_has_type: writePath_preserves_readPath_HasType -/
private theorem wellTypedState_heap_writeRef
    (frame : Frame) (stack : List Frame) (heap heap' : Heap)
    (loc : Loc) (wpath : List Field) (vval v_leaf : Value) (τ : BasicMoveType)
    (env : TypeEnv) (lenv : LabelEnv) (retType : MoveType) (rmap : RefMap)
    (hwt : WellTypedState ⟨frame, stack, heap⟩ env lenv retType rmap)
    (hwr : heap.writeRef loc wpath vval = some heap')
    (hv_leaf_read : heap.readRef loc wpath = some v_leaf)
    (hv_leaf_ht : HasType v_leaf τ)
    (hmval : HasType vval τ) :
    WellTypedState ⟨frame, stack, heap'⟩ env lenv retType rmap := by
  -- Extract base value and writePath facts
  have hlb := hwt.heap_loc_bound
  simp only [Heap.readRef, bind, Option.bind] at hv_leaf_read
  simp only [Heap.writeRef, bind, Option.bind] at hwr
  cases hbase : heap.read loc with
  | none => simp [hbase] at hv_leaf_read
  | some baseVal =>
    simp only [hbase] at hv_leaf_read hwr
    cases hwp : writePath baseVal wpath vval with
    | none => simp [hwp] at hwr
    | some newRoot =>
      simp [hwp] at hwr
      -- hwr : heap' = heap.write loc newRoot (or reverse)
      -- hv_leaf_read : readPath baseVal wpath = some v_leaf
      -- Helper: reads at other locations
      have hread_diff : ∀ loc', loc' ≠ loc → heap'.read loc' = heap.read loc' := by
        intro loc' hne; rw [← hwr]
        exact heap_write_preserves_read heap loc loc' newRoot (Ne.symm hne)
      have hread_loc : heap'.read loc = some newRoot := by
        rw [← hwr]; simp [Heap.write, Heap.read, lookup_insert_same]
      -- Reconstruct the full writeRef for helpers that need it
      have hwr_full : heap.writeRef loc wpath vval = some heap' := by
        simp [Heap.writeRef, bind, Option.bind, hbase, hwp, hwr]
      exact {
        env_wf := hwt.env_wf
        stmt_typed := hwt.stmt_typed
        var_consistent := by
          intro x isv τ_x ms hvar
          have hvc := hwt.var_consistent x isv τ_x ms hvar
          cases isv with
          | validVar =>
            obtain ⟨loc_x, v_x, hvarStore, hread_x, hmatch_x⟩ := hvc
            by_cases hloc : loc_x = loc
            · subst hloc
              have hveq : v_x = baseVal := by
                rw [hbase] at hread_x; simp only [Option.some.injEq] at hread_x; exact hread_x.symm
              subst hveq
              refine ⟨loc_x, newRoot, hvarStore, hread_loc, ?_⟩
              cases τ_x with
              | basic bt_x =>
                dsimp only [ValueMatchesType] at hmatch_x ⊢
                exact writePath_preserves_HasType_general v_x wpath vval newRoot bt_x
                  hmatch_x hwp (by
                    intro bt_leaf htap
                    obtain ⟨bt', htap'⟩ := readPath_ne_none_implies_typeAtPath v_x bt_x
                      wpath hmatch_x (by rw [hv_leaf_read]; exact Option.some_ne_none _)
                    rw [htap'] at htap; simp only [Option.some.injEq] at htap; subst htap
                    obtain ⟨u, hru, hhu⟩ := HasType_typeAtPath v_x bt_x wpath bt' hmatch_x htap'
                    rw [hv_leaf_read] at hru; simp only [Option.some.injEq] at hru; subst hru
                    exact HasType_transfer hhu hv_leaf_ht hmval)
              | ref bt_ref r_ref bk_ref =>
                exfalso
                dsimp only [ValueMatchesType] at hmatch_x
                obtain ⟨loc', path', hveq, _⟩ := hmatch_x
                rw [hveq] at hwp hv_leaf_read
                cases wpath with
                | cons f rest => simp [writePath] at hwp
                | nil =>
                  simp [readPath] at hv_leaf_read; rw [← hv_leaf_read] at hv_leaf_ht
                  exact HasType_not_ref loc' path' τ hv_leaf_ht
            · exact ⟨loc_x, v_x, hvarStore, by rw [hread_diff loc_x hloc]; exact hread_x, hmatch_x⟩
          | invalidVar => exact hvc
        site_consistent := hwt.site_consistent
        rmap_live := by
          intro r' loc' path' hrmap'
          have hlive := hwt.rmap_live r' loc' path' hrmap'
          by_cases hloc : loc = loc'
          · subst hloc
            exact heap_writeRef_preserves_readRef_same_loc heap loc wpath path' vval heap'
              hwr_full hlive (by
                intro suffix hsuffix
                cases suffix with
                | nil => simp [readPath]
                | cons sf srest =>
                  simp only [Heap.readRef, bind, Option.bind, hbase] at hlive
                  rw [← hsuffix, readPath_append] at hlive
                  simp only [hv_leaf_read, Option.bind] at hlive
                  exact HasType_transfer_readPath_ne_none v_leaf vval τ
                    (sf :: srest) hv_leaf_ht hmval hlive)
          · simp only [Heap.readRef, bind, Option.bind] at hlive ⊢
            rw [hread_diff loc' (Ne.symm hloc)]
            exact hlive
        rmap_paths := by
          intro r1 r2 hr1 hr2 p hp
          have hpih := hwt.rmap_paths r1 r2 hr1 hr2 p hp
          unfold PathReflectedInHeap at hpih ⊢
          cases hrm1 : rmap.map r1 with
          | none => simp [hrm1] at hpih ⊢
          | some p1 =>
            obtain ⟨loc1, path1⟩ := p1
            cases hrm2 : rmap.map r2 with
            | none => simp [hrm1, hrm2] at hpih ⊢
            | some p2 =>
              obtain ⟨loc2, path2⟩ := p2
              simp only [hrm1, hrm2] at hpih ⊢
              intro hloc_eq
              obtain ⟨hpath_eq, hne⟩ := hpih hloc_eq
              refine ⟨hpath_eq, ?_⟩
              by_cases hloc2 : loc = loc2
              · subst hloc2
                exact heap_writeRef_preserves_readRef_same_loc heap loc wpath path2 vval heap'
                  hwr_full hne (by
                    intro suffix hsuffix
                    cases suffix with
                    | nil => simp [readPath]
                    | cons sf srest =>
                      simp only [Heap.readRef, bind, Option.bind, hbase] at hne
                      rw [← hsuffix, readPath_append] at hne
                      simp only [hv_leaf_read, Option.bind] at hne
                      exact HasType_transfer_readPath_ne_none v_leaf vval τ
                        (sf :: srest) hv_leaf_ht hmval hne)
              · simp only [Heap.readRef, bind, Option.bind] at hne ⊢
                rw [hread_diff loc2 (Ne.symm hloc2)]
                exact hne
        varEnv_refs_in_pathEnv := hwt.varEnv_refs_in_pathEnv
        siteEnv_refs_in_pathEnv := hwt.siteEnv_refs_in_pathEnv
        live_refs_unique := hwt.live_refs_unique
        blocks_typed := hwt.blocks_typed
        lenv_empty_siteEnv := hwt.lenv_empty_siteEnv
        lenv_wf := hwt.lenv_wf
        lenv_var_tracked := hwt.lenv_var_tracked
        lenv_var_unique := hwt.lenv_var_unique
        lenv_funEnv_eq := hwt.lenv_funEnv_eq
        funEnv_typed := hwt.funEnv_typed
        heap_loc_bound := heap_loc_bound_after_writeRef heap loc wpath vval heap' hlb hwr_full
        rmap_root_none := hwt.rmap_root_none
        no_paths_to_root := hwt.no_paths_to_root
        root_path_coherence := hwt.root_path_coherence
        paths_from_non_member_empty := hwt.paths_from_non_member_empty
        paths_to_non_member_empty := hwt.paths_to_non_member_empty
        self_loop_only_empty := hwt.self_loop_only_empty
        rmap_has_type := by
          intro r' bt loc' path' hrmap' hcond
          obtain ⟨v_old, hread_old, hht_old⟩ := hwt.rmap_has_type r' bt loc' path' hrmap' hcond
          by_cases hloc' : loc = loc'
          · subst hloc'
            simp only [Heap.readRef, bind, Option.bind, hbase] at hread_old
            obtain ⟨vnew, hread_vnew, hht_vnew⟩ := writePath_preserves_readPath_HasType
              baseVal wpath path' vval newRoot v_leaf v_old τ bt
              hwp hread_old hht_old hv_leaf_read hv_leaf_ht hmval
            exact ⟨vnew, by simp [Heap.readRef, bind, Option.bind, hread_loc, hread_vnew], hht_vnew⟩
          · refine ⟨v_old, ?_, hht_old⟩
            simp only [Heap.readRef, bind, Option.bind] at hread_old ⊢
            rw [hread_diff loc' (Ne.symm hloc')]
            exact hread_old
      }

/-- StackSafe is preserved under heap.writeRef -/
private theorem stackSafe_heap_writeRef (stack : List Frame) (ri : Option ReturnInfo)
    (heap heap' : Heap) (loc : Loc) (wpath : List Field)
    (vval v_leaf : Value) (τ : BasicMoveType)
    (hss : StackSafe stack ri heap)
    (hwr : heap.writeRef loc wpath vval = some heap')
    (hv_leaf_read : heap.readRef loc wpath = some v_leaf)
    (hv_leaf_ht : HasType v_leaf τ)
    (hmval : HasType vval τ) :
    StackSafe stack ri heap' := by
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
          wellTypedState_heap_writeRef _ _ heap heap' loc wpath vval v_leaf τ
            env' lenv' retType' rmap' hwt' hwr hv_leaf_read hv_leaf_ht hmval,
          stackSafe_heap_writeRef rest callerFrame.returnInfo heap heap' loc wpath
            vval v_leaf τ hss' hwr hv_leaf_read hv_leaf_ht hmval⟩
      · exact stackSafe_heap_writeRef rest callerFrame.returnInfo heap heap' loc wpath
          vval v_leaf τ hrest hwr hv_leaf_read hv_leaf_ht hmval

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
  · subst hu
    rw [if_neg (fun ⟨_, h⟩ => hr_not_root h.symm), if_pos (Or.inl rfl)] at hp
    exact hp.elim
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
          have ⟨val', hval', hht_val⟩ :=
            hwt.rmap_has_type r τ loc path hrmap (Or.inr ⟨src, isBor, hlookup⟩)
          have : val = val' := Option.some.inj (hrd.symm.trans hval')
          subst this
          exact ⟨val, lookup_insert_same _ _ _, hht_val⟩
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
      lenv_wf := hwt.lenv_wf
      lenv_var_tracked := hwt.lenv_var_tracked
      lenv_var_unique := hwt.lenv_var_unique
      lenv_funEnv_eq := hwt.lenv_funEnv_eq
      funEnv_typed := hwt.funEnv_typed
      heap_loc_bound := hwt.heap_loc_bound
      rmap_root_none := hwt.rmap_root_none
      no_paths_to_root := no_paths_to_root_delete_ref_node' hwt r hr_not_root
      root_path_coherence := root_path_coherence_delete_ref_node' hwt r hr_not_root
      paths_from_non_member_empty :=
        delete_ref_node_paths_from_non_member env.pathEnv r hwt.paths_from_non_member_empty
      paths_to_non_member_empty :=
        delete_ref_node_paths_to_non_member env.pathEnv r hwt.paths_to_non_member_empty
      self_loop_only_empty := by
        intro u p hp
        simp only [delete_ref_node] at hp
        by_cases hu : u = r
        · subst hu; rw [if_pos ⟨rfl, rfl⟩] at hp; exact hp
        · simp only [hu, false_or, ↓reduceIte] at hp
          exact hwt.self_loop_only_empty u p hp
      rmap_has_type := by
        intro r' bt loc path hrmap hcond
        apply hwt.rmap_has_type r' bt loc path hrmap
        rcases hcond with ⟨x, bk, ms, hvar⟩ | ⟨s', bk, hsite⟩
        · exact Or.inl ⟨x, bk, ms, hvar⟩
        · by_cases heqs : s' = s
          · subst heqs; simp [lookup_insert_same] at hsite
          · rw [lookup_insert_ne _ s s' _ heqs] at hsite
            have hne_src : s' ≠ src := by
              intro h; subst h; rw [lookup_delete_same] at hsite; simp at hsite
            rw [lookup_delete_ne _ src s' hne_src] at hsite
            exact Or.inr ⟨s', bk, hsite⟩
    }

/-- If evalBinop succeeds and binop_type determines the output type,
    the result value has the output type. -/
private lemma evalBinop_has_type (op : Binop) (bt1 bt2 bt3 : BasicMoveType)
    (na nb : Nat) (result : Value)
    (hbt : binop_type op bt1 bt2 = some bt3)
    (heval : evalBinop op na nb = some result) :
    HasType result bt3 := by
  cases op <;> simp only [binop_type] at hbt <;>
    (try (cases bt1 <;> cases bt2 <;> simp at hbt)) <;>
    subst hbt <;>
    simp only [evalBinop, Option.some.injEq] at heval <;>
    (try subst heval) <;>
    first
    | exact HasType.int _
    | exact HasType.bool _
    | (-- div/mod: heval has a match on nb
       cases nb with
       | zero => simp at heval
       | succ n =>
         simp only [Option.some.injEq] at heval
         subst heval; exact HasType.int _)

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
  have hsc : ∀ result, HasType result bt3 → ∀ s' τ',
      lookup (insert (delete (delete env.siteEnv sA) sB) s (.basic bt3)) s' = some τ' →
      ∃ v', lookup (insert m.frame.siteStore s result) s' = some v' ∧
            ValueMatchesType v' τ' rmap := by
    intro result hht_result s' τ' hl
    by_cases heq : s' = s
    · subst heq; simp only [lookup_insert_same, Option.some.injEq] at hl; subst hl
      exact ⟨result, lookup_insert_same _ _ _, hht_result⟩
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
    site_consistent := hsc result (evalBinop_has_type op bt1 bt2 bt3 na nb result hbt heval)
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
    lenv_wf := hwt.lenv_wf
    lenv_var_tracked := hwt.lenv_var_tracked
    lenv_var_unique := hwt.lenv_var_unique
    lenv_funEnv_eq := hwt.lenv_funEnv_eq
    funEnv_typed := hwt.funEnv_typed
    heap_loc_bound := hwt.heap_loc_bound
    rmap_root_none := hwt.rmap_root_none
    no_paths_to_root := hwt.no_paths_to_root
    root_path_coherence := hwt.root_path_coherence
    paths_from_non_member_empty := hwt.paths_from_non_member_empty
    paths_to_non_member_empty := hwt.paths_to_non_member_empty
    self_loop_only_empty := hwt.self_loop_only_empty
    rmap_has_type := by
      intro r bt loc path hrmap hcond
      apply hwt.rmap_has_type r bt loc path hrmap
      rcases hcond with ⟨x, bk, ms, hvar⟩ | ⟨s', bk, hsite⟩
      · exact Or.inl ⟨x, bk, ms, hvar⟩
      · by_cases heq : s' = s
        · subst heq; simp [lookup_insert_same] at hsite
        · rw [lookup_insert_ne _ s s' _ heq] at hsite
          have hne_b : s' ≠ sB := by
            intro h; rw [h, lookup_delete_same] at hsite; simp at hsite
          rw [lookup_delete_ne _ sB s' hne_b] at hsite
          have hne_a : s' ≠ sA := by
            intro h; rw [h, lookup_delete_same] at hsite; simp at hsite
          rw [lookup_delete_ne _ sA s' hne_a] at hsite
          exact Or.inr ⟨s', bk, hsite⟩
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
    lenv_wf := hwt.lenv_wf
    lenv_var_tracked := hwt.lenv_var_tracked
    lenv_var_unique := hwt.lenv_var_unique
    lenv_funEnv_eq := hwt.lenv_funEnv_eq
    funEnv_typed := hwt.funEnv_typed
    heap_loc_bound := hwt.heap_loc_bound
    rmap_root_none := hwt.rmap_root_none
    no_paths_to_root := no_paths_to_root_delete_ref_node' hwt r hr_not_root
    root_path_coherence := root_path_coherence_delete_ref_node' hwt r hr_not_root
    paths_from_non_member_empty :=
      delete_ref_node_paths_from_non_member env.pathEnv r hwt.paths_from_non_member_empty
    paths_to_non_member_empty :=
      delete_ref_node_paths_to_non_member env.pathEnv r hwt.paths_to_non_member_empty
    self_loop_only_empty := by
      intro u p hp
      simp only [delete_ref_node] at hp
      by_cases hu : u = r
      · subst hu; rw [if_pos ⟨rfl, rfl⟩] at hp; exact hp
      · simp only [hu, false_or, ↓reduceIte] at hp
        exact hwt.self_loop_only_empty u p hp
    rmap_has_type := by
      intro r' bt loc path hrmap hcond
      apply hwt.rmap_has_type r' bt loc path hrmap
      rcases hcond with ⟨x, bk, ms, hvar⟩ | ⟨s', bk, hsite⟩
      · exact Or.inl ⟨x, bk, ms, hvar⟩
      · have hne : s' ≠ site := by
          intro h; subst h; rw [lookup_delete_same] at hsite; simp at hsite
        rw [lookup_delete_ne env.siteEnv site s' hne] at hsite
        exact Or.inr ⟨s', bk, hsite⟩
  }

private theorem preservation_writeRef (m m' : Machine) (env : TypeEnv) (lenv : LabelEnv)
    (retType : MoveType) (rmap : RefMap)
    (hwt : WellTypedState m env lenv retType rmap)
    (hss : StackSafe m.stack m.frame.returnInfo m.heap)
    (dst val : Site) (cont : Stmt)
    (hstmt : m.frame.stmt = .writeRef dst val cont)
    (hstep : step (.running m) = .running m') :
    ∃ env' lenv' retType' rmap',
      WellTypedState m' env' lenv' retType' rmap' ∧
      StackSafe m'.stack m'.frame.returnInfo m'.heap := by
  -- 1. Invert typing
  obtain ⟨τ, r, hdst_type, hval_type, hcheck, hcont⟩ :=
    inv_writeRef (by rw [← hstmt]; exact hwt.stmt_typed)
  -- 2. Get concrete values from site_consistent
  obtain ⟨vdst, hvdst, hmdst⟩ := hwt.site_consistent dst (.ref τ r .siteBorrowMut) hdst_type
  obtain ⟨loc, wpath, hveq, hrmap⟩ := hmdst
  obtain ⟨vval, hvval, hmval⟩ := hwt.site_consistent val (.basic τ) hval_type
  -- hmval : HasType vval τ
  -- 3. Show readSite succeeds
  have hrs_dst : readSite m dst = some (.ref loc wpath) := by rw [readSite, hvdst, hveq]
  have hrs_val : readSite m val = some vval := hvval
  -- 4. Show writeRef succeeds (from rmap_live)
  have hheap := hwt.rmap_live r loc wpath hrmap
  obtain ⟨heap', hwr⟩ := readRef_ne_none_implies_writeRef_ne_none m.heap loc wpath vval hheap
  -- 5. Step gives m'
  simp only [step, hstmt, hrs_dst, hrs_val, hwr, ExecState.running.injEq] at hstep; subst hstep
  -- 6. Key facts
  have hr_not_root : r ≠ .root := hwt.env_wf.siteEnv_wf dst (.ref τ r .siteBorrowMut) hdst_type
  have hcheck_empty := check_outbound_only_empty env.pathEnv r hcheck
  -- rmap_has_type for the ref r
  have hrmap_ht := hwt.rmap_has_type r τ loc wpath hrmap (Or.inr ⟨dst, .siteBorrowMut, hdst_type⟩)
  obtain ⟨v_leaf, hv_leaf_read, hv_leaf_ht⟩ := hrmap_ht
  -- Helper: heap'.read at different locations is unchanged
  have hread_diff : ∀ loc', loc' ≠ loc → heap'.read loc' = m.heap.read loc' := by
    intro loc' hne
    simp only [Heap.writeRef, bind, Option.bind] at hwr
    cases hbase : m.heap.read loc with
    | none => simp [hbase] at hwr
    | some baseVal =>
      simp [hbase] at hwr
      cases hwp : writePath baseVal wpath vval with
      | none => simp [hwp] at hwr
      | some newVal =>
        simp [hwp] at hwr; rw [← hwr]
        exact heap_write_preserves_read m.heap loc loc' newVal (Ne.symm hne)
  -- 7. Construct WellTypedState for m'
  refine ⟨{env with siteEnv := delete (delete env.siteEnv val) dst,
                     pathEnv := delete_ref_node env.pathEnv r},
          lenv, retType, rmap, ?_,
          stackSafe_heap_writeRef m.stack m.frame.returnInfo m.heap heap' loc wpath
            vval v_leaf τ hss hwr hv_leaf_read hv_leaf_ht hmval⟩
  exact {
    env_wf := ⟨delete_ref_node_wellformed env.pathEnv r hwt.env_wf.pathEnv_wf hr_not_root,
               SiteEnv.delete_refs_not_root _ dst
                 (SiteEnv.delete_refs_not_root _ val hwt.env_wf.siteEnv_wf),
               hwt.env_wf.varEnv_wf⟩
    stmt_typed := hcont
    var_consistent := by
      intro x isv τ_x ms hvar
      have hvc := hwt.var_consistent x isv τ_x ms hvar
      cases isv with
      | validVar =>
        dsimp only at hvc ⊢
        obtain ⟨loc_x, v_x, hvarStore, hread_x, hmatch_x⟩ := hvc
        by_cases hloc : loc = loc_x
        · -- Same location: heap value at loc changes due to writeRef
          subst hloc  -- eliminates loc_x, keeps loc
          -- Extract writePath and new root value from writeRef
          have ⟨newRootVal, hwp, hread_new⟩ :
              ∃ nv, writePath v_x wpath vval = some nv ∧ heap'.read loc = some nv := by
            simp only [Heap.writeRef, bind, Option.bind, hread_x] at hwr
            cases hwp' : writePath v_x wpath vval with
            | none => simp [hwp'] at hwr
            | some nv =>
              simp [hwp'] at hwr
              exact ⟨nv, rfl, by rw [← hwr]; simp [Heap.write, Heap.read, lookup_insert_same]⟩
          refine ⟨loc, newRootVal, hvarStore, hread_new, ?_⟩
          -- ValueMatchesType newRootVal τ_x rmap
          cases τ_x with
          | basic bt_x =>
            dsimp only [ValueMatchesType] at hmatch_x ⊢
            exact writePath_preserves_HasType_general v_x wpath vval newRootVal bt_x
              hmatch_x hwp (by
                intro bt_leaf htap
                -- Derive readPath v_x wpath = some v_leaf from readRef
                have hread_leaf : readPath v_x wpath = some v_leaf := by
                  simp only [Heap.readRef, bind, Option.bind, hread_x] at hv_leaf_read
                  exact hv_leaf_read
                -- HasType_typeAtPath gives HasType v_leaf bt_leaf
                obtain ⟨u, hread_u, hht_u⟩ :=
                  HasType_typeAtPath v_x bt_x wpath bt_leaf hmatch_x htap
                rw [hread_leaf] at hread_u
                simp only [Option.some.injEq] at hread_u; subst hread_u
                -- Transfer: HasType v_leaf bt_leaf → HasType v_leaf τ → HasType vval τ → HasType vval bt_leaf
                exact HasType_transfer hht_u hv_leaf_ht hmval)
          | ref bt_ref r_ref bk_ref =>
            -- Variable x has ref type at same location as write target — impossible
            exfalso
            dsimp only [ValueMatchesType] at hmatch_x
            obtain ⟨loc', path', hveq, _⟩ := hmatch_x
            rw [hveq] at hwp hread_x
            -- readRef loc wpath succeeds (from rmap_has_type for r at loc),
            -- but v_x = .ref so readPath (.ref ...) at non-empty path = none
            -- and at empty path, the leaf IS .ref which can't have HasType
            cases wpath with
            | cons f rest => simp [writePath] at hwp
            | nil =>
              simp only [Heap.readRef, bind, Option.bind, hread_x, readPath,
                          Option.some.injEq] at hv_leaf_read
              rw [← hv_leaf_read] at hv_leaf_ht
              exact HasType_not_ref loc' path' τ hv_leaf_ht
        · -- Different location: heap value unchanged
          exact ⟨loc_x, v_x, hvarStore, (hread_diff loc_x (Ne.symm hloc)).trans hread_x, hmatch_x⟩
      | invalidVar =>
        dsimp only at hvc ⊢
        rcases hvc with hvc_none | ⟨loc_x, hvc_some⟩
        · exact Or.inl hvc_none
        · exact Or.inr ⟨loc_x, hvc_some⟩
    site_consistent := by
      intro s' τ' hl
      have hne_dst : s' ≠ dst := by
        intro h; subst h; rw [lookup_delete_same] at hl; simp at hl
      rw [lookup_delete_ne _ dst s' hne_dst] at hl
      have hne_val : s' ≠ val := by
        intro h; subst h; rw [lookup_delete_same] at hl; simp at hl
      rw [lookup_delete_ne _ val s' hne_val] at hl
      exact hwt.site_consistent s' τ' hl
    rmap_live := by
      intro r' loc' path' hrmap'
      have hlive := hwt.rmap_live r' loc' path' hrmap'
      by_cases hloc : loc = loc'
      · subst hloc
        exact heap_writeRef_preserves_readRef_same_loc m.heap loc wpath path' vval heap'
          hwr hlive (by
            intro suffix hsuffix
            cases suffix with
            | nil => simp [readPath]
            | cons sf srest =>
              -- Derive readPath v_leaf (sf :: srest) ≠ none from old heap
              have hleaf_suffix : readPath v_leaf (sf :: srest) ≠ none := by
                simp only [Heap.readRef, bind, Option.bind] at hlive hv_leaf_read
                cases hbase : m.heap.read loc with
                | none => simp [hbase] at hv_leaf_read
                | some baseVal =>
                  simp only [hbase] at hlive hv_leaf_read
                  rw [← hsuffix, readPath_append] at hlive
                  simp only [hv_leaf_read, Option.bind] at hlive
                  exact hlive
              -- Transfer readPath success from v_leaf to vval via shared type τ
              exact HasType_transfer_readPath_ne_none v_leaf vval τ
                (sf :: srest) hv_leaf_ht hmval hleaf_suffix)
      · rwa [heap_writeRef_preserves_readRef_diff_loc m.heap loc loc' wpath path' vval heap'
               hloc hwr]
    rmap_paths := by
      intro r1 r2 hr1 hr2 p hp
      have hr1_orig : r1 ∈ env.pathEnv.refs := by
        simp only [delete_ref_node_refs, List.mem_filter, decide_eq_true_eq] at hr1; exact hr1.1
      have hr2_orig : r2 ∈ env.pathEnv.refs := by
        simp only [delete_ref_node_refs, List.mem_filter, decide_eq_true_eq] at hr2; exact hr2.1
      have hr1_ne_r : r1 ≠ r := by
        simp only [delete_ref_node_refs, List.mem_filter, decide_eq_true_eq] at hr1; exact hr1.2
      have hr2_ne_r : r2 ≠ r := by
        simp only [delete_ref_node_refs, List.mem_filter, decide_eq_true_eq] at hr2; exact hr2.2
      simp only [delete_ref_node, hr1_ne_r, hr2_ne_r, false_or, ↓reduceIte] at hp
      have hpih := hwt.rmap_paths r1 r2 hr1_orig hr2_orig p hp
      unfold PathReflectedInHeap at hpih ⊢
      cases hrm1 : rmap.map r1 with
      | none => simp [hrm1] at hpih ⊢
      | some p1 =>
        obtain ⟨loc1, path1⟩ := p1
        cases hrm2 : rmap.map r2 with
        | none => simp [hrm1, hrm2] at hpih ⊢
        | some p2 =>
          obtain ⟨loc2, path2⟩ := p2
          simp only [hrm1, hrm2] at hpih ⊢
          intro hloc_eq
          obtain ⟨hpath_eq, hne⟩ := hpih hloc_eq
          refine ⟨hpath_eq, ?_⟩
          by_cases hloc2 : loc = loc2
          · subst hloc2
            exact heap_writeRef_preserves_readRef_same_loc m.heap loc wpath path2 vval heap'
              hwr hne (by
                intro suffix hsuffix
                cases suffix with
                | nil => simp [readPath]
                | cons sf srest =>
                  -- Same pattern as rmap_live suffix case
                  have hleaf_suffix : readPath v_leaf (sf :: srest) ≠ none := by
                    simp only [Heap.readRef, bind, Option.bind] at hne hv_leaf_read
                    cases hbase : m.heap.read loc with
                    | none => simp [hbase] at hv_leaf_read
                    | some baseVal =>
                      simp only [hbase] at hne hv_leaf_read
                      rw [← hsuffix, readPath_append] at hne
                      simp only [hv_leaf_read, Option.bind] at hne
                      exact hne
                  exact HasType_transfer_readPath_ne_none v_leaf vval τ
                    (sf :: srest) hv_leaf_ht hmval hleaf_suffix)
          · rwa [heap_writeRef_preserves_readRef_diff_loc m.heap loc loc2 wpath path2 vval heap'
                   hloc2 hwr]
    varEnv_refs_in_pathEnv :=
      varEnv_refs_in_pathEnv_delete_ref_node hwt r dst τ (.siteBorrowMut) hdst_type
    siteEnv_refs_in_pathEnv := by
      intro s' bt r' bk hl
      have hne_dst : s' ≠ dst := by
        intro h; subst h; rw [lookup_delete_same] at hl; simp at hl
      rw [lookup_delete_ne _ dst s' hne_dst] at hl
      have hne_val : s' ≠ val := by
        intro h; subst h; rw [lookup_delete_same] at hl; simp at hl
      rw [lookup_delete_ne _ val s' hne_val] at hl
      have hr'_in := hwt.siteEnv_refs_in_pathEnv s' bt r' bk hl
      have hr'_ne : r' ≠ r := by
        intro heq; rw [heq] at hl
        exact (hwt.live_refs_unique r).2.1 s' dst bt τ bk .siteBorrowMut hne_dst hl hdst_type
      simp only [delete_ref_node_refs, List.mem_filter, decide_eq_true_eq]
      exact ⟨hr'_in, hr'_ne⟩
    live_refs_unique := by
      intro r'
      refine ⟨fun x' bt bk ms' s' bt' bk' hvar' hs' => ?_,
              fun s1 s2 bt1 bt2 bk1 bk2 hne hs1 hs2 => ?_,
              fun x1 x2 bt1 bt2 bk1 bk2 ms1 ms2 hne hx1 hx2 =>
                (hwt.live_refs_unique r').2.2 x1 x2 bt1 bt2 bk1 bk2 ms1 ms2 hne hx1 hx2⟩
      · have hne_dst : s' ≠ dst := by
          intro h; subst h; rw [lookup_delete_same] at hs'; simp at hs'
        rw [lookup_delete_ne _ dst s' hne_dst] at hs'
        have hne_val : s' ≠ val := by
          intro h; subst h; rw [lookup_delete_same] at hs'; simp at hs'
        rw [lookup_delete_ne _ val s' hne_val] at hs'
        exact (hwt.live_refs_unique r').1 x' bt bk ms' s' bt' bk' hvar' hs'
      · have hne1_dst : s1 ≠ dst := by
          intro h; subst h; rw [lookup_delete_same] at hs1; simp at hs1
        rw [lookup_delete_ne _ dst s1 hne1_dst] at hs1
        have hne1_val : s1 ≠ val := by
          intro h; subst h; rw [lookup_delete_same] at hs1; simp at hs1
        rw [lookup_delete_ne _ val s1 hne1_val] at hs1
        have hne2_dst : s2 ≠ dst := by
          intro h; subst h; rw [lookup_delete_same] at hs2; simp at hs2
        rw [lookup_delete_ne _ dst s2 hne2_dst] at hs2
        have hne2_val : s2 ≠ val := by
          intro h; subst h; rw [lookup_delete_same] at hs2; simp at hs2
        rw [lookup_delete_ne _ val s2 hne2_val] at hs2
        exact (hwt.live_refs_unique r').2.1 s1 s2 bt1 bt2 bk1 bk2 hne hs1 hs2
    blocks_typed := hwt.blocks_typed
    lenv_empty_siteEnv := hwt.lenv_empty_siteEnv
    lenv_wf := hwt.lenv_wf
    lenv_var_tracked := hwt.lenv_var_tracked
    lenv_var_unique := hwt.lenv_var_unique
    lenv_funEnv_eq := hwt.lenv_funEnv_eq
    funEnv_typed := hwt.funEnv_typed
    heap_loc_bound := heap_loc_bound_after_writeRef m.heap loc wpath vval heap' hwt.heap_loc_bound hwr
    rmap_root_none := hwt.rmap_root_none
    no_paths_to_root := no_paths_to_root_delete_ref_node' hwt r hr_not_root
    root_path_coherence := root_path_coherence_delete_ref_node' hwt r hr_not_root
    paths_from_non_member_empty :=
      delete_ref_node_paths_from_non_member env.pathEnv r hwt.paths_from_non_member_empty
    paths_to_non_member_empty :=
      delete_ref_node_paths_to_non_member env.pathEnv r hwt.paths_to_non_member_empty
    self_loop_only_empty := by
      intro u p hp
      simp only [delete_ref_node] at hp
      by_cases hu : u = r
      · subst hu; rw [if_pos ⟨rfl, rfl⟩] at hp; exact hp
      · simp only [hu, false_or, ↓reduceIte] at hp
        exact hwt.self_loop_only_empty u p hp
    rmap_has_type := by
      intro r' bt loc' path' hrmap' hcond
      have hcond' : (∃ x bk ms, lookup env.varEnv x = some (.validVar, .ref bt r' bk, ms)) ∨
                    (∃ s bk, lookup env.siteEnv s = some (.ref bt r' bk)) := by
        rcases hcond with ⟨x, bk, ms, hvar⟩ | ⟨s', bk, hsite⟩
        · exact Or.inl ⟨x, bk, ms, hvar⟩
        · have hne_dst : s' ≠ dst := by
            intro h; subst h; rw [lookup_delete_same] at hsite; simp at hsite
          rw [lookup_delete_ne _ dst s' hne_dst] at hsite
          have hne_val : s' ≠ val := by
            intro h; subst h; rw [lookup_delete_same] at hsite; simp at hsite
          rw [lookup_delete_ne _ val s' hne_val] at hsite
          exact Or.inr ⟨s', bk, hsite⟩
      obtain ⟨v_old, hread_old, hht_old⟩ := hwt.rmap_has_type r' bt loc' path' hrmap' hcond'
      by_cases hloc' : loc = loc'
      · subst hloc'
        -- Same location: use writePath_preserves_readPath_HasType
        -- Extract base value and readPath facts from readRef
        simp only [Heap.readRef, bind, Option.bind] at hread_old hv_leaf_read
        have hwr' := hwr
        simp only [Heap.writeRef, bind, Option.bind] at hwr'
        cases hbase : m.heap.read loc with
        | none => simp [hbase] at hv_leaf_read
        | some baseVal =>
          simp only [hbase] at hread_old hv_leaf_read hwr'
          cases hwp2 : writePath baseVal wpath vval with
          | none => simp [hwp2] at hwr'
          | some newRoot =>
            simp [hwp2] at hwr'
            -- hwr' : m.heap.write loc newRoot = heap'
            obtain ⟨vnew, hread_vnew, hht_vnew⟩ := writePath_preserves_readPath_HasType
              baseVal wpath path' vval newRoot v_leaf v_old τ bt
              hwp2 hread_old hht_old hv_leaf_read hv_leaf_ht hmval
            refine ⟨vnew, ?_, hht_vnew⟩
            rw [← hwr']
            simp only [Heap.readRef, bind, Option.bind, Heap.write, Heap.read,
                        lookup_insert_same, hread_vnew]
      · have hread' : heap'.readRef loc' path' = some v_old := by
          rw [heap_writeRef_preserves_readRef_diff_loc m.heap loc loc' wpath path' vval heap'
                hloc' hwr]
          exact hread_old
        exact ⟨v_old, hread', hht_old⟩
  }

-- ============================================================
-- Unpack helpers: addFieldSites and runtime foldl lemmas
-- ============================================================

private theorem addFieldSites_nil (fentries : AssocMap Field BasicMoveType)
    (se : AssocMap Site MoveType) :
    addFieldSites fentries se [] = se := rfl

private theorem addFieldSites_cons (fentries : AssocMap Field BasicMoveType)
    (se : AssocMap Site MoveType) (f : Field) (s : Site) (rest : List (Field × Site)) :
    addFieldSites fentries se ((f, s) :: rest) =
    addFieldSites fentries
      (match AssocMap.lookup fentries f with
       | some bt => insert se s (.basic bt)
       | none => se) rest := rfl

private theorem addFieldSites_lookup_not_in_fields
    (fentries : AssocMap Field BasicMoveType) (se : AssocMap Site MoveType)
    (fields : List (Field × Site)) (a : Site)
    (hnotin : a ∉ fields.map Prod.snd) :
    lookup (addFieldSites fentries se fields) a = lookup se a := by
  induction fields generalizing se with
  | nil => simp [addFieldSites_nil]
  | cons hd tl ih =>
    obtain ⟨f, s⟩ := hd
    simp only [List.map, List.mem_cons, not_or] at hnotin
    obtain ⟨hne, hnotin_tl⟩ := hnotin
    rw [addFieldSites_cons]
    rw [ih _ hnotin_tl]
    cases hlookup : lookup fentries f with
    | none => rfl
    | some bt => exact lookup_insert_ne se s a (.basic bt) hne

private theorem addFieldSites_lookup_mem
    (fentries : AssocMap Field BasicMoveType) (se : AssocMap Site MoveType)
    (fields : List (Field × Site)) (f : Field) (a : Site) (bt : BasicMoveType)
    (hmem : (f, a) ∈ fields)
    (hftype : lookup fentries f = some bt)
    (huniq : ∀ f', (f', a) ∈ fields → f' = f) :
    lookup (addFieldSites fentries se fields) a = some (.basic bt) := by
  induction fields generalizing se with
  | nil => nomatch hmem
  | cons hd tl ih =>
    obtain ⟨f', s⟩ := hd
    rw [addFieldSites_cons]
    simp only [List.mem_cons, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | hmem_tl
    · -- head is (f, a)
      rw [hftype]
      by_cases ha_tl : a ∈ tl.map Prod.snd
      · -- a appears again in tl
        obtain ⟨⟨f'', _⟩, hmem_tl', heq⟩ := List.mem_map.mp ha_tl
        simp at heq; subst heq
        have hf'' : f'' = f := huniq f'' (List.mem_cons_of_mem _ hmem_tl')
        subst hf''
        exact ih _ hmem_tl' (fun f''' hf''' => huniq f''' (List.mem_cons_of_mem _ hf'''))
      · -- a does not appear again
        rw [addFieldSites_lookup_not_in_fields _ _ _ _ ha_tl]
        exact lookup_insert_same se a (.basic bt)
    · -- (f, a) ∈ tl
      have huniq_tl : ∀ f', (f', a) ∈ tl → f' = f :=
        fun f' hf' => huniq f' (List.mem_cons_of_mem _ hf')
      cases hlookup : lookup fentries f' with
      | none => exact ih se hmem_tl huniq_tl
      | some bt' =>
        exact ih _ hmem_tl huniq_tl

private theorem unpack_foldl_lookup_not_in_fields
    (recFields : List (Field × Value)) (siteStore : AssocMap Site Value)
    (fields : List (Field × Site)) (a : Site)
    (hnotin : a ∉ fields.map Prod.snd) :
    lookup (fields.foldl (fun ss (fa : Field × Site) =>
      match recFields.lookup fa.1 with
      | some v => AssocMap.insert ss fa.2 v
      | none => ss) siteStore) a = lookup siteStore a := by
  induction fields generalizing siteStore with
  | nil => simp [List.foldl]
  | cons hd tl ih =>
    obtain ⟨f, s⟩ := hd
    simp only [List.map, List.mem_cons, not_or] at hnotin
    obtain ⟨hne, hnotin_tl⟩ := hnotin
    simp only [List.foldl]
    rw [ih _ hnotin_tl]
    cases hlookup : recFields.lookup f with
    | none => rfl
    | some v => exact lookup_insert_ne siteStore s a v hne

private theorem unpack_foldl_lookup_mem
    (recFields : List (Field × Value)) (siteStore : AssocMap Site Value)
    (fields : List (Field × Site)) (f : Field) (a : Site) (v : Value)
    (hmem : (f, a) ∈ fields)
    (hfval : recFields.lookup f = some v)
    (huniq : ∀ f', (f', a) ∈ fields → f' = f) :
    lookup (fields.foldl (fun ss (fa : Field × Site) =>
      match recFields.lookup fa.1 with
      | some v => AssocMap.insert ss fa.2 v
      | none => ss) siteStore) a = some v := by
  induction fields generalizing siteStore with
  | nil => nomatch hmem
  | cons hd tl ih =>
    obtain ⟨f', s⟩ := hd
    simp only [List.foldl]
    simp only [List.mem_cons, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | hmem_tl
    · -- head is (f, a)
      rw [hfval]
      by_cases ha_tl : a ∈ tl.map Prod.snd
      · obtain ⟨⟨f'', _⟩, hmem_tl', heq⟩ := List.mem_map.mp ha_tl
        simp at heq; subst heq
        have hf'' : f'' = f := huniq f'' (List.mem_cons_of_mem _ hmem_tl')
        subst hf''
        exact ih _ hmem_tl' (fun f''' hf''' => huniq f''' (List.mem_cons_of_mem _ hf'''))
      · rw [unpack_foldl_lookup_not_in_fields _ _ _ _ ha_tl]
        exact lookup_insert_same siteStore a v
    · have huniq_tl : ∀ f', (f', a) ∈ tl → f' = f :=
        fun f' hf' => huniq f' (List.mem_cons_of_mem _ hf')
      cases hlookup : recFields.lookup f' with
      | none => exact ih siteStore hmem_tl huniq_tl
      | some v' => exact ih _ hmem_tl huniq_tl

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

/-- If collectPackFields succeeds and (f, a) ∈ fieldSites, the value at a is in fieldVals -/
private lemma list_lookup_ne_none_of_mem [BEq α] [LawfulBEq α]
    {l : List (α × β)} {a : α} {b : β} (h : (a, b) ∈ l) : l.lookup a ≠ none := by
  induction l with
  | nil => nomatch h
  | cons hd tl ih =>
    obtain ⟨k, v⟩ := hd
    simp only [List.lookup]
    simp only [List.mem_cons, Prod.mk.injEq] at h
    rcases h with ⟨rfl, rfl⟩ | h'
    · simp
    · split
      · exact nofun
      · exact ih h'

private lemma collectPackFields_mem
    (siteStore : SiteStore) (fieldSites : List (Field × Site))
    (fieldVals : List (Field × Value))
    (hcpf : collectPackFields siteStore fieldSites = some fieldVals)
    (f : Field) (a : Site) (hmem : (f, a) ∈ fieldSites) :
    ∃ v, lookup siteStore a = some v ∧ (f, v) ∈ fieldVals := by
  induction fieldSites generalizing fieldVals with
  | nil => nomatch hmem
  | cons hd tl ih =>
    obtain ⟨f', s'⟩ := hd
    simp only [collectPackFields, bind, Option.bind, pure, Pure.pure] at hcpf
    cases hlk : lookup siteStore s' with
    | none => rw [hlk] at hcpf; simp at hcpf
    | some v' =>
      rw [hlk] at hcpf
      cases hrec : collectPackFields siteStore tl with
      | none => rw [hrec] at hcpf; simp at hcpf
      | some vs' =>
        rw [hrec] at hcpf; simp only [Option.some.injEq] at hcpf; subst hcpf
        cases hmem with
        | head => exact ⟨v', hlk, List.mem_cons_self⟩
        | tail _ hmem' =>
          obtain ⟨v, hv, hmv⟩ := ih vs' hrec hmem'
          exact ⟨v, hv, List.mem_cons_of_mem _ hmv⟩

/-- If collectPackFields succeeds and fieldVals.lookup f = some v, then (f, a) ∈ fieldSites
    for some a with lookup siteStore a = some v -/
private lemma collectPackFields_lookup_inv
    (siteStore : SiteStore) (fieldSites : List (Field × Site))
    (fieldVals : List (Field × Value))
    (hcpf : collectPackFields siteStore fieldSites = some fieldVals)
    (f : Field) (v : Value) (hlookup : fieldVals.lookup f = some v) :
    ∃ a, (f, a) ∈ fieldSites ∧ lookup siteStore a = some v := by
  induction fieldSites generalizing fieldVals with
  | nil => simp [collectPackFields] at hcpf; subst hcpf; simp at hlookup
  | cons hd tl ih =>
    obtain ⟨f', s'⟩ := hd
    simp only [collectPackFields, bind, Option.bind, pure, Pure.pure] at hcpf
    cases hlk : lookup siteStore s' with
    | none => rw [hlk] at hcpf; simp at hcpf
    | some v' =>
      rw [hlk] at hcpf
      cases hrec : collectPackFields siteStore tl with
      | none => rw [hrec] at hcpf; simp at hcpf
      | some vs' =>
        rw [hrec] at hcpf; simp only [Option.some.injEq] at hcpf; subst hcpf
        simp only [List.lookup] at hlookup
        cases hbeq : (f == f') with
        | true =>
          simp only [hbeq] at hlookup
          have hf_eq : f = f' := eq_of_beq hbeq
          subst hf_eq
          exact ⟨s', List.mem_cons_self, by simp only [Option.some.injEq] at hlookup; subst hlookup; exact hlk⟩
        | false =>
          simp only [hbeq] at hlookup
          obtain ⟨a, ha, hv⟩ := ih vs' hrec hlookup
          exact ⟨a, List.mem_cons_of_mem _ ha, hv⟩

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
  obtain ⟨fentries, hfield_map, hcomplete, hcont⟩ := inv_pack (by rw [← hstmt]; exact hwt.stmt_typed)
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
          exact ⟨.record fieldVals, lookup_insert_same _ _ _,
            HasType.record fieldVals fentries
              (fun f hne_fent => by
                obtain ⟨a, ha_mem⟩ := hcomplete f hne_fent
                obtain ⟨v, _, hv_mem⟩ := collectPackFields_mem m.frame.siteStore fieldSites
                  fieldVals hcpf f a ha_mem
                exact list_lookup_ne_none_of_mem hv_mem)
              (fun f hne_fv => by
                cases hv : fieldVals.lookup f with
                | none => exact absurd hv hne_fv
                | some v =>
                  obtain ⟨a, ha_mem, _⟩ := collectPackFields_lookup_inv m.frame.siteStore
                    fieldSites fieldVals hcpf f v hv
                  obtain ⟨_, _, hfent_bt⟩ := hfield_map f a ha_mem
                  rw [hfent_bt]; exact Option.some_ne_none _)
              (fun f bt v hfent hval => by
                obtain ⟨a, ha_mem, ha_store⟩ := collectPackFields_lookup_inv m.frame.siteStore
                  fieldSites fieldVals hcpf f v hval
                obtain ⟨bt', hsite_bt, hfent_bt⟩ := hfield_map f a ha_mem
                have hbt_eq : bt = bt' := Option.some.inj (hfent.symm.trans hfent_bt)
                subst hbt_eq
                obtain ⟨v', hv', hht'⟩ := hwt.site_consistent a (.basic bt) hsite_bt
                have hv_eq : v = v' := Option.some.inj (ha_store.symm.trans hv')
                subst hv_eq
                exact hht')⟩
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
      lenv_wf := hwt.lenv_wf
      lenv_var_tracked := hwt.lenv_var_tracked
      lenv_var_unique := hwt.lenv_var_unique
      lenv_funEnv_eq := hwt.lenv_funEnv_eq
      funEnv_typed := hwt.funEnv_typed
      heap_loc_bound := hwt.heap_loc_bound
      rmap_root_none := hwt.rmap_root_none
      no_paths_to_root := hwt.no_paths_to_root
      root_path_coherence := hwt.root_path_coherence
      paths_from_non_member_empty := hwt.paths_from_non_member_empty
      paths_to_non_member_empty := hwt.paths_to_non_member_empty
      self_loop_only_empty := hwt.self_loop_only_empty
      rmap_has_type := by
        intro r bt loc path hrmap hcond
        apply hwt.rmap_has_type r bt loc path hrmap
        rcases hcond with ⟨x, bk, ms, hvar⟩ | ⟨s', bk, hsite⟩
        · exact Or.inl ⟨x, bk, ms, hvar⟩
        · by_cases heq : s' = s
          · subst heq; simp [lookup_insert_same] at hsite
          · rw [lookup_insert_ne _ s s' _ heq] at hsite
            exact Or.inr ⟨s', bk, lookup_deleteAll_some env.siteEnv _ s' _ hsite⟩
    }

private theorem preservation_assign_valid (m m' : Machine) (env : TypeEnv) (lenv : LabelEnv)
    (retType : MoveType) (rmap : RefMap)
    (hwt : WellTypedState m env lenv retType rmap)
    (hss : StackSafe m.stack m.frame.returnInfo m.heap)
    (x : Var) (a : Site) (cont : Stmt)
    (ax : Site) (τ : BasicMoveType) (ms : Mut) (r : Aref)
    (hvar : lookup env.varEnv x = some (.validVar, .basic τ, ms))
    (ha_type : lookup env.siteEnv a = some (.basic τ))
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
          (update_with_epsilon_wellformed r r env.pathEnv hwt.env_wf.pathEnv_wf hr_not_root)
          hr_not_root)
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
          -- Use ha_type to get HasType for the value at site a
          obtain ⟨v', hv', hht⟩ := hwt.site_consistent a (.basic τ) ha_type
          have hv_eq : v = v' := Option.some.inj (hrs.symm.trans hv')
          subst hv_eq
          exact ⟨(m.heap.alloc v).2, v, lookup_insert_same _ _ _,
                 heap_alloc_read_new m.heap v, hht⟩
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
      lenv_wf := hwt.lenv_wf
      lenv_var_tracked := hwt.lenv_var_tracked
      lenv_var_unique := hwt.lenv_var_unique
      lenv_funEnv_eq := hwt.lenv_funEnv_eq
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
            exact delete_ref_node_paths_involving_r _ r r .root hr_not_root (Or.inl rfl)
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
      paths_from_non_member_empty := by
        have h_eps_refs : (update_with_epsilon r r env.pathEnv).refs = r :: env.pathEnv.refs := by
          simp only [update_with_epsilon, update_with_extension]
          simp only [show ¬r ∈ env.pathEnv.refs from hr_fresh, not_false_eq_true, ↓reduceIte]
        have h_root_in_mid : Aref.root ∈ (update_with_epsilon r r env.pathEnv).refs :=
          h_eps_refs ▸ List.mem_cons_of_mem _ hwt.env_wf.pathEnv_wf.root_in_refs
        exact garbage_collect_paths_from_non_member _ r
          (update_with_extension_paths_from_non_member r .root [.root_to_var x] _
            (by unfold update_with_epsilon
                exact update_with_extension_paths_from_non_member r r [] env.pathEnv
                  hwt.paths_from_non_member_empty (Or.inr rfl))
            (Or.inl h_root_in_mid))
      paths_to_non_member_empty := by
        have h_eps_refs : (update_with_epsilon r r env.pathEnv).refs = r :: env.pathEnv.refs := by
          simp only [update_with_epsilon, update_with_extension]
          simp only [show ¬r ∈ env.pathEnv.refs from hr_fresh, not_false_eq_true, ↓reduceIte]
        have h_root_in_mid : Aref.root ∈ (update_with_epsilon r r env.pathEnv).refs :=
          h_eps_refs ▸ List.mem_cons_of_mem _ hwt.env_wf.pathEnv_wf.root_in_refs
        exact garbage_collect_paths_to_non_member _ r
          (update_with_extension_paths_to_non_member r .root [.root_to_var x] _
            (by unfold update_with_epsilon
                exact update_with_extension_paths_to_non_member r r [] env.pathEnv
                  hwt.paths_to_non_member_empty (Or.inr rfl))
            (Or.inl h_root_in_mid))
      self_loop_only_empty := by
        show ∀ u p, interpret_regex (pe'.paths (u, u)) p → p = []
        intro u p hp
        unfold pe' garbage_collect at hp
        by_cases hu : u = r
        · subst hu; simp only [and_self, ↓reduceIte, interpret_regex] at hp; exact hp
        · simp only [hu, false_or, ↓reduceIte] at hp
          unfold update_with_extension at hp
          simp only [show ¬(u = r) from hu, and_false, ↓reduceIte] at hp
          unfold update_with_epsilon update_with_extension at hp
          simp only [show ¬(u = r) from hu, and_false, ↓reduceIte] at hp
          exact hwt.self_loop_only_empty u p hp
      rmap_has_type := by
        intro r' bt loc path hrmap hcond
        -- rmap unchanged, heap grew by alloc
        -- Reduce new env condition to old env condition
        have hold_cond : ((∃ x' bk ms', lookup env.varEnv x' = some (.validVar, .ref bt r' bk, ms')) ∨
            (∃ s' bk, lookup env.siteEnv s' = some (.ref bt r' bk))) := by
          rcases hcond with ⟨x', bk, ms', hvar'⟩ | ⟨s', bk, hsite'⟩
          · -- varEnv unchanged
            exact Or.inl ⟨x', bk, ms', hvar'⟩
          · -- siteEnv: reduce se' to env.siteEnv
            have hl' : lookup se' s' = some (.ref bt r' bk) := hsite'
            have hs_ne_ax : s' ≠ ax := by
              intro h; subst h; simp [se', lookup_delete_same] at hl'
            have hs_ne_a : s' ≠ a := by
              intro heq; simp only [se'] at hl'
              rw [lookup_delete_ne _ ax s' hs_ne_ax, heq, lookup_delete_same] at hl'; simp at hl'
            simp only [se'] at hl'
            rw [lookup_delete_ne _ ax s' hs_ne_ax] at hl'
            rw [lookup_delete_ne _ a s' hs_ne_a] at hl'
            rw [lookup_insert_ne _ ax s' _ hs_ne_ax] at hl'
            exact Or.inr ⟨s', bk, hl'⟩
        obtain ⟨val, hread, hht⟩ := hwt.rmap_has_type r' bt loc path hrmap hold_cond
        have hlt := hwt.heap_loc_bound loc (readRef_implies_read m.heap loc path
          (hwt.rmap_live r' loc path hrmap))
        have hne : loc ≠ m.heap.nextLoc := by intro h; subst h; exact Nat.lt_irrefl _ hlt
        rw [heap_alloc_preserves_readRef m.heap v loc path hne]
        exact ⟨val, hread, hht⟩
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
  have hfresh_τ' : moveTypeRefNotRoot τ' :=
    MoveType.compatible_preserves_not_root τ τ'
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
               VarEnv.update_refs_not_root env.varEnv x (.validVar, τ', .mutable)
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
    lenv_wf := hwt.lenv_wf
    lenv_var_tracked := hwt.lenv_var_tracked
    lenv_var_unique := hwt.lenv_var_unique
    lenv_funEnv_eq := hwt.lenv_funEnv_eq
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
    paths_from_non_member_empty := hwt.paths_from_non_member_empty
    paths_to_non_member_empty := hwt.paths_to_non_member_empty
    self_loop_only_empty := hwt.self_loop_only_empty
    rmap_has_type := by
      intro r' bt loc path hrmap hcond
      -- rmap unchanged, heap grew by alloc
      have hold_cond : ((∃ x' bk ms', lookup env.varEnv x' = some (.validVar, .ref bt r' bk, ms')) ∨
          (∃ s' bk, lookup env.siteEnv s' = some (.ref bt r' bk))) := by
        rcases hcond with ⟨y, bk, ms', hvy⟩ | ⟨s', bk, hsite'⟩
        · -- varEnv: y has validVar in updated env
          have hvy' : lookup (insert env.varEnv x (.validVar, τ', .mutable)) y =
              some (.validVar, .ref bt r' bk, ms') := hvy
          by_cases heq : y = x
          · subst heq; rw [lookup_insert_same] at hvy'
            -- τ' = .ref bt r' bk, came from site a in old siteEnv
            have hτ : τ' = .ref bt r' bk := by
              simp only [Option.some.injEq, Prod.mk.injEq] at hvy'; exact hvy'.2.1
            rw [hτ] at hsite_a
            exact Or.inr ⟨a, bk, hsite_a⟩
          · rw [lookup_insert_ne _ x y _ heq] at hvy'
            exact Or.inl ⟨y, bk, ms', hvy'⟩
        · -- siteEnv: delete a
          have hne : s' ≠ a := by
            intro h; subst h; rw [lookup_delete_same] at hsite'; simp at hsite'
          rw [lookup_delete_ne env.siteEnv a s' hne] at hsite'
          exact Or.inr ⟨s', bk, hsite'⟩
      obtain ⟨val, hread, hht⟩ := hwt.rmap_has_type r' bt loc path hrmap hold_cond
      have hlt := hwt.heap_loc_bound loc (readRef_implies_read m.heap loc path
        (hwt.rmap_live r' loc path hrmap))
      have hne : loc ≠ m.heap.nextLoc := by intro h; subst h; exact Nat.lt_irrefl _ hlt
      rw [heap_alloc_preserves_readRef m.heap v loc path hne]
      exact ⟨val, hread, hht⟩
  }

/-- Preservation for freeze: converts a (possibly mutable) reference to an immutable one.
    At runtime this is a no-op (value copy). The typing env deletes the old site, inserts a new
    site with a fresh ref r', and applies consume_ref_transfer to transfer paths from r to r'. -/
private theorem preservation_freeze (m m' : Machine) (env : TypeEnv) (lenv : LabelEnv)
    (retType : MoveType) (rmap : RefMap)
    (hwt : WellTypedState m env lenv retType rmap)
    (hss : StackSafe m.stack m.frame.returnInfo m.heap)
    (s : Site) (src : Site) (cont : Stmt)
    (hstmt : m.frame.stmt = .letBind s (.freeze src) cont)
    (hstep : step (.running m) = .running m') :
    ∃ env' lenv' retType' rmap',
      WellTypedState m' env' lenv' retType' rmap' ∧
      StackSafe m'.stack m'.frame.returnInfo m'.heap := by
  -- 1. Invert typing
  obtain ⟨τ, r, r', isBor, hlookup, hnv, hfresh, hcont⟩ :=
    inv_freeze (by rw [← hstmt]; exact hwt.stmt_typed)
  -- 2. Get value at src from site_consistent
  obtain ⟨vref, hvref, hmatch⟩ := hwt.site_consistent src (.ref τ r isBor) hlookup
  obtain ⟨loc, path, hveq, hrmap⟩ := hmatch
  -- 3. Simplify step
  have hrs : readSite m src = some vref := hvref
  rw [hveq] at hrs
  simp only [step, hstmt, hrs, ExecState.running.injEq] at hstep; subst hstep
  -- 4. Freshness facts
  have hfresh_bool : freshRefInEnvBool r' env = true :=
    (freshRefInEnv_iff_freshRefInEnvBool r' env).mp hfresh
  have hfresh_pathEnv : freshRefBool r' env.pathEnv :=
    freshRefInEnvBool_implies_freshRefBool r' env hfresh_bool
  have hr'_not_root : r' ≠ Aref.root := freshRef_not_root hwt.env_wf.pathEnv_wf r' hfresh_pathEnv
  have hr'_fresh_pe : r' ∉ env.pathEnv.refs :=
    (freshRef_iff_freshRefBool r' env.pathEnv).mpr hfresh_pathEnv
  have hr_not_root : r ≠ .root := hwt.env_wf.siteEnv_wf src (.ref τ r isBor) hlookup
  have hr_in_refs : r ∈ env.pathEnv.refs := hwt.siteEnv_refs_in_pathEnv src τ r isBor hlookup
  -- 5. rmap extends: r' → rmap(r), everything else unchanged
  let rmap' : RefMap := { map := fun ref => if ref = r' then some (loc, path) else rmap.map ref }
  -- 6. Heap liveness for the new mapping
  have hlive_r : m.heap.readRef loc path ≠ none := hwt.rmap_live r loc path hrmap
  -- 7. Abbreviation for new pathEnv
  let pe' := consume_ref_transfer env.pathEnv r r'
  -- 8. pe'.refs facts
  have hpe_refs : pe'.refs = List.filter (fun x => x ≠ r) (r' :: env.pathEnv.refs) := by
    simp only [pe', consume_ref_transfer]
    simp only [hr'_fresh_pe, not_false_eq_true, ↓reduceIte]
  have hr'_ne_r : r' ≠ r := by
    intro h; rw [h] at hr'_fresh_pe; exact hr'_fresh_pe hr_in_refs
  have hr'_in_pe : r' ∈ pe'.refs := by
    rw [hpe_refs]; simp only [List.mem_filter, decide_eq_true_eq, List.mem_cons]
    exact ⟨.inl trivial, hr'_ne_r⟩
  -- 9. Construct WellTypedState
  refine ⟨{env with siteEnv := insert (delete env.siteEnv src) s (.ref τ r' .siteBorrowImm),
                     pathEnv := pe'},
          lenv, retType, rmap', ?_, hss⟩
  exact {
    env_wf := TypeEnv.delete_insert_pathEnv_wf env src s (.ref τ r' .siteBorrowImm) pe' hwt.env_wf
      (consume_ref_transfer_wellformed env.pathEnv r r' hwt.env_wf.pathEnv_wf
        hr_not_root hr'_fresh_pe hnv) hr'_not_root
    stmt_typed := hcont
    var_consistent := var_consistent_extend_rmap_fresh hwt r' loc path hfresh_bool
    site_consistent := by
      intro s' τ' hl
      by_cases heq : s' = s
      · subst heq; rw [lookup_insert_same] at hl; injection hl with hl; subst hl
        refine ⟨Value.ref loc path, lookup_insert_same _ _ _, loc, path, rfl, ?_⟩
        show (if r' = r' then some (loc, path) else rmap.map r') = some (loc, path)
        rw [if_pos rfl]
      · rw [lookup_insert_ne _ s s' _ heq] at hl
        have hne_src : s' ≠ src := by
          intro h; subst h; rw [lookup_delete_same] at hl; simp at hl
        rw [lookup_delete_ne _ src s' hne_src] at hl
        have ⟨v', hv', hm⟩ := site_consistent_old_entry_extend_rmap hwt r' loc path hfresh_bool s' τ' hl
        exact ⟨v', by rw [lookup_insert_ne _ s s' _ heq]; exact hv', hm⟩
    rmap_live := rmap_live_extend_fresh hwt r' loc path hlive_r
    rmap_paths := by
      intro r1 r2 hr1 hr2 p hp
      -- Extract membership facts from pe'.refs
      have hr1_facts : (r1 = r' ∨ r1 ∈ env.pathEnv.refs) ∧ r1 ≠ r := by
        rw [hpe_refs] at hr1; simp only [List.mem_filter, decide_eq_true_eq, List.mem_cons] at hr1
        exact hr1
      have hr2_facts : (r2 = r' ∨ r2 ∈ env.pathEnv.refs) ∧ r2 ≠ r := by
        rw [hpe_refs] at hr2; simp only [List.mem_filter, decide_eq_true_eq, List.mem_cons] at hr2
        exact hr2
      -- Simplify pe'.paths(r1, r2) using consume_ref_transfer definition
      simp only [pe', consume_ref_transfer] at hp
      simp only [hr1_facts.2, hr2_facts.2, or_false, ↓reduceIte] at hp
      -- Case split on r2 = r'
      by_cases hr2_r' : r2 = r'
      · -- Case B: r2 = r', paths = union(G(r1, r'), G(r1, r))
        rw [hr2_r'] at hp ⊢; simp only [↓reduceIte] at hp
        rcases hp with hp_old | hp_from_r
        · -- Sub-case: from G(r1, r')
          by_cases hr1_r' : r1 = r'
          · -- B1 self-loop: G(r', r'), by self_loop_only_empty p = []
            rw [hr1_r'] at hp_old ⊢
            have hpeq := hwt.self_loop_only_empty r' p hp_old
            subst hpeq
            have hrmap'_r' : rmap'.map r' = some (loc, path) := if_pos rfl
            unfold PathReflectedInHeap
            simp only [hrmap'_r']
            intro _
            exact ⟨by simp [fieldPathOf], hlive_r⟩
          · -- r1 ≠ r': paths_to_non_member_empty contradicts
            exact absurd hp_old
              (hwt.paths_to_non_member_empty r1 r' p hr'_fresh_pe hr'_not_root hr1_r')
        · -- Sub-case: from G(r1, r)
          have hr1_ne_r' : r1 ≠ r' := by
            intro heq; rw [heq] at hp_from_r
            exact hwt.paths_from_non_member_empty r' r p hr'_fresh_pe hr'_not_root hr'_ne_r hp_from_r
          have hr1_in : r1 ∈ env.pathEnv.refs := hr1_facts.1.resolve_left hr1_ne_r'
          have hold := hwt.rmap_paths r1 r hr1_in hr_in_refs p hp_from_r
          unfold PathReflectedInHeap at hold ⊢
          have h1 : rmap'.map r1 = rmap.map r1 := if_neg hr1_ne_r'
          have h2 : rmap'.map r' = some (loc, path) := if_pos rfl
          rw [h1, h2]
          rw [hrmap] at hold
          exact hold
      · -- Case A: r2 ≠ r', paths = G(r1, r2) (old paths, unchanged)
        simp only [if_neg hr2_r'] at hp
        have hr1_ne_r' : r1 ≠ r' := by
          intro heq; rw [heq] at hp
          exact hwt.paths_from_non_member_empty r' r2 p hr'_fresh_pe hr'_not_root
            (fun h => hr2_r' h.symm) hp
        have hr2_ne_r' : r2 ≠ r' := fun h => hr2_r' h
        have hr1_in : r1 ∈ env.pathEnv.refs := hr1_facts.1.resolve_left hr1_ne_r'
        have hr2_in : r2 ∈ env.pathEnv.refs := hr2_facts.1.resolve_left hr2_ne_r'
        have hold := hwt.rmap_paths r1 r2 hr1_in hr2_in p hp
        unfold PathReflectedInHeap at hold ⊢
        have h1 : rmap'.map r1 = rmap.map r1 := if_neg hr1_ne_r'
        have h2 : rmap'.map r2 = rmap.map r2 := if_neg hr2_ne_r'
        rw [h1, h2]
        exact hold
    varEnv_refs_in_pathEnv := by
      intro x bt r_v bk ms hvar
      have hold := hwt.varEnv_refs_in_pathEnv x bt r_v bk ms hvar
      -- r_v ∈ env.pathEnv.refs, need r_v ∈ pe'.refs
      -- pe'.refs = filter (≠ r) (r' :: env.pathEnv.refs)
      rw [hpe_refs]; simp only [List.mem_filter, decide_eq_true_eq, List.mem_cons]
      constructor
      · exact .inr hold
      · -- r_v ≠ r: because r_v is in varEnv and r is in siteEnv (live_refs_unique)
        intro heq; rw [heq] at hvar
        exact (hwt.live_refs_unique r).1 x bt bk ms src τ isBor hvar hlookup
    siteEnv_refs_in_pathEnv := by
      intro s' bt r_s bk hl
      by_cases heqs : s' = s
      · subst heqs; rw [lookup_insert_same] at hl
        simp only [Option.some.injEq, MoveType.ref.injEq] at hl
        rw [← hl.2.1]; exact hr'_in_pe
      · rw [lookup_insert_ne _ s s' _ heqs] at hl
        have hne_src : s' ≠ src := by
          intro h; subst h; rw [lookup_delete_same] at hl; simp at hl
        rw [lookup_delete_ne _ src s' hne_src] at hl
        have hold := hwt.siteEnv_refs_in_pathEnv s' bt r_s bk hl
        rw [hpe_refs]; simp only [List.mem_filter, decide_eq_true_eq, List.mem_cons]
        constructor
        · exact .inr hold
        · -- r_s ≠ r: because s' ≠ src but both would have r (live_refs_unique site-site)
          intro heq; rw [heq] at hl
          exact (hwt.live_refs_unique r).2.1 src s' τ bt isBor bk (Ne.symm hne_src) hlookup hl
    live_refs_unique := by
      -- siteEnv = insert (delete env.siteEnv src) s (.ref τ r' .siteBorrowImm)
      -- New site s has fresh ref r'. After deleting src, rest is like release.
      -- The insert adds r' which is fresh → use live_refs_unique_insert_fresh_ref on the deleted env
      -- But the underlying siteEnv is delete env.siteEnv src, not env.siteEnv
      -- So we need to reason about insert (delete ...) directly
      intro r_u
      refine ⟨fun x bt bk ms s' bt' bk' hvar hs => ?_,
              fun s1 s2 bt1 bt2 bk1 bk2 hne hs1 hs2 => ?_,
              fun x y bt1 bt2 bk1 bk2 ms1 ms2 hne hx hy =>
                (hwt.live_refs_unique r_u).2.2 x y bt1 bt2 bk1 bk2 ms1 ms2 hne hx hy⟩
      · -- var-site
        by_cases heqs : s' = s
        · subst heqs; rw [lookup_insert_same] at hs
          simp only [Option.some.injEq, MoveType.ref.injEq] at hs
          rw [← hs.2.1] at hvar
          -- r' is in varEnv → contradicts freshness
          exact absurd (hwt.varEnv_refs_in_pathEnv x bt r' bk ms hvar) hr'_fresh_pe
        · rw [lookup_insert_ne _ s s' _ heqs] at hs
          have hne_src : s' ≠ src := by
            intro h; subst h; rw [lookup_delete_same] at hs; simp at hs
          rw [lookup_delete_ne _ src s' hne_src] at hs
          exact (hwt.live_refs_unique r_u).1 x bt bk ms s' bt' bk' hvar hs
      · -- site-site
        by_cases heq1 : s1 = s
        · subst heq1; rw [lookup_insert_same] at hs1
          simp only [Option.some.injEq, MoveType.ref.injEq] at hs1
          have hne2 : s2 ≠ s1 := hne.symm
          rw [lookup_insert_ne _ s1 s2 _ hne2] at hs2
          have hne_src2 : s2 ≠ src := by
            intro h; subst h; rw [lookup_delete_same] at hs2; simp at hs2
          rw [lookup_delete_ne _ src s2 hne_src2] at hs2
          rw [← hs1.2.1] at hs2
          exact absurd (hwt.siteEnv_refs_in_pathEnv s2 bt2 r' bk2 hs2) hr'_fresh_pe
        · by_cases heq2 : s2 = s
          · subst heq2; rw [lookup_insert_same] at hs2
            simp only [Option.some.injEq, MoveType.ref.injEq] at hs2
            rw [lookup_insert_ne _ s2 s1 _ hne] at hs1
            have hne_src1 : s1 ≠ src := by
              intro h; subst h; rw [lookup_delete_same] at hs1; simp at hs1
            rw [lookup_delete_ne _ src s1 hne_src1] at hs1
            rw [← hs2.2.1] at hs1
            exact absurd (hwt.siteEnv_refs_in_pathEnv s1 bt1 r' bk1 hs1) hr'_fresh_pe
          · rw [lookup_insert_ne _ s s1 _ heq1] at hs1
            rw [lookup_insert_ne _ s s2 _ heq2] at hs2
            have hne_src1 : s1 ≠ src := by
              intro h; subst h; rw [lookup_delete_same] at hs1; simp at hs1
            have hne_src2 : s2 ≠ src := by
              intro h; subst h; rw [lookup_delete_same] at hs2; simp at hs2
            rw [lookup_delete_ne _ src s1 hne_src1] at hs1
            rw [lookup_delete_ne _ src s2 hne_src2] at hs2
            exact (hwt.live_refs_unique r_u).2.1 s1 s2 bt1 bt2 bk1 bk2 hne hs1 hs2
    blocks_typed := hwt.blocks_typed
    lenv_empty_siteEnv := hwt.lenv_empty_siteEnv
    lenv_wf := hwt.lenv_wf
    lenv_var_tracked := hwt.lenv_var_tracked
    lenv_var_unique := hwt.lenv_var_unique
    lenv_funEnv_eq := hwt.lenv_funEnv_eq
    funEnv_typed := hwt.funEnv_typed
    heap_loc_bound := hwt.heap_loc_bound
    rmap_root_none := rmap_root_none_extend_fresh hwt.rmap_root_none r' loc path hr'_not_root
    no_paths_to_root := by
      intro u p hp
      have hroot_ne_r : ¬(Aref.root = r) := Ne.symm hr_not_root
      have h_and : ¬(u = r ∧ Aref.root = r) := fun ⟨_, h⟩ => hroot_ne_r h
      simp only [pe', consume_ref_transfer, h_and, ↓reduceIte] at hp
      by_cases hu : u = r
      · subst hu; simp only [true_or, ↓reduceIte, interpret_regex] at hp
      · simp only [hu, hroot_ne_r, or_false, ↓reduceIte] at hp
        by_cases hroot_r' : Aref.root = r'
        · exact absurd hroot_r'.symm hr'_not_root
        · simp only [hroot_r', ↓reduceIte] at hp
          exact hwt.no_paths_to_root u p hp
    root_path_coherence := by
      intro v y rest hv_mem hp loc_v path_v hrmap_v loc_y hloc heq
      -- v ∈ pe'.refs, need to analyze paths (.root, v) in pe'
      have hroot_ne_r : ¬(Aref.root = r) := Ne.symm hr_not_root
      have hv_ne_r : v ≠ r := by
        rw [hpe_refs] at hv_mem
        simp only [List.mem_filter, decide_eq_true_eq] at hv_mem; exact hv_mem.2
      have h_and_rpc : ¬(Aref.root = r ∧ v = r) := fun ⟨h, _⟩ => hroot_ne_r h
      simp only [pe', consume_ref_transfer, h_and_rpc, ↓reduceIte] at hp
      simp only [hroot_ne_r, hv_ne_r, or_false, ↓reduceIte] at hp
      by_cases hv_r' : v = r'
      · -- v = r': paths(.root, r') = union(G(.root, r'), G(.root, r))
        rw [hv_r'] at hp hrmap_v
        simp only [ite_true] at hp
        simp only [interpret_regex] at hp
        rcases hp with hp_old | hp_from_r
        · -- From old paths (.root, r'): r' was not in refs
          -- By well-formedness refs_complete: paths from root to non-member are empty
          have := hwt.env_wf.pathEnv_wf.refs_complete r' hr'_fresh_pe
          rw [this] at hp_old
          simp [interpret_regex] at hp_old
        · -- From old paths (.root, r): rmap'(r') = some (loc, path) = rmap(r)
          -- Extract loc_v = loc, path_v = path from hrmap_v
          have hrmap'_r' : rmap'.map r' = some (loc, path) := if_pos rfl
          rw [hrmap'_r'] at hrmap_v
          simp only [Option.some.injEq, Prod.mk.injEq] at hrmap_v
          rw [← hrmap_v.1] at heq; rw [← hrmap_v.2]
          exact hwt.root_path_coherence r y rest hr_in_refs hp_from_r loc path hrmap loc_y hloc heq
      · -- v ≠ r': paths(.root, v) unchanged from old pathEnv
        simp only [hv_r', ↓reduceIte] at hp
        -- v ∈ pe'.refs and v ≠ r' → v ∈ env.pathEnv.refs
        have hv_in : v ∈ env.pathEnv.refs := by
          rw [hpe_refs] at hv_mem
          simp only [List.mem_filter, decide_eq_true_eq, List.mem_cons] at hv_mem
          rcases hv_mem.1 with h | h
          · exact absurd h hv_r'
          · exact h
        -- rmap'(v) = rmap(v) since v ≠ r'
        simp only [rmap', if_neg hv_r'] at hrmap_v
        exact hwt.root_path_coherence v y rest hv_in hp loc_v path_v hrmap_v loc_y hloc heq
    paths_from_non_member_empty :=
      consume_ref_transfer_paths_from_non_member env.pathEnv r r' hwt.paths_from_non_member_empty
    paths_to_non_member_empty :=
      consume_ref_transfer_paths_to_non_member env.pathEnv r r' hwt.paths_to_non_member_empty
    self_loop_only_empty := by
      intro u p hp
      by_cases hu_r : u = r
      · rw [hu_r] at hp
        simp only [pe', consume_ref_transfer, and_self, ↓reduceIte, interpret_regex] at hp
        exact hp
      · have h_and_sl : ¬(u = r ∧ u = r) := fun ⟨h, _⟩ => hu_r h
        simp only [pe', consume_ref_transfer, h_and_sl, ↓reduceIte] at hp
        simp only [hu_r, false_or, ↓reduceIte] at hp
        by_cases hu_r' : u = r'
        · rw [hu_r'] at hp; simp only [↓reduceIte, interpret_regex] at hp
          rcases hp with hp_old | hp_r
          · exact hwt.self_loop_only_empty r' p hp_old
          · exact absurd hp_r (hwt.paths_from_non_member_empty r' r p hr'_fresh_pe hr'_not_root hr'_ne_r)
        · simp only [hu_r', ↓reduceIte] at hp
          exact hwt.self_loop_only_empty u p hp
    rmap_has_type := by
      intro r_arg bt_arg loc_arg path_arg hrmap_arg hcond
      by_cases hrt : r_arg = r'
      · -- r_arg = r': rmap'(r') = some (loc, path), same as rmap(r)
        simp only [rmap', hrt, ite_true] at hrmap_arg
        obtain ⟨h1, h2⟩ := Prod.mk.inj (Option.some.inj hrmap_arg)
        subst h1; subst h2
        -- From old state: src has .ref τ r isBor, rmap(r) = (loc, path)
        -- Need to establish bt_arg = τ from the condition
        rcases hcond with ⟨x', bk', ms', hvar'⟩ | ⟨s', bk', hsite'⟩
        · -- varEnv unchanged, r' is fresh → contradiction
          rw [hrt] at hvar'
          exact absurd (hwt.varEnv_refs_in_pathEnv x' bt_arg r' bk' ms' hvar') hr'_fresh_pe
        · by_cases heqs : s' = s
          · subst heqs; rw [lookup_insert_same] at hsite'
            simp only [Option.some.injEq, MoveType.ref.injEq] at hsite'
            rw [hrt] at hsite'
            -- hsite'.1 : τ = bt_arg, so bt_arg = τ
            rw [← hsite'.1]
            -- Now need HasType v τ at (loc, path), using old rmap_has_type for r
            exact hwt.rmap_has_type r τ loc path hrmap (Or.inr ⟨src, isBor, hlookup⟩)
          · rw [lookup_insert_ne _ s s' _ heqs] at hsite'
            have hne_src : s' ≠ src := by
              intro h; subst h; rw [lookup_delete_same] at hsite'; simp at hsite'
            rw [lookup_delete_ne _ src s' hne_src] at hsite'
            rw [hrt] at hsite'
            exact absurd (hwt.siteEnv_refs_in_pathEnv s' bt_arg r' bk' hsite') hr'_fresh_pe
      · -- r_arg ≠ r': rmap'(r_arg) = rmap(r_arg), delegate to old
        simp only [rmap', if_neg hrt] at hrmap_arg
        apply hwt.rmap_has_type r_arg bt_arg loc_arg path_arg hrmap_arg
        rcases hcond with ⟨x', bk', ms', hvar'⟩ | ⟨s', bk', hsite'⟩
        · exact Or.inl ⟨x', bk', ms', hvar'⟩
        · by_cases heqs : s' = s
          · subst heqs; rw [lookup_insert_same] at hsite'
            simp only [Option.some.injEq, MoveType.ref.injEq] at hsite'
            exact absurd hsite'.2.1.symm hrt
          · rw [lookup_insert_ne _ s s' _ heqs] at hsite'
            have hne_src : s' ≠ src := by
              intro h; subst h; rw [lookup_delete_same] at hsite'; simp at hsite'
            rw [lookup_delete_ne _ src s' hne_src] at hsite'
            exact Or.inr ⟨s', bk', hsite'⟩
  }

-- ============================================================
-- Part 8a-unpack: Preservation for unpack
-- ============================================================

private theorem preservation_unpack (m m' : Machine) (env : TypeEnv) (lenv : LabelEnv)
    (retType : MoveType) (rmap : RefMap)
    (hwt : WellTypedState m env lenv retType rmap)
    (hss : StackSafe m.stack m.frame.returnInfo m.heap)
    (fields : List (Field × Site)) (src : Site) (cont : Stmt)
    (hstmt : m.frame.stmt = .unpack fields src cont)
    (hstep : step (.running m) = .running m') :
    ∃ env' lenv' retType' rmap',
      WellTypedState m' env' lenv' retType' rmap' ∧
      StackSafe m'.stack m'.frame.returnInfo m'.heap := by
  -- 1. Invert typing
  obtain ⟨fentries, hlookup_src, hfresh, hdistinct, hfield_exists, hcont⟩ :=
    inv_unpack (by rw [← hstmt]; exact hwt.stmt_typed)
  -- 2. Get record value from site_consistent
  obtain ⟨vsrc, hvsrc, hmatch_src⟩ := hwt.site_consistent src _ hlookup_src
  simp only [ValueMatchesType] at hmatch_src
  obtain ⟨recFields, hrec_eq⟩ := HasType.record_fields hmatch_src
  subst hrec_eq
  -- 3. readSite succeeds → simplify step
  have hrs : readSite m src = some (.record recFields) := by unfold readSite; exact hvsrc
  simp only [step, hstmt, hrs, ExecState.running.injEq] at hstep; subst hstep
  -- 4. Derive site uniqueness from distinctness
  have huniq_site : ∀ (a : Site), ∀ f f', (f, a) ∈ fields → (f', a) ∈ fields → f' = f := by
    intro a f f' hfa hf'a
    by_contra hne
    exact absurd rfl (hdistinct a a ⟨f, f', hfa, hf'a, Ne.symm hne⟩)
  -- 5. Helper: any field site in addFieldSites has basic type
  have field_site_lookup : ∀ sd fd,
      (fd, sd) ∈ fields →
      ∃ bt, lookup fentries fd = some bt ∧
        lookup (addFieldSites fentries (delete env.siteEnv src) fields) sd = some (.basic bt) :=
    fun sd fd hmem =>
      let ⟨bt, hbt⟩ := hfield_exists fd sd hmem
      ⟨bt, hbt, addFieldSites_lookup_mem fentries _ fields fd sd bt hmem hbt
        (fun f' hf' => huniq_site sd fd f' hmem hf')⟩
  -- 6. Construct new WellTypedState
  refine ⟨{env with siteEnv := addFieldSites fentries (delete env.siteEnv src) fields},
          lenv, retType, rmap, ?_, hss⟩
  exact {
    env_wf := by
      constructor
      · exact hwt.env_wf.pathEnv_wf
      · exact addFieldSites_refs_not_root fentries _ fields
              (SiteEnv.delete_refs_not_root env.siteEnv src hwt.env_wf.siteEnv_wf)
      · exact hwt.env_wf.varEnv_wf
    stmt_typed := hcont
    var_consistent := hwt.var_consistent
    site_consistent := by
      intro s' τ' hlookup_s'
      by_cases hs'_in : s' ∈ fields.map Prod.snd
      · -- s' is one of the new field sites
        obtain ⟨⟨fd, sd⟩, hmem_fd, heq_s'⟩ := List.mem_map.mp hs'_in
        simp at heq_s'; subst heq_s'
        obtain ⟨bt, hbt, hlookup_new⟩ := field_site_lookup sd fd hmem_fd
        rw [hlookup_new] at hlookup_s'
        cases hlookup_s'
        -- τ' = .basic bt, need to find value in new siteStore
        obtain ⟨vf, _, hvf_ht⟩ := HasType.readPath_field hmatch_src hbt
        -- readPath (.record recFields) [fd] = some vf implies recFields.lookup fd = some vf
        have hrf : recFields.lookup fd = some vf := by
          simp only [readPath] at *
          cases hrl : recFields.lookup fd with
          | none => simp [hrl] at *
          | some v' => simp [hrl] at *; assumption
        have hlookup_ss := unpack_foldl_lookup_mem recFields m.frame.siteStore fields
          fd sd vf hmem_fd hrf (fun f' hf' => huniq_site sd fd f' hmem_fd hf')
        exact ⟨vf, hlookup_ss, hvf_ht⟩
      · -- s' is not a new field site → delegates to old
        have hlookup_env := addFieldSites_lookup_not_in_fields fentries
          (delete env.siteEnv src) fields s' hs'_in
        rw [hlookup_env] at hlookup_s'
        have hne_src : s' ≠ src := by
          intro h; subst h; rw [lookup_delete_same] at hlookup_s'; cases hlookup_s'
        rw [lookup_delete_ne _ src s' hne_src] at hlookup_s'
        obtain ⟨v, hv, hmatch⟩ := hwt.site_consistent s' τ' hlookup_s'
        have hlookup_ss := unpack_foldl_lookup_not_in_fields recFields m.frame.siteStore
          fields s' hs'_in
        exact ⟨v, hlookup_ss ▸ hv, hmatch⟩
    rmap_live := hwt.rmap_live
    rmap_paths := hwt.rmap_paths
    varEnv_refs_in_pathEnv := hwt.varEnv_refs_in_pathEnv
    siteEnv_refs_in_pathEnv := by
      intro s' bt r bk hlookup_s'
      by_cases hs'_in : s' ∈ fields.map Prod.snd
      · -- s' is a field site → type is .basic, not .ref
        obtain ⟨⟨fd, sd⟩, hmem_fd, heq_s'⟩ := List.mem_map.mp hs'_in
        simp at heq_s'; subst heq_s'
        obtain ⟨bt', _, hlookup_new⟩ := field_site_lookup sd fd hmem_fd
        rw [hlookup_new] at hlookup_s'; cases hlookup_s'
      · -- s' is old → use old siteEnv_refs_in_pathEnv
        have hlookup_env := addFieldSites_lookup_not_in_fields fentries
          (delete env.siteEnv src) fields s' hs'_in
        rw [hlookup_env] at hlookup_s'
        have hne_src : s' ≠ src := by
          intro h; subst h; rw [lookup_delete_same] at hlookup_s'; cases hlookup_s'
        rw [lookup_delete_ne _ src s' hne_src] at hlookup_s'
        exact hwt.siteEnv_refs_in_pathEnv s' bt r bk hlookup_s'
    live_refs_unique := by
      intro r
      refine ⟨?_, ?_, ?_⟩
      · -- var-site: no ref in new siteEnv maps to r from var
        intro x bt bk ms s' bt' bk' hvar hlookup_s'
        by_cases hs'_in : s' ∈ fields.map Prod.snd
        · obtain ⟨⟨fd, sd⟩, hmem_fd, heq_s'⟩ := List.mem_map.mp hs'_in
          simp at heq_s'; subst heq_s'
          obtain ⟨_, _, hlookup_new⟩ := field_site_lookup sd fd hmem_fd
          rw [hlookup_new] at hlookup_s'; cases hlookup_s'
        · have hlookup_env := addFieldSites_lookup_not_in_fields fentries
            (delete env.siteEnv src) fields s' hs'_in
          rw [hlookup_env] at hlookup_s'
          have hne_src : s' ≠ src := by
            intro h; subst h; rw [lookup_delete_same] at hlookup_s'; cases hlookup_s'
          rw [lookup_delete_ne _ src s' hne_src] at hlookup_s'
          exact (hwt.live_refs_unique r).1 x bt bk ms s' bt' bk' hvar hlookup_s'
      · -- site-site: no two different sites in new siteEnv map to same ref
        intro s1 s2 bt1 bt2 bk1 bk2 hne12 hs1 hs2
        -- Extract both lookups to old siteEnv
        have get_old : ∀ s bt' bk', lookup (addFieldSites fentries (delete env.siteEnv src) fields) s
            = some (.ref bt' r bk') → lookup env.siteEnv s = some (.ref bt' r bk') := by
          intro s bt' bk' hs
          by_cases hs_in : s ∈ fields.map Prod.snd
          · obtain ⟨⟨fd, sd⟩, hmem_fd, heq_s⟩ := List.mem_map.mp hs_in
            simp at heq_s; subst heq_s
            obtain ⟨_, _, hlookup_new⟩ := field_site_lookup sd fd hmem_fd
            rw [hlookup_new] at hs; cases hs
          · rw [addFieldSites_lookup_not_in_fields _ _ _ _ hs_in] at hs
            have hne_src : s ≠ src := by
              intro h; subst h; rw [lookup_delete_same] at hs; cases hs
            rw [lookup_delete_ne _ src s hne_src] at hs
            exact hs
        exact (hwt.live_refs_unique r).2.1 s1 s2 bt1 bt2 bk1 bk2 hne12
          (get_old s1 bt1 bk1 hs1) (get_old s2 bt2 bk2 hs2)
      · exact (hwt.live_refs_unique r).2.2
    blocks_typed := hwt.blocks_typed
    lenv_empty_siteEnv := hwt.lenv_empty_siteEnv
    lenv_wf := hwt.lenv_wf
    lenv_var_tracked := hwt.lenv_var_tracked
    lenv_var_unique := hwt.lenv_var_unique
    lenv_funEnv_eq := hwt.lenv_funEnv_eq
    funEnv_typed := hwt.funEnv_typed
    heap_loc_bound := hwt.heap_loc_bound
    rmap_root_none := hwt.rmap_root_none
    no_paths_to_root := hwt.no_paths_to_root
    root_path_coherence := hwt.root_path_coherence
    paths_from_non_member_empty := hwt.paths_from_non_member_empty
    paths_to_non_member_empty := hwt.paths_to_non_member_empty
    self_loop_only_empty := hwt.self_loop_only_empty
    rmap_has_type := by
      intro r' bt' loc path hrmap hcond
      apply hwt.rmap_has_type r' bt' loc path hrmap
      rcases hcond with ⟨x, bk, ms, hvar⟩ | ⟨s', bk, hsite⟩
      · exact Or.inl ⟨x, bk, ms, hvar⟩
      · by_cases hs'_in : s' ∈ fields.map Prod.snd
        · obtain ⟨⟨fd, sd⟩, hmem_fd, heq_s'⟩ := List.mem_map.mp hs'_in
          simp at heq_s'; subst heq_s'
          obtain ⟨_, _, hlookup_new⟩ := field_site_lookup sd fd hmem_fd
          rw [hlookup_new] at hsite; cases hsite
        · have hlookup_env := addFieldSites_lookup_not_in_fields fentries
            (delete env.siteEnv src) fields s' hs'_in
          rw [hlookup_env] at hsite
          have hne_src : s' ≠ src := by
            intro h; subst h; rw [lookup_delete_same] at hsite; cases hsite
          rw [lookup_delete_ne _ src s' hne_src] at hsite
          exact Or.inr ⟨s', bk, hsite⟩
  }

-- ============================================================
-- Part 8a-ii: Helpers for jump/branch preservation
-- ============================================================

/-- If envL has empty siteEnv and envL.subsumes env, then env also has empty siteEnv. -/
private lemma siteEnv_empty_from_subsumes (envL env : TypeEnv)
    (hsubsumes : TypeEnv.subsumes envL env)
    (hempty : ∀ s, lookup envL.siteEnv s = none) :
    ∀ s, lookup env.siteEnv s = none := by
  intro s
  obtain ⟨σ, _, _, hse, _, _, _, _⟩ := hsubsumes
  unfold SiteEnvSubstEquiv at hse
  specialize hse s
  simp only [hempty s] at hse
  cases hs : lookup env.siteEnv s with
  | none => rfl
  | some _ => simp only [hs] at hse

/-- findBlock returns an element from the list with matching label. -/
private lemma findBlock_spec (blocks : List Block) (label : Label) (block : Block)
    (h : findBlock blocks label = some block) :
    block ∈ blocks ∧ block.label = label := by
  unfold findBlock at h
  induction blocks with
  | nil => simp at h
  | cons hd tl ih =>
    simp only [List.find?] at h
    split at h
    · rename_i htrue
      simp only [Option.some.injEq] at h; subst h
      exact ⟨List.mem_cons_self, beq_iff_eq.mp htrue⟩
    · obtain ⟨hmem, hlbl⟩ := ih h
      exact ⟨List.mem_cons_of_mem _ hmem, hlbl⟩

-- ============================================================
-- Part 8a-iii: Preservation for jump
-- ============================================================

private theorem preservation_jump (m m' : Machine) (env : TypeEnv) (lenv : LabelEnv)
    (retType : MoveType) (rmap : RefMap)
    (hwt : WellTypedState m env lenv retType rmap)
    (hss : StackSafe m.stack m.frame.returnInfo m.heap)
    (label : Label)
    (hstmt : m.frame.stmt = .jump label)
    (hstep : step (.running m) = .running m') :
    ∃ env' lenv' retType' rmap',
      WellTypedState m' env' lenv' retType' rmap' ∧
      StackSafe m'.stack m'.frame.returnInfo m'.heap := by
  -- 1. Extract typing info
  obtain ⟨envL, hlenv, hsubsumes⟩ := inv_jump (by rw [← hstmt]; exact hwt.stmt_typed)
  -- 2. Case split on findBlock (step requires it to succeed)
  cases hfb : findBlock m.frame.blocks label with
  | none =>
    exfalso; simp only [step, hstmt, hfb] at hstep; contradiction
  | some block =>
    simp only [step, hstmt, hfb, ExecState.running.injEq] at hstep; subst hstep
    -- 3. Block membership and label match
    obtain ⟨hmem, hlabel⟩ := findBlock_spec m.frame.blocks label block hfb
    -- 4. Get typing for block body via weakening
    have hblock := hwt.blocks_typed block hmem envL (hlabel ▸ hlenv)
    have hwfL := hwt.lenv_wf label envL hlenv
    have hsite_empty := hwt.lenv_empty_siteEnv label envL hlenv
    have hstmt' := typecheck_stmt_weaken lenv envL env block.body retType
        hblock hsubsumes (hwt.lenv_funEnv_eq label envL hlenv) hwfL hwt.env_wf
        (fun s _ _ _ h => absurd h (by rw [hsite_empty s]; simp))
        (hwt.lenv_var_tracked label envL hlenv)
        (fun r => ⟨fun _ _ _ _ s _ _ _ h => by rw [hsite_empty s] at h; simp at h,
                   fun s _ _ _ _ _ _ h => by rw [hsite_empty s] at h; simp at h,
                   hwt.lenv_var_unique label envL hlenv r⟩)
        hwt.paths_to_non_member_empty
        hwt.paths_from_non_member_empty
        hwt.self_loop_only_empty
    -- 5. env.siteEnv is empty (from subsumes + lenv_empty_siteEnv)
    have hse : ∀ s, lookup env.siteEnv s = none :=
      siteEnv_empty_from_subsumes envL env hsubsumes
        (hwt.lenv_empty_siteEnv label envL hlenv)
    -- 6. Construct result
    refine ⟨env, lenv, retType, rmap, ?_, hss⟩
    exact {
      env_wf := hwt.env_wf
      stmt_typed := hstmt'
      var_consistent := hwt.var_consistent
      site_consistent := fun s τ h => by simp [hse s] at h
      rmap_live := hwt.rmap_live
      rmap_paths := hwt.rmap_paths
      blocks_typed := hwt.blocks_typed
      lenv_empty_siteEnv := hwt.lenv_empty_siteEnv
      lenv_wf := hwt.lenv_wf
      lenv_var_tracked := hwt.lenv_var_tracked
      lenv_var_unique := hwt.lenv_var_unique
      lenv_funEnv_eq := hwt.lenv_funEnv_eq
      funEnv_typed := hwt.funEnv_typed
      heap_loc_bound := hwt.heap_loc_bound
      varEnv_refs_in_pathEnv := hwt.varEnv_refs_in_pathEnv
      siteEnv_refs_in_pathEnv := fun s _ _ _ h => by simp [hse s] at h
      live_refs_unique := by
        intro r'
        exact ⟨fun _ _ _ _ s _ _ _ h => by simp [hse s] at h,
               fun s _ _ _ _ _ _ h => by simp [hse s] at h,
               (hwt.live_refs_unique r').2.2⟩
      rmap_root_none := hwt.rmap_root_none
      no_paths_to_root := hwt.no_paths_to_root
      root_path_coherence := hwt.root_path_coherence
      paths_from_non_member_empty := hwt.paths_from_non_member_empty
      paths_to_non_member_empty := hwt.paths_to_non_member_empty
      self_loop_only_empty := hwt.self_loop_only_empty
      rmap_has_type := by
        intro r bt loc path hrmap hcond
        apply hwt.rmap_has_type r bt loc path hrmap
        rcases hcond with ⟨x, bk, ms, hvar⟩ | ⟨s, bk, hsite⟩
        · exact Or.inl ⟨x, bk, ms, hvar⟩
        · simp [hse s] at hsite
    }

-- ============================================================
-- Part 8a-iv: Preservation for branch
-- ============================================================

private theorem preservation_branch (m m' : Machine) (env : TypeEnv) (lenv : LabelEnv)
    (retType : MoveType) (rmap : RefMap)
    (hwt : WellTypedState m env lenv retType rmap)
    (hss : StackSafe m.stack m.frame.returnInfo m.heap)
    (c : Site) (l1 l2 : Label)
    (hstmt : m.frame.stmt = .branch c l1 l2)
    (hstep : step (.running m) = .running m') :
    ∃ env' lenv' retType' rmap',
      WellTypedState m' env' lenv' retType' rmap' ∧
      StackSafe m'.stack m'.frame.returnInfo m'.heap := by
  -- 1. Extract typing info
  obtain ⟨envL1, envL2, hc_type, hl1, hl2, hs1, hs2⟩ :=
    inv_branch (by rw [← hstmt]; exact hwt.stmt_typed)
  -- 2. Get concrete bool value from site_consistent
  obtain ⟨v, hv_store, hv_match⟩ := hwt.site_consistent c (.basic .tbool) hc_type
  -- ValueMatchesType v (.basic .tbool) rmap = HasType v .tbool
  cases hv_match with
  | bool b =>
    -- 3. Set up env' = {env with siteEnv := delete env.siteEnv c}
    let env' : TypeEnv := {env with siteEnv := delete env.siteEnv c}
    -- env'.siteEnv is empty (from subsumes + lenv_empty_siteEnv)
    have hse' : ∀ s, lookup env'.siteEnv s = none :=
      siteEnv_empty_from_subsumes envL1 env' hs1
        (hwt.lenv_empty_siteEnv l1 envL1 hl1)
    -- env' is well-formed
    have hwf' : TypeEnv.WellFormed env' :=
      ⟨hwt.env_wf.pathEnv_wf,
       SiteEnv.delete_refs_not_root env.siteEnv c hwt.env_wf.siteEnv_wf,
       hwt.env_wf.varEnv_wf⟩
    -- readSite m c = some (.bool b)
    have hrs : readSite m c = some (.bool b) := hv_store
    -- 4. Case split on bool value and findBlock
    cases b with
    | true =>
      -- step uses l1
      simp only [step, hstmt, hrs] at hstep
      cases hfb : findBlock m.frame.blocks l1 with
      | none => exfalso; simp only [hfb] at hstep; contradiction
      | some block =>
        simp only [hfb, ExecState.running.injEq] at hstep; subst hstep
        obtain ⟨hmem, hlabel⟩ := findBlock_spec m.frame.blocks l1 block hfb
        -- Get typing via weakening
        have hblock := hwt.blocks_typed block hmem envL1 (hlabel ▸ hl1)
        have hwfL := hwt.lenv_wf l1 envL1 hl1
        have hsite_empty := hwt.lenv_empty_siteEnv l1 envL1 hl1
        have hstmt' := typecheck_stmt_weaken lenv envL1 env' block.body retType
            hblock hs1 (hwt.lenv_funEnv_eq l1 envL1 hl1) hwfL hwf'
            (fun s _ _ _ h => absurd h (by rw [hsite_empty s]; simp))
            (hwt.lenv_var_tracked l1 envL1 hl1)
            (fun r => ⟨fun _ _ _ _ s _ _ _ h => by rw [hsite_empty s] at h; simp at h,
                       fun s _ _ _ _ _ _ h => by rw [hsite_empty s] at h; simp at h,
                       hwt.lenv_var_unique l1 envL1 hl1 r⟩)
            hwt.paths_to_non_member_empty
            hwt.paths_from_non_member_empty
            hwt.self_loop_only_empty
        -- Construct result
        refine ⟨env', lenv, retType, rmap, ?_, hss⟩
        exact {
          env_wf := hwf'
          stmt_typed := hstmt'
          var_consistent := hwt.var_consistent
          site_consistent := fun s τ h => by simp [hse' s] at h
          rmap_live := hwt.rmap_live
          rmap_paths := hwt.rmap_paths
          blocks_typed := hwt.blocks_typed
          lenv_empty_siteEnv := hwt.lenv_empty_siteEnv
          lenv_wf := hwt.lenv_wf
          lenv_var_tracked := hwt.lenv_var_tracked
          lenv_var_unique := hwt.lenv_var_unique
          lenv_funEnv_eq := hwt.lenv_funEnv_eq
          funEnv_typed := hwt.funEnv_typed
          heap_loc_bound := hwt.heap_loc_bound
          varEnv_refs_in_pathEnv := hwt.varEnv_refs_in_pathEnv
          siteEnv_refs_in_pathEnv := fun s _ _ _ h => by simp [hse' s] at h
          live_refs_unique := by
            intro r'
            exact ⟨fun _ _ _ _ s _ _ _ h => by simp [hse' s] at h,
                   fun s _ _ _ _ _ _ h => by simp [hse' s] at h,
                   (hwt.live_refs_unique r').2.2⟩
          rmap_root_none := hwt.rmap_root_none
          no_paths_to_root := hwt.no_paths_to_root
          root_path_coherence := hwt.root_path_coherence
          paths_from_non_member_empty := hwt.paths_from_non_member_empty
          paths_to_non_member_empty := hwt.paths_to_non_member_empty
          self_loop_only_empty := hwt.self_loop_only_empty
          rmap_has_type := by
            intro r bt loc path hrmap hcond
            apply hwt.rmap_has_type r bt loc path hrmap
            rcases hcond with ⟨x, bk, ms, hvar⟩ | ⟨s, bk, hsite⟩
            · exact Or.inl ⟨x, bk, ms, hvar⟩
            · simp [hse' s] at hsite
        }
    | false =>
      -- step uses l2
      simp only [step, hstmt, hrs] at hstep
      cases hfb : findBlock m.frame.blocks l2 with
      | none => exfalso; simp only [hfb] at hstep; contradiction
      | some block =>
        simp only [hfb, ExecState.running.injEq] at hstep; subst hstep
        obtain ⟨hmem, hlabel⟩ := findBlock_spec m.frame.blocks l2 block hfb
        -- Get typing via weakening
        have hblock := hwt.blocks_typed block hmem envL2 (hlabel ▸ hl2)
        have hwfL := hwt.lenv_wf l2 envL2 hl2
        have hsite_empty := hwt.lenv_empty_siteEnv l2 envL2 hl2
        have hstmt' := typecheck_stmt_weaken lenv envL2 env' block.body retType
            hblock hs2 (hwt.lenv_funEnv_eq l2 envL2 hl2) hwfL hwf'
            (fun s _ _ _ h => absurd h (by rw [hsite_empty s]; simp))
            (hwt.lenv_var_tracked l2 envL2 hl2)
            (fun r => ⟨fun _ _ _ _ s _ _ _ h => by rw [hsite_empty s] at h; simp at h,
                       fun s _ _ _ _ _ _ h => by rw [hsite_empty s] at h; simp at h,
                       hwt.lenv_var_unique l2 envL2 hl2 r⟩)
            hwt.paths_to_non_member_empty
            hwt.paths_from_non_member_empty
            hwt.self_loop_only_empty
        -- Construct result
        refine ⟨env', lenv, retType, rmap, ?_, hss⟩
        exact {
          env_wf := hwf'
          stmt_typed := hstmt'
          var_consistent := hwt.var_consistent
          site_consistent := fun s τ h => by simp [hse' s] at h
          rmap_live := hwt.rmap_live
          rmap_paths := hwt.rmap_paths
          blocks_typed := hwt.blocks_typed
          lenv_empty_siteEnv := hwt.lenv_empty_siteEnv
          lenv_wf := hwt.lenv_wf
          lenv_var_tracked := hwt.lenv_var_tracked
          lenv_var_unique := hwt.lenv_var_unique
          lenv_funEnv_eq := hwt.lenv_funEnv_eq
          funEnv_typed := hwt.funEnv_typed
          heap_loc_bound := hwt.heap_loc_bound
          varEnv_refs_in_pathEnv := hwt.varEnv_refs_in_pathEnv
          siteEnv_refs_in_pathEnv := fun s _ _ _ h => by simp [hse' s] at h
          live_refs_unique := by
            intro r'
            exact ⟨fun _ _ _ _ s _ _ _ h => by simp [hse' s] at h,
                   fun s _ _ _ _ _ _ h => by simp [hse' s] at h,
                   (hwt.live_refs_unique r').2.2⟩
          rmap_root_none := hwt.rmap_root_none
          no_paths_to_root := hwt.no_paths_to_root
          root_path_coherence := hwt.root_path_coherence
          paths_from_non_member_empty := hwt.paths_from_non_member_empty
          paths_to_non_member_empty := hwt.paths_to_non_member_empty
          self_loop_only_empty := hwt.self_loop_only_empty
          rmap_has_type := by
            intro r bt loc path hrmap hcond
            apply hwt.rmap_has_type r bt loc path hrmap
            rcases hcond with ⟨x, bk, ms, hvar⟩ | ⟨s, bk, hsite⟩
            · exact Or.inl ⟨x, bk, ms, hvar⟩
            · simp [hse' s] at hsite
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
      | borrowMut x => exact preservation_borrowMut m m' env lenv retType rmap hwt hss s x cont hstmt hstep
    | borrowField src bt field => exact preservation_borrowFieldImm m m' env lenv retType rmap hwt hss s src bt field cont hstmt hstep
    | borrowMutField src bt field => exact preservation_borrowMutField m m' env lenv retType rmap hwt hss s src bt field cont hstmt hstep
    | readRef src => exact preservation_readRef m m' env lenv retType rmap hwt hss s src cont hstmt hstep
    | freeze src => exact preservation_freeze m m' env lenv retType rmap hwt hss s src cont hstmt hstep
    | pack name fieldSites => exact preservation_pack m m' env lenv retType rmap hwt hss s name fieldSites cont hstmt hstep
    | binop op a b => exact preservation_binop m m' env lenv retType rmap hwt hss s op a b cont hstmt hstep
  | release site cont => exact preservation_release m m' env lenv retType rmap hwt hss site cont hstmt hstep
  | assign x site cont =>
    rcases inv_assign (by rw [← hstmt]; exact hwt.stmt_typed) with
      ⟨ax, τ, ms, r, hvar, ha_type, hnv, hfresh, hnotin, hcont⟩ | ⟨τ, τ', hvar, hsite, hcompat, hcont⟩
    · exact preservation_assign_valid m m' env lenv retType rmap hwt hss x site cont ax τ ms r
        hvar ha_type hnv hfresh hnotin hcont hstmt hstep
    · exact preservation_assign_invalid m m' env lenv retType rmap hwt hss x site cont τ τ'
        hvar hsite hcompat hcont hstmt hstep
  | writeRef dst val cont => exact preservation_writeRef m m' env lenv retType rmap hwt hss dst val cont hstmt hstep
  | unpack fields src cont => exact preservation_unpack m m' env lenv retType rmap hwt hss fields src cont hstmt hstep
  | jump label => exact preservation_jump m m' env lenv retType rmap hwt hss label hstmt hstep
  | branch c l1 l2 => exact preservation_branch m m' env lenv retType rmap hwt hss c l1 l2 hstmt hstep
  | ret sites => sorry
  | call results fname argSites cont => sorry



end LeanMove.Typing.TypeSoundness
