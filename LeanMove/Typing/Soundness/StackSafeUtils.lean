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
# StackSafe Maintenance Utilities

Contains lemmas for maintaining `StackSafe` and `WellTypedState` under heap operations
(alloc, writeRef). Also contains `wellTypedState_extend_result_sites` and related lemmas
for the call/ret preservation cases.
-/

namespace LeanMove.Typing.TypeSoundness

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Typing
open LeanMove.Semantics
open AssocMap

-- ============================================================
-- Part 1: Heap Operation Preservation Lemmas
-- ============================================================

/-- PathReflectedInHeap is preserved under heap.alloc -/
theorem pathReflectedInHeap_heap_alloc (rmap : RefMap) (heap : Heap) (v : Value)
    (r1 r2 : Aref) (p : List PathElement)
    (hrfl : PathReflectedInHeap rmap heap r1 r2 p)
    (hlive_r2 : ∀ loc path, rmap.map r2 = some (loc, path) → heap.readRef loc path ≠ none)
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
      have hloc2_lt := hlb loc2 (readRef_implies_read heap loc2 path2 (hlive_r2 loc2 path2 hr2))
      have hne : loc2 ≠ heap.nextLoc := by intro h; subst h; exact Nat.lt_irrefl _ hloc2_lt
      rw [heap_alloc_preserves_readRef heap v loc2 path2 hne]
      exact hread

/-- WellTypedState is preserved when only the heap grows by alloc (frame unchanged) -/
theorem wellTypedState_heap_alloc
    (frame : Frame) (stack : List Frame) (heap : Heap)
    (env : TypeEnv) (lenv : LabelEnv) (retTypes : List ParamType) (rmap : RefMap)
    (v : Value)
    (hwt : WellTypedState ⟨frame, stack, heap⟩ env lenv retTypes rmap) :
    WellTypedState ⟨frame, stack, (heap.alloc v).1⟩ env lenv retTypes rmap := by
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
      intro r loc path hr_tracked hrmap
      have hlive := hwt.rmap_live r loc path hr_tracked hrmap
      have hlt := hlb loc (readRef_implies_read heap loc path hlive)
      have hne : loc ≠ heap.nextLoc := by intro h; subst h; exact Nat.lt_irrefl _ hlt
      rw [heap_alloc_preserves_readRef heap v loc path hne]
      exact hlive
    rmap_paths := by
      intro r1 r2 hr1 hr2 p hp
      exact pathReflectedInHeap_heap_alloc rmap heap v r1 r2 p
        (hwt.rmap_paths r1 r2 hr1 hr2 p hp)
        (fun loc path hrmap => hwt.rmap_live r2 loc path hr2 hrmap) hlb
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
      -- Derive tracking from hcond (ref is in varEnv or siteEnv → tracked)
      have hr_tracked : r ∈ env.pathEnv.refs := by
        rcases hcond with ⟨x, bk, ms, hvar⟩ | ⟨s, bk, hsite⟩
        · exact hwt.varEnv_refs_in_pathEnv x bt r bk ms hvar
        · exact hwt.siteEnv_refs_in_pathEnv s bt r bk hsite
      have hlt := hlb loc (readRef_implies_read heap loc path (hwt.rmap_live r loc path hr_tracked hrmap))
      have hne : loc ≠ heap.nextLoc := by intro h; subst h; exact Nat.lt_irrefl _ hlt
      rw [heap_alloc_preserves_readRef heap v loc path hne]
      exact ⟨val, hread, hht⟩
    funEnv_sig_consistent := hwt.funEnv_sig_consistent
    refs_tracked_mapped := hwt.refs_tracked_mapped
    lenv_labels_in_blocks := hwt.lenv_labels_in_blocks
    has_return_info := hwt.has_return_info
    varStore_locs_bound := by
      intro y loc_y hvar
      have hlt := hwt.varStore_locs_bound y loc_y hvar
      show loc_y < (heap.alloc v).1.nextLoc
      simp only [Heap.alloc]
      exact Nat.lt_trans hlt (Nat.lt_succ_of_le (Nat.le_refl _))
    enum_mutable_no_extension := hwt.enum_mutable_no_extension
  }

/-- StackSafe is preserved under heap.alloc -/
theorem stackSafe_heap_alloc (globalEnumEnv : EnumEnv) (stack : List Frame) (ri : Option ReturnInfo)
    (heap : Heap) (v : Value) {calleeRetTypes : List ParamType}
    (hss : StackSafe globalEnumEnv stack ri heap calleeRetTypes)
    (hlb : ∀ loc, heap.read loc ≠ none → loc < heap.nextLoc) :
    StackSafe globalEnumEnv stack ri (heap.alloc v).1 calleeRetTypes := by
  cases stack with
  | nil => simp [StackSafe]
  | cons callerFrame rest =>
    cases ri with
    | none => simp [StackSafe]
    | some ri =>
      unfold StackSafe at hss ⊢
      obtain ⟨cE, cL, cR, cM, hfields, hrest⟩ := hss
      -- Extract enumEnv equality and TypeEnv.WellFormed separately
      have henum_eq : cE.enumEnv = globalEnumEnv := hfields.1
      have henv_wf : TypeEnv.WellFormed cE := hfields.2.1
      obtain ⟨hstmt, hblocks, hlenv_se, hlenv_wf, hlenv_vt,
        hlenv_vu, hlenv_fe, hlenv_lib, hhas_ri, hfe_typed, hve_refs, hse_refs, hlru, hrmap_root, hno_paths_root,
        hroot_coh, hpfnm, hptnm, hsle, hiso_unmapped, hrru, hrtm, hvar_con, hsite_con, hrmap_live, hrmap_paths_f,
        hhlb, hvlb, hrmap_ht, hfe_sig, htc⟩ := hfields.2.2
      refine ⟨cE, cL, cR, cM, ⟨henum_eq, henv_wf, hstmt, hblocks, hlenv_se, hlenv_wf, hlenv_vt,
        hlenv_vu, hlenv_fe, hlenv_lib, hhas_ri, hfe_typed, hve_refs, hse_refs, hlru, hrmap_root, hno_paths_root,
        hroot_coh, hpfnm, hptnm, hsle, hiso_unmapped, hrru, hrtm, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, htc⟩, ?_⟩
      · -- var_consistent
        intro x isv τ ms hvar
        have hold := hvar_con x isv τ ms hvar
        cases isv with
        | validVar =>
          obtain ⟨loc, val, hloc, hread, hmatch⟩ := hold
          have hlt := hlb loc (by rw [Heap.read] at hread ⊢; simp [hread])
          exact ⟨loc, val, hloc, by rw [heap_alloc_preserves_read heap v loc hlt]; exact hread, hmatch⟩
        | invalidVar => exact hold
      · -- site_consistent
        intro s τ hse hni
        exact hsite_con s τ hse hni
      · -- rmap_live
        intro r loc path hr_tracked hrmap
        have hlive := hrmap_live r loc path hr_tracked hrmap
        have hlt := hlb loc (readRef_implies_read heap loc path hlive)
        have hne : loc ≠ heap.nextLoc := by intro h; subst h; exact Nat.lt_irrefl _ hlt
        rw [heap_alloc_preserves_readRef heap v loc path hne]; exact hlive
      · -- rmap_paths
        intro r1 r2 hr1 hr2 p hp
        exact pathReflectedInHeap_heap_alloc cM heap v r1 r2 p
          (hrmap_paths_f r1 r2 hr1 hr2 p hp)
          (fun loc path hrmap => hrmap_live r2 loc path hr2 hrmap) hlb
      · -- heap_loc_bound
        exact heap_loc_bound_after_alloc heap v hlb
      · -- varStore_locs_bound
        intro y loc_y hvar
        have hlt := hvlb y loc_y hvar
        exact Nat.lt_trans hlt (by simp [Heap.alloc])
      · -- rmap_has_type
        intro r bt loc path hrmap hcond
        obtain ⟨val, hread, hht⟩ := hrmap_ht r bt loc path hrmap hcond
        -- Derive tracking for r from hcond (ref in varEnv or non-result siteEnv)
        have hr_tracked : r ∈ cE.pathEnv.refs := by
          rcases hcond with ⟨x, bk, ms, hvar⟩ | ⟨s, bk, hsite, _⟩
          · exact hve_refs x bt r bk ms hvar
          · exact hse_refs s bt r bk hsite
        have hlt := hlb loc (readRef_implies_read heap loc path (hrmap_live r loc path hr_tracked hrmap))
        have hne : loc ≠ heap.nextLoc := by intro h; subst h; exact Nat.lt_irrefl _ hlt
        rw [heap_alloc_preserves_readRef heap v loc path hne]; exact ⟨val, hread, hht⟩
      · -- funEnv_sig_consistent
        exact hfe_sig
      · exact stackSafe_heap_alloc globalEnumEnv rest callerFrame.returnInfo heap v hrest hlb

/-- StackSafe is preserved under heap.writeRef -/
theorem stackSafe_heap_writeRef
    (globalEnumEnv : EnumEnv)
    (stack : List Frame) (ri : Option ReturnInfo)
    (heap heap' : Heap) (loc : Loc) (wpath : List Field)
    (vval v_leaf : Value) (τ : BasicMoveType)
    {calleeRetTypes : List ParamType}
    (hss : StackSafe globalEnumEnv stack ri heap calleeRetTypes)
    (hwr : heap.writeRef loc wpath vval = some heap')
    (hv_leaf_read : heap.readRef loc wpath = some v_leaf)
    (hv_leaf_ht : HasType globalEnumEnv v_leaf τ)
    (hmval : HasType globalEnumEnv vval τ)
    (htransfer_read : ∀ (suffix : List Field), suffix ≠ [] →
      readPath v_leaf suffix ≠ none → readPath vval suffix ≠ none)
    (htransfer_type : ∀ (suffix : List Field), suffix ≠ [] →
      typeAtPathV globalEnumEnv vval τ suffix = typeAtPathV globalEnumEnv v_leaf τ suffix) :
    StackSafe globalEnumEnv stack ri heap' calleeRetTypes := by
  cases stack with
  | nil => simp [StackSafe]
  | cons callerFrame rest =>
    cases ri with
    | none => simp [StackSafe]
    | some ri =>
      unfold StackSafe at hss ⊢
      obtain ⟨cE, cL, cR, cM, hfields, hrest⟩ := hss
      -- Extract enumEnv equality and TypeEnv.WellFormed separately
      have henum_eq : cE.enumEnv = globalEnumEnv := hfields.1
      have henv_wf : TypeEnv.WellFormed cE := hfields.2.1
      obtain ⟨hstmt, hblocks, hlenv_se, hlenv_wf, hlenv_vt,
        hlenv_vu, hlenv_fe, hlenv_lib, hhas_ri, hfe_typed, hve_refs, hse_refs, hlru, hrmap_root, hno_paths_root,
        hroot_coh, hpfnm, hptnm, hsle, hiso_unmapped, hrru, hrtm, hvar_con, hsite_con, hrmap_live, hrmap_paths_f,
        hhlb, hvlb, hrmap_ht, hfe_sig, htc⟩ := hfields.2.2
      -- Instantiate enum hypotheses with cE.enumEnv via henum_eq
      have hv_leaf_ht_cE : HasType cE.enumEnv v_leaf τ := henum_eq ▸ hv_leaf_ht
      have hmval_cE : HasType cE.enumEnv vval τ := henum_eq ▸ hmval
      -- Extract base value and writePath facts for field maintenance
      have hv_leaf_read' := hv_leaf_read
      have hwr' := hwr
      simp only [Heap.readRef, bind, Option.bind] at hv_leaf_read'
      simp only [Heap.writeRef, bind, Option.bind] at hwr'
      cases hbase : heap.read loc with
      | none => simp [hbase] at hv_leaf_read'
      | some baseVal =>
        simp only [hbase] at hv_leaf_read' hwr'
        cases hwp : writePath baseVal wpath vval with
        | none => simp [hwp] at hwr'
        | some newRoot =>
          simp [hwp] at hwr'
          have hread_diff : ∀ loc', loc' ≠ loc → heap'.read loc' = heap.read loc' := by
            intro loc' hne; rw [← hwr']
            exact heap_write_preserves_read heap loc loc' newRoot (Ne.symm hne)
          have hread_loc : heap'.read loc = some newRoot := by
            rw [← hwr']; simp [Heap.write, Heap.read, lookup_insert_same]
          refine ⟨cE, cL, cR, cM, ⟨henum_eq, henv_wf, hstmt, hblocks, hlenv_se, hlenv_wf, hlenv_vt,
            hlenv_vu, hlenv_fe, hlenv_lib, hhas_ri, hfe_typed, hve_refs, hse_refs, hlru, hrmap_root, hno_paths_root,
            hroot_coh, hpfnm, hptnm, hsle, hiso_unmapped, hrru, hrtm, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, htc⟩, ?_⟩
          · -- var_consistent
            intro x isv τ_x ms hvar
            have hvc := hvar_con x isv τ_x ms hvar
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
                  exact writePath_preserves_HasType_generalV v_x wpath vval newRoot bt_x
                    hmatch_x hwp (by
                      intro bt_leaf htapV
                      obtain ⟨u, hru, hhu⟩ := HasType_typeAtPathV v_x bt_x wpath bt_leaf hmatch_x htapV
                      rw [hv_leaf_read'] at hru; simp only [Option.some.injEq] at hru; subst hru
                      exact HasType_transfer hhu hv_leaf_ht_cE hmval_cE)
                | ref bt_ref r_ref bk_ref =>
                  exfalso
                  dsimp only [ValueMatchesType] at hmatch_x
                  obtain ⟨loc', path', hveq, _⟩ := hmatch_x
                  rw [hveq] at hwp hv_leaf_read'
                  cases wpath with
                  | cons f rest => simp [writePath] at hwp
                  | nil =>
                    simp [readPath] at hv_leaf_read'; rw [← hv_leaf_read'] at hv_leaf_ht_cE
                    exact HasType_not_ref loc' path' τ hv_leaf_ht_cE
              · exact ⟨loc_x, v_x, hvarStore, by rw [hread_diff loc_x hloc]; exact hread_x, hmatch_x⟩
            | invalidVar => exact hvc
          · -- site_consistent
            exact hsite_con
          · -- rmap_live
            intro r' loc' path' hr'_tracked hrmap'
            have hlive := hrmap_live r' loc' path' hr'_tracked hrmap'
            by_cases hloc : loc = loc'
            · subst hloc
              exact heap_writeRef_preserves_readRef_same_loc heap loc wpath path' vval heap'
                hwr hlive (by
                  intro suffix hsuffix
                  cases suffix with
                  | nil => simp [readPath]
                  | cons sf srest =>
                    simp only [Heap.readRef, bind, Option.bind, hbase] at hlive
                    rw [← hsuffix, readPath_append] at hlive
                    simp only [hv_leaf_read', Option.bind] at hlive
                    exact htransfer_read (sf :: srest) (List.cons_ne_nil _ _) hlive)
            · simp only [Heap.readRef, bind, Option.bind] at hlive ⊢
              rw [hread_diff loc' (Ne.symm hloc)]
              exact hlive
          · -- rmap_paths
            intro r1 r2 hr1 hr2 p hp
            have hpih := hrmap_paths_f r1 r2 hr1 hr2 p hp
            unfold PathReflectedInHeap at hpih ⊢
            cases hrm1 : cM.map r1 with
            | none => simp [hrm1] at hpih ⊢
            | some p1 =>
              obtain ⟨loc1, path1⟩ := p1
              cases hrm2 : cM.map r2 with
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
                    hwr hne (by
                      intro suffix hsuffix
                      cases suffix with
                      | nil => simp [readPath]
                      | cons sf srest =>
                        -- rmap_paths suffix: need readPath transfer
                        -- path2 = wpath ++ sf :: srest, so suffix is non-empty
                        -- We don't have hlive unfolded here like in rmap_live case
                        -- but hne gives us readRef at path2 ≠ none
                        simp only [Heap.readRef, bind, Option.bind, hbase] at hne
                        rw [← hsuffix, readPath_append] at hne
                        cases hrl : readPath baseVal wpath with
                        | none => simp [hrl] at hv_leaf_read'
                        | some vl =>
                          simp only [hrl, Option.bind] at hne
                          have : vl = v_leaf := by
                            simp only [hrl, Option.some.injEq] at hv_leaf_read'; exact hv_leaf_read'
                          subst this
                          exact htransfer_read (sf :: srest) (List.cons_ne_nil _ _) hne)
                · simp only [Heap.readRef, bind, Option.bind] at hne ⊢
                  rw [hread_diff loc2 (Ne.symm hloc2)]
                  exact hne
          · -- heap_loc_bound
            exact heap_loc_bound_after_writeRef heap loc wpath vval heap' hhlb hwr
          · -- varStore_locs_bound
            intro y loc_y hvar
            have hlt := hvlb y loc_y hvar
            rw [writeRef_preserves_nextLoc heap loc wpath vval heap' hwr]; exact hlt
          · -- rmap_has_type
            intro r' bt loc' path' hrmap' hcond
            obtain ⟨v_old, hread_old, hht_old⟩ := hrmap_ht r' bt loc' path' hrmap' hcond
            by_cases hloc' : loc = loc'
            · subst hloc'
              simp only [Heap.readRef, bind, Option.bind, hbase] at hread_old
              obtain ⟨vnew, hread_vnew, hht_vnew⟩ := writePath_preserves_readPath_HasType
                baseVal wpath path' vval newRoot v_leaf v_old τ bt
                hwp hread_old hht_old hv_leaf_read' hv_leaf_ht_cE hmval_cE
                (fun suffix hne_suffix => henum_eq ▸ htransfer_type suffix hne_suffix)
              exact ⟨vnew, by simp [Heap.readRef, bind, Option.bind, hread_loc, hread_vnew], hht_vnew⟩
            · refine ⟨v_old, ?_, hht_old⟩
              simp only [Heap.readRef, bind, Option.bind] at hread_old ⊢
              rw [hread_diff loc' (Ne.symm hloc')]
              exact hread_old
          · -- funEnv_sig_consistent
            exact hfe_sig
          · exact stackSafe_heap_writeRef globalEnumEnv rest callerFrame.returnInfo heap heap' loc wpath
              vval v_leaf τ hrest hwr hv_leaf_read hv_leaf_ht hmval htransfer_read htransfer_type

-- ============================================================
-- Part 2: Helper Lemmas for preservation_ret
-- ============================================================

/-- If collectSiteValues succeeds and v ∈ vals, then v came from some site in the list -/
theorem collectSiteValues_mem (siteStore : SiteStore) (sites : List Site)
    (vals : List Value) (v : Value)
    (hcsv : collectSiteValues siteStore sites = some vals)
    (hv : v ∈ vals) :
    ∃ s ∈ sites, lookup siteStore s = some v := by
  induction sites generalizing vals with
  | nil => simp [collectSiteValues] at hcsv; subst hcsv; simp at hv
  | cons s ss ih =>
    simp [collectSiteValues, bind, Option.bind] at hcsv
    cases hlu : lookup siteStore s with
    | none => simp [hlu] at hcsv
    | some v_hd =>
      simp only [hlu] at hcsv
      cases hrest : collectSiteValues siteStore ss with
      | none => simp [hrest] at hcsv
      | some vs =>
        simp only [hrest] at hcsv
        simp only [Option.some.injEq] at hcsv; subst hcsv
        cases hv with
        | head => exact ⟨s, List.Mem.head _, hlu⟩
        | tail _ hv' =>
          obtain ⟨s', hs', hlu'⟩ := ih vs hrest hv'
          exact ⟨s', List.Mem.tail _ hs', hlu'⟩

/-- types_conform implies each site has a type in the siteEnv -/
theorem types_conform_site_has_type (siteEnv : SiteEnv) (sites : List Site)
    (retTypes : List ParamType) (s : Site)
    (htc : types_conform siteEnv sites retTypes)
    (hs : s ∈ sites) :
    ∃ τ, lookup siteEnv s = some τ := by
  induction sites generalizing retTypes with
  | nil => simp at hs
  | cons s' ss ih =>
    cases retTypes with
    | nil => simp [types_conform] at htc
    | cons pt pts =>
      simp only [types_conform] at htc
      cases hse : lookup siteEnv s' with
      | none => simp [hse] at htc
      | some τ =>
        simp only [hse] at htc
        cases hs with
        | head => exact ⟨τ, hse⟩
        | tail _ hs' =>
          have htc_tail : types_conform siteEnv ss pts := by
            revert htc; cases pt with
            | mk bt isRef =>
              cases isRef with
              | none =>
                cases τ with
                | basic _ => intro ⟨_, htc'⟩; exact htc'
                | ref _ _ _ => intro h; exact absurd h (by simp)
              | some _ =>
                cases τ with
                | basic _ => intro h; exact absurd h (by simp)
                | ref _ _ _ => intro ⟨_, _, htc'⟩; exact htc'
          exact ih pts htc_tail hs'

/-- A ref value cannot have a basic HasType -/
theorem HasType_not_ref_basic {enumEnv : EnumEnv} (loc : Loc) (path : List Field) (bt : BasicMoveType) :
    ¬HasType enumEnv (Value.ref loc path) bt := by
  intro h; cases h

/-- bindReturnValues preserves lookups for sites not in the result list -/
theorem bindReturnValues_preserves (siteStore : SiteStore) (sites : List Site)
    (vals : List Value) (newStore : SiteStore) (s : Site)
    (hbrv : bindReturnValues siteStore sites vals = some newStore)
    (hni : s ∉ sites) :
    lookup newStore s = lookup siteStore s := by
  induction sites generalizing vals siteStore with
  | nil =>
    cases vals with
    | nil => simp [bindReturnValues] at hbrv; subst hbrv; rfl
    | cons _ _ => simp [bindReturnValues] at hbrv
  | cons s' ss ih =>
    cases vals with
    | nil => simp [bindReturnValues] at hbrv
    | cons v vs =>
      simp [bindReturnValues] at hbrv
      have hne : s ≠ s' := fun h => hni (h ▸ List.Mem.head _)
      have hni' : s ∉ ss := fun h => hni (List.Mem.tail _ h)
      rw [ih (insert siteStore s' v) vs hbrv hni', lookup_insert_ne siteStore s' s v hne]

/-- Returned ref values from the callee are live in the heap.
    If .ref loc path ∈ vals (collected from callee's siteStore) and the callee
    is well-typed, then heap.readRef loc path ≠ none. -/
theorem returned_ref_is_live
    {enumEnv : EnumEnv}
    (siteEnv : SiteEnv) (siteStore : SiteStore) (rmap : RefMap) (heap : Heap)
    (sites : List Site) (retTypes : List ParamType) (vals : List Value)
    (loc : Loc) (path : List Field)
    {pe_refs : List Aref}
    (hcsv : collectSiteValues siteStore sites = some vals)
    (htc : types_conform siteEnv sites retTypes)
    (hsc : ∀ s τ, lookup siteEnv s = some τ →
      ∃ v, lookup siteStore s = some v ∧ ValueMatchesType enumEnv v τ rmap)
    (hse_refs : ∀ s bt r bk, lookup siteEnv s = some (.ref bt r bk) → r ∈ pe_refs)
    (hrl : ∀ r loc path, r ∈ pe_refs → rmap.map r = some (loc, path) → heap.readRef loc path ≠ none)
    (hv : Value.ref loc path ∈ vals) :
    heap.readRef loc path ≠ none := by
  obtain ⟨cs, hcs_mem, hlu⟩ := collectSiteValues_mem siteStore sites vals (.ref loc path) hcsv hv
  obtain ⟨τ, hτ⟩ := types_conform_site_has_type siteEnv sites retTypes cs htc hcs_mem
  obtain ⟨v', hlu', hvm⟩ := hsc cs τ hτ
  rw [hlu] at hlu'; simp at hlu'; subst hlu'
  cases τ with
  | basic bt => exact absurd hvm (HasType_not_ref_basic loc path bt)
  | ref bt r bk =>
    obtain ⟨loc', path', hveq, hrmap_eq⟩ := hvm
    simp at hveq; obtain ⟨rfl, rfl⟩ := hveq
    exact hrl r loc path (hse_refs cs bt r bk hτ) hrmap_eq

/-- Derive ReturnValsWellTyped from callee's typing info.
    Bridges callee's types_conform + site_consistent with caller's types_conform
    to show that returned values match caller's result site types. -/
theorem derive_returnValsWellTyped
    {enumEnv : EnumEnv}
    (calleeSiteEnv callerSiteEnv : SiteEnv)
    (calleeSites callerSites : List Site)
    (retTypes : List ParamType)
    (siteStore : SiteStore) (heap : Heap) (rmap : RefMap)
    (vals : List Value)
    (htc_callee : types_conform calleeSiteEnv calleeSites retTypes)
    (htc_caller : types_conform callerSiteEnv callerSites retTypes)
    (hcsv : collectSiteValues siteStore calleeSites = some vals)
    (hsc : ∀ s τ, lookup calleeSiteEnv s = some τ →
      ∃ v, lookup siteStore s = some v ∧ ValueMatchesType enumEnv v τ rmap)
    (hrt : ∀ r bt loc path, rmap.map r = some (loc, path) →
      (∃ s bk, lookup calleeSiteEnv s = some (.ref bt r bk)) →
      ∃ v, heap.readRef loc path = some v ∧ HasType enumEnv v bt) :
    ReturnValsWellTyped enumEnv vals callerSites callerSiteEnv heap := by
  induction retTypes generalizing calleeSites callerSites vals with
  | nil =>
    cases calleeSites with
    | cons _ _ => simp [types_conform] at htc_callee
    | nil =>
      cases callerSites with
      | cons _ _ => simp [types_conform] at htc_caller
      | nil =>
        simp [collectSiteValues] at hcsv; subst hcsv
        exact trivial
  | cons pt pts ih =>
    cases calleeSites with
    | nil => simp [types_conform] at htc_callee
    | cons s_ee ss_ee =>
      cases callerSites with
      | nil => simp [types_conform] at htc_caller
      | cons s_er ss_er =>
        -- Decompose collectSiteValues: vals = v_hd :: vals_tl
        simp [collectSiteValues, bind, Option.bind] at hcsv
        cases hlu_store : lookup siteStore s_ee with
        | none => simp [hlu_store] at hcsv
        | some v_hd =>
          simp only [hlu_store] at hcsv
          cases hcsv_rest : collectSiteValues siteStore ss_ee with
          | none => simp [hcsv_rest] at hcsv
          | some vals_tl =>
            simp only [hcsv_rest, Option.some.injEq] at hcsv; subst hcsv
            -- Decompose types_conform for callee
            simp only [types_conform] at htc_callee
            cases hlu_ee : lookup calleeSiteEnv s_ee with
            | none => simp [hlu_ee] at htc_callee
            | some τ_ee =>
              simp only [hlu_ee] at htc_callee
              -- Decompose types_conform for caller
              simp only [types_conform] at htc_caller
              cases hlu_er : lookup callerSiteEnv s_er with
              | none => simp [hlu_er] at htc_caller
              | some τ_er =>
                simp only [hlu_er] at htc_caller
                -- Get value from hsc
                obtain ⟨v_sc, hv_lu, hvm⟩ := hsc s_ee τ_ee hlu_ee
                rw [hlu_store] at hv_lu
                simp only [Option.some.injEq] at hv_lu; subst hv_lu
                -- hvm : ValueMatchesType v_hd τ_ee rmap
                -- Unfold ReturnValsWellTyped
                simp only [ReturnValsWellTyped, hlu_er]
                -- Case-split on pt to reduce types_conform matches
                revert htc_callee htc_caller
                obtain ⟨bt, isRef⟩ := pt
                cases isRef with
                | none =>
                  -- Basic parameter: ⟨bt, none⟩
                  cases τ_ee with
                  | basic bt_ee =>
                    cases τ_er with
                    | basic bt_er =>
                      intro ⟨hbt_ee, htc_callee_tail⟩ ⟨hbt_er, htc_caller_tail⟩
                      subst hbt_ee; subst hbt_er
                      -- hvm : HasType v_hd bt (ValueMatchesType for basic = HasType)
                      exact ⟨hvm, ih ss_ee ss_er vals_tl htc_callee_tail htc_caller_tail
                        hcsv_rest⟩
                    | ref _ _ _ => intro _ h; exact h.elim
                  | ref _ _ _ => intro h; exact h.elim
                | some _ =>
                  -- Ref parameter: ⟨bt, some isRefMut⟩
                  cases τ_ee with
                  | basic _ => intro h; exact h.elim
                  | ref bt_ee r_ee bk_ee =>
                    cases τ_er with
                    | basic _ => intro _ h; exact h.elim
                    | ref bt_er r_er bk_er =>
                      intro ⟨hbt_ee, _, htc_callee_tail⟩ ⟨hbt_er, _, htc_caller_tail⟩
                      subst hbt_ee; subst hbt_er
                      -- hvm : ValueMatchesType v_hd (.ref bt r_ee bk_ee) rmap
                      obtain ⟨loc, path, hveq, hrmap_ee⟩ := hvm
                      obtain ⟨v_target, hread, hhas_type⟩ :=
                        hrt r_ee bt loc path hrmap_ee ⟨s_ee, bk_ee, hlu_ee⟩
                      exact ⟨⟨loc, path, hveq, v_target, hread, hhas_type⟩,
                             ih ss_ee ss_er vals_tl htc_callee_tail htc_caller_tail
                               hcsv_rest⟩

/-- One-step reduction for extendWithReturns when site type is ref and value is ref -/
private theorem ewr_step_ref (rmap : RefMap) (siteEnv : SiteEnv)
    (s : Site) (ss : List Site) (bt : BasicMoveType) (r : Aref) (bk : BorrowingKind)
    (loc : Loc) (path : List Field) (vs : List Value)
    (hse : lookup siteEnv s = some (.ref bt r bk)) :
    RefMap.extendWithReturns rmap siteEnv (s :: ss) (Value.ref loc path :: vs) =
    RefMap.extendWithReturns ⟨fun r' => if r' = r then some (loc, path) else rmap.map r'⟩ siteEnv ss vs := by
  simp only [RefMap.extendWithReturns]
  rw [hse]

/-- If extendWithReturns creates a new mapping for ref r (r was unmapped in the original rmap),
    and ReturnValsWellTyped holds, then the heap has a readable well-typed value
    at the mapped location. Returns the base type from the siteEnv. -/
theorem extendWithReturns_new_mapping_type
    {enumEnv : EnumEnv}
    (rmap : RefMap) (siteEnv : SiteEnv)
    (sites : List Site) (vals : List Value) (heap : Heap)
    (r : Aref) (loc : Loc) (path : List Field)
    (hrmap : (RefMap.extendWithReturns rmap siteEnv sites vals).map r = some (loc, path))
    (hold : rmap.map r = none)
    (hrvt : ReturnValsWellTyped enumEnv vals sites siteEnv heap) :
    ∃ bt bk s, s ∈ sites ∧ lookup siteEnv s = some (.ref bt r bk) ∧
      ∃ v, heap.readRef loc path = some v ∧ HasType enumEnv v bt := by
  -- Prove a stronger version: either rmap already maps r, or some site provided the mapping
  suffices hsuf : ∀ (rmap : RefMap) (vals : List Value),
      (RefMap.extendWithReturns rmap siteEnv sites vals).map r = some (loc, path) →
      ReturnValsWellTyped enumEnv vals sites siteEnv heap →
      rmap.map r = some (loc, path) ∨
      ∃ bt bk s, s ∈ sites ∧ lookup siteEnv s = some (.ref bt r bk) ∧
        ∃ v, heap.readRef loc path = some v ∧ HasType enumEnv v bt by
    rcases hsuf rmap vals hrmap hrvt with h | h
    · rw [hold] at h; exact absurd h (by simp)
    · exact h
  clear rmap hold hrmap hrvt
  intro rmap vals hrmap hrvt
  induction sites generalizing vals rmap with
  | nil =>
    cases vals <;> (simp [RefMap.extendWithReturns] at hrmap; exact Or.inl hrmap)
  | cons s ss ih =>
    cases vals with
    | nil => simp [RefMap.extendWithReturns] at hrmap; exact Or.inl hrmap
    | cons v vs =>
      simp only [ReturnValsWellTyped] at hrvt
      cases hse_s : lookup siteEnv s with
      | none => simp only [hse_s] at hrvt; exact absurd hrvt.1 id
      | some τ =>
        simp only [hse_s] at hrvt
        cases τ with
        | basic _ =>
          exact (ih rmap vs (by
            revert hrmap; cases v <;> simp [RefMap.extendWithReturns, hse_s]) hrvt.2).elim
            Or.inl
            (fun ⟨bt, bk, s', hs', hse', hv⟩ =>
              Or.inr ⟨bt, bk, s', List.mem_cons_of_mem _ hs', hse', hv⟩)
        | ref bt_s r_s bk_s =>
          obtain ⟨loc_v, path_v, hveq, v', hread_v, htype_v⟩ := hrvt.1
          cases hv : v with
          | ref loc_v' path_v' =>
            subst hv; simp only [Value.ref.injEq] at hveq; obtain ⟨rfl, rfl⟩ := hveq
            rw [ewr_step_ref rmap siteEnv s ss bt_s r_s bk_s loc_v' path_v' vs hse_s] at hrmap
            exact (ih _ vs hrmap hrvt.2).elim
              (fun hold' => by
                by_cases hrr : r = r_s
                · subst hrr; simp at hold'; obtain ⟨rfl, rfl⟩ := hold'
                  exact Or.inr ⟨bt_s, bk_s, s, List.mem_cons_self .., hse_s, v', hread_v, htype_v⟩
                · have h : (⟨fun r' => if r' = r_s then some (loc_v', path_v') else rmap.map r'⟩ :
                      RefMap).map r = rmap.map r := by simp [hrr]
                  rw [h] at hold'; exact Or.inl hold')
              (fun ⟨bt, bk, s', hs', hse', hv'⟩ =>
                Or.inr ⟨bt, bk, s', List.mem_cons_of_mem _ hs', hse', hv'⟩)
          | int n => subst hv; exact Value.noConfusion hveq
          | bool b => subst hv; exact Value.noConfusion hveq
          | unit => subst hv; exact Value.noConfusion hveq
          | «record» fs => subst hv; exact Value.noConfusion hveq
          | vec _ => subst hv; exact Value.noConfusion hveq
          | variant _ _ _ => subst hv; exact Value.noConfusion hveq

/-- Monotonicity: if rmap already maps r, extendWithReturns still maps r. -/
theorem RefMap.extendWithReturns_ne_none (rmap : RefMap) (siteEnv : SiteEnv)
    (sites : List Site) (vals : List Value) (r : Aref)
    (h : rmap.map r ≠ none) :
    (RefMap.extendWithReturns rmap siteEnv sites vals).map r ≠ none := by
  induction sites generalizing vals rmap with
  | nil => cases vals <;> simp [RefMap.extendWithReturns, h]
  | cons s ss ih =>
    cases vals with
    | nil => simp [RefMap.extendWithReturns, h]
    | cons v vs =>
      simp only [RefMap.extendWithReturns]
      cases hse : lookup siteEnv s with
      | none => exact ih rmap vs h
      | some τ =>
        cases τ with
        | basic _ => exact ih rmap vs h
        | ref bt r' bk =>
          cases v with
          | ref loc path =>
            apply ih
            show (if r = r' then some (loc, path) else rmap.map r) ≠ none
            by_cases hrr : r = r'
            · simp [hrr]
            · simp [hrr]; exact h
          | int _ => exact ih rmap vs h
          | bool _ => exact ih rmap vs h
          | unit => exact ih rmap vs h
          | «record» _ => exact ih rmap vs h
          | vec _ => exact ih rmap vs h
          | variant _ _ _ => exact ih rmap vs h

/-- If a result site has a ref type mapping abstract ref r, and ReturnValsWellTyped holds,
    then extendWithReturns maps r (r is non-none in the result). -/
theorem RefMap.extendWithReturns_maps_result_ref
    {enumEnv : EnumEnv}
    (rmap : RefMap) (siteEnv : SiteEnv)
    (sites : List Site) (vals : List Value) (heap : Heap) (r : Aref)
    (hrvt : ReturnValsWellTyped enumEnv vals sites siteEnv heap)
    (s : Site) (bt : BasicMoveType) (bk : BorrowingKind)
    (hs : s ∈ sites) (hse : lookup siteEnv s = some (.ref bt r bk)) :
    (RefMap.extendWithReturns rmap siteEnv sites vals).map r ≠ none := by
  induction sites generalizing vals rmap with
  | nil => simp at hs
  | cons s' ss ih =>
    cases vals with
    | nil => simp [ReturnValsWellTyped] at hrvt
    | cons v' vs =>
      simp only [ReturnValsWellTyped] at hrvt
      simp only [RefMap.extendWithReturns]
      cases hse_s' : lookup siteEnv s' with
      | none =>
        simp only [hse_s'] at hrvt
        exact absurd hrvt.1 id
      | some τ' =>
        simp only [hse_s'] at hrvt
        rcases List.mem_cons.mp hs with rfl | hs_in_ss
        · -- s = s': this site maps r
          rw [hse] at hse_s'; cases hse_s'
          obtain ⟨loc, path, hveq, _⟩ := hrvt.1
          cases v' with
          | ref loc' path' =>
            -- After this step, intermediate rmap maps r → (loc', path')
            -- Use monotonicity to show it's preserved through remaining sites
            exact RefMap.extendWithReturns_ne_none _ siteEnv ss vs r (by simp)
          | int _ => simp at hveq
          | bool _ => simp at hveq
          | unit => simp at hveq
          | «record» _ => simp at hveq
          | vec _ => simp at hveq
          | variant _ _ _ => simp at hveq
        · -- s ∈ ss: recurse with IH
          cases τ' with
          | basic _ =>
            exact ih rmap vs hrvt.2 hs_in_ss
          | ref bt' r' bk' =>
            obtain ⟨loc', path', hveq', _⟩ := hrvt.1
            cases v' with
            | ref l p =>
              exact ih _ vs hrvt.2 hs_in_ss
            | int _ => simp at hveq'
            | bool _ => simp at hveq'
            | unit => simp at hveq'
            | «record» _ => simp at hveq'
            | vec _ => simp at hveq'
            | variant _ _ _ => simp at hveq'

/-- Result sites get the correct values after bindReturnValues + extendWithReturns.
    For each result site s with type τ in siteEnv, produces a value in newSiteStore
    that matches the type under the extended rmap. -/
theorem returnVals_site_consistent
    {enumEnv : EnumEnv}
    (rmap : RefMap) (siteStore : SiteStore) (siteEnv : SiteEnv)
    (sites : List Site) (vals : List Value) (heap : Heap) (newSiteStore : SiteStore)
    (hbrv : bindReturnValues siteStore sites vals = some newSiteStore)
    (hrvt : ReturnValsWellTyped enumEnv vals sites siteEnv heap)
    (huniq : ∀ s₁ ∈ sites, ∀ s₂ ∈ sites, s₁ ≠ s₂ →
      ∀ bt₁ bt₂ r bk₁ bk₂,
      lookup siteEnv s₁ = some (.ref bt₁ r bk₁) →
      lookup siteEnv s₂ = some (.ref bt₂ r bk₂) → False) :
    ∀ s ∈ sites, ∀ τ, lookup siteEnv s = some τ →
      ∃ v, lookup newSiteStore s = some v ∧
           ValueMatchesType enumEnv v τ (RefMap.extendWithReturns rmap siteEnv sites vals) := by
  induction sites generalizing vals rmap siteStore with
  | nil => intro s hs; simp at hs
  | cons s' ss ih =>
    cases vals with
    | nil => simp [bindReturnValues] at hbrv
    | cons v' vs =>
      simp only [bindReturnValues] at hbrv
      simp only [ReturnValsWellTyped] at hrvt
      have huniq' : ∀ s₁ ∈ ss, ∀ s₂ ∈ ss, s₁ ≠ s₂ → ∀ bt₁ bt₂ r bk₁ bk₂,
          lookup siteEnv s₁ = some (.ref bt₁ r bk₁) →
          lookup siteEnv s₂ = some (.ref bt₂ r bk₂) → False :=
        fun s₁ hs₁ s₂ hs₂ => huniq s₁ (List.mem_cons_of_mem _ hs₁) s₂ (List.mem_cons_of_mem _ hs₂)
      intro s hs τ hse
      -- If s ∈ ss, defer to IH (definitional equality handles rmap_step)
      by_cases hmem : s ∈ ss
      · -- s ∈ ss: use IH. The goal's extendWithReturns unfolds to rmap_step.extendWithReturns ss vs,
        -- which is exactly what the IH produces.
        cases hse_s' : lookup siteEnv s' with
        | none =>
          simp only [hse_s'] at hrvt
          exact ih _ _ vs hbrv hrvt.2 huniq' s hmem τ hse
        | some τ' =>
          simp only [hse_s'] at hrvt
          cases τ' with
          | basic _ => exact ih _ _ vs hbrv hrvt.2 huniq' s hmem τ hse
          | ref bt' r' bk' =>
            -- ReturnValsWellTyped forces v' to be a ref when site type is ref
            obtain ⟨loc', path', hveq', _, _, _⟩ := hrvt.1
            cases v' with
            | ref l p => exact ih _ _ vs hbrv hrvt.2 huniq' s hmem τ hse
            | int _ => simp at hveq'
            | bool _ => simp at hveq'
            | unit => simp at hveq'
            | «record» _ => simp at hveq'
            | vec _ => simp at hveq'
            | variant _ _ _ => simp at hveq'
      · -- s ∉ ss, so s = s'
        have hseq : s = s' := by
          rcases List.mem_cons.mp hs with h | h
          · exact h
          · exact absurd h hmem
        subst hseq
        -- lookup newSiteStore s = some v'
        have hlookup : lookup newSiteStore s = some v' := by
          rw [bindReturnValues_preserves (insert siteStore s v') ss vs newSiteStore s hbrv hmem]
          exact lookup_insert_same siteStore s v'
        -- Now prove ValueMatchesType
        cases hse_s : lookup siteEnv s with
        | none => rw [hse_s] at hse; simp at hse
        | some τ' =>
          have hτ_eq : τ' = τ := by rw [hse_s] at hse; simp at hse; exact hse
          subst hτ_eq
          simp only [hse_s] at hrvt
          cases τ' with
          | basic bt =>
            -- HasType v' bt from ReturnValsWellTyped, ValueMatchesType for basic is HasType
            exact ⟨v', hlookup, hrvt.1⟩
          | ref bt r_out bk =>
            -- ReturnValsWellTyped: ∃ loc path, v' = .ref loc path ∧ ∃ v'', ...
            obtain ⟨loc, pathf, hveq, _, _, _⟩ := hrvt.1
            refine ⟨v', hlookup, loc, pathf, hveq, ?_⟩
            -- Need rmap'.map r_out = some (loc, pathf)
            -- v' = .ref loc pathf, so we can cases on v'
            cases v' with
            | ref loc' path' =>
              simp only [Value.ref.injEq] at hveq
              obtain ⟨rfl, rfl⟩ := hveq
              -- extendWithReturns maps r_out to (loc', path') at this step
              rw [ewr_step_ref rmap siteEnv s ss bt r_out bk loc' path' vs hse_s]
              -- No other site in ss has ref r_out
              have hne_ss : ∀ s₂ ∈ ss, ∀ bt₂ r₂ bk₂,
                  lookup siteEnv s₂ = some (.ref bt₂ r₂ bk₂) → r₂ ≠ r_out := by
                intro s₂ hs₂ bt₂ r₂ bk₂ hse₂ hr₂eq; subst hr₂eq
                exact huniq s (List.mem_cons_self ..) s₂ (List.mem_cons_of_mem _ hs₂)
                  (fun h => hmem (h ▸ hs₂)) bt bt₂ r₂ bk bk₂ hse hse₂
              exact RefMap.extendWithReturns_preserves
                ⟨fun r' => if r' = r_out then some (loc', path') else rmap.map r'⟩
                siteEnv ss vs r_out (loc', path') (by simp) hne_ss
            | int _ => simp at hveq
            | bool _ => simp at hveq
            | unit => simp at hveq
            | «record» _ => simp at hveq
            | vec _ => simp at hveq
            | variant _ _ _ => simp at hveq

-- ============================================================
-- Part 5: StackSafe preservation through allocArgs
-- ============================================================

/-- StackSafe is preserved through allocArgs (a sequence of heap.alloc calls).
    By induction on the params/args list, using stackSafe_heap_alloc at each step. -/
theorem stackSafe_allocArgs (globalEnumEnv : EnumEnv) (stack : List Frame) (ri : Option ReturnInfo)
    (heap : Heap) (params : List (Var × MoveType)) (args : List Value)
    (heap' : Heap) (vs : VarStore) {calleeRetTypes : List ParamType}
    (hss : StackSafe globalEnumEnv stack ri heap calleeRetTypes)
    (hlb : ∀ loc, heap.read loc ≠ none → loc < heap.nextLoc)
    (halloc : allocArgs heap params args = some (heap', vs)) :
    StackSafe globalEnumEnv stack ri heap' calleeRetTypes := by
  induction params generalizing heap args heap' vs with
  | nil =>
    cases args with
    | nil =>
      have : heap' = heap := by
        simp only [allocArgs, Option.some.injEq, Prod.mk.injEq] at halloc
        exact halloc.1.symm
      rw [this]; exact hss
    | cons => simp [allocArgs] at halloc
  | cons p ps ih =>
    obtain ⟨y, τ_y⟩ := p
    cases args with
    | nil => simp [allocArgs] at halloc
    | cons a as' =>
      simp only [allocArgs, Bind.bind, Option.bind] at halloc
      cases hrec : allocArgs (heap.alloc a).1 ps as' with
      | none => rw [hrec] at halloc; simp at halloc
      | some pair =>
        obtain ⟨h'', vs''⟩ := pair
        rw [hrec] at halloc; dsimp at halloc
        simp only [Option.some.injEq, Prod.mk.injEq] at halloc
        rw [halloc.1.symm]
        exact ih (heap.alloc a).1 as' h'' vs''
          (stackSafe_heap_alloc globalEnumEnv stack ri heap a hss hlb)
          (heap_loc_bound_after_alloc heap a hlb)
          hrec

-- ============================================================
-- Part 6: init_fun_varEnv / addLocals lemmas
-- (shared between InitState.lean and Preservation.lean)
-- ============================================================

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
lemma init_fun_varEnv_valid_in_params (f : FunDef) (x : Var) (τ : MoveType) (ms : Mut) :
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
lemma init_fun_varEnv_valid_not_local (f : FunDef) (x : Var) (τ : MoveType) (ms : Mut) :
    lookup (init_fun_varEnv f) x = some (.validVar, τ, ms) →
    x ∉ f.locals.map (·.name) := by
  unfold init_fun_varEnv add_locals_to_varEnv
  intro h
  exact (add_locals_foldl_valid _ _ _ _ _ h).2

/-- If lookup in init_fun_varEnv gives .invalidVar, then x is a local name. -/
lemma init_fun_varEnv_invalid_is_local (f : FunDef) (x : Var) (τ : MoveType) (ms : Mut) :
    lookup (init_fun_varEnv f) x = some (.invalidVar, τ, ms) →
    x ∈ f.locals.map (·.name) := by
  unfold init_fun_varEnv add_locals_to_varEnv
  intro h
  by_contra habs
  rw [add_locals_foldl_preserves _ _ _ habs] at h
  have := init_varEnv_from_params_isValidVar f.params x .invalidVar τ ms h
  cases this  -- .invalidVar = .validVar is impossible

/-- addLocals preserves lookups for variables not in the locals list. -/
lemma addLocals_preserves_lookup (vs : VarStore) (locals : List LocalVar) (x : Var)
    (hx : x ∉ locals.map (·.name)) : lookup (addLocals vs locals) x = lookup vs x := by
  induction locals generalizing vs with
  | nil => rfl
  | cons lv rest ih =>
    simp only [List.map, List.mem_cons, not_or] at hx
    simp only [addLocals]
    rw [ih (insert vs lv.name none) hx.2, lookup_insert_ne _ _ _ _ hx.1]

/-- addLocals sets variables that appear in locals to none. -/
lemma addLocals_local_some_none (vs : VarStore) (locals : List LocalVar) (x : Var)
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

-- ============================================================
-- Part 7: Heap.alloc + allocArgs helper lemmas
-- (shared between InitState.lean and Preservation.lean)
-- ============================================================

lemma heap_alloc_nextLoc (h : Heap) (v : Value) :
    (h.alloc v).1.nextLoc = h.nextLoc + 1 := by
  simp [Heap.alloc]

lemma lt_heap_alloc_nextLoc (h : Heap) (v : Value) (n : ℕ) (hlt : n < h.nextLoc) :
    n < (h.alloc v).1.nextLoc :=
  Nat.lt_trans hlt (by simp [Heap.alloc])

lemma heap_alloc_read_same (h : Heap) (v : Value) :
    (h.alloc v).1.read h.nextLoc = some v := by
  simp [Heap.alloc, Heap.read, lookup_insert_same]

lemma heap_alloc_read_ne (h : Heap) (v : Value) (loc : Loc) (hne : loc ≠ h.nextLoc) :
    (h.alloc v).1.read loc = h.read loc := by
  simp only [Heap.alloc, Heap.read]
  exact lookup_insert_ne h.store h.nextLoc loc v hne

lemma heap_alloc_preserves_bound (h : Heap) (v : Value)
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
lemma allocArgs_preserves_old_read (heap : Heap) (params : List (Var × MoveType))
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
lemma allocArgs_heap_loc_bound' (heap : Heap) (params : List (Var × MoveType))
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

/-- allocArgs only grows the heap: nextLoc is non-decreasing. -/
lemma allocArgs_nextLoc_le (heap : Heap) (params : List (Var × MoveType))
    (args : List Value) (heap_out : Heap) (vs : VarStore) :
    allocArgs heap params args = some (heap_out, vs) →
    heap.nextLoc ≤ heap_out.nextLoc := by
  induction params generalizing heap args heap_out vs with
  | nil =>
    intro halloc
    cases args with
    | nil =>
      simp only [allocArgs, Option.some.injEq, Prod.mk.injEq] at halloc
      rw [halloc.1.symm]; exact Nat.le_refl _
    | cons => simp [allocArgs] at halloc
  | cons p ps ih =>
    intro halloc
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
        have h1 : heap.nextLoc ≤ (heap.alloc a).1.nextLoc := by simp [Heap.alloc]
        have h2 := ih (heap.alloc a).1 as' h' vs' hrec
        exact Nat.le_trans h1 h2

/-- All locations stored in paramVarStore by allocArgs are within heap bounds. -/
lemma allocArgs_varStore_locs_bound (heap : Heap) (params : List (Var × MoveType))
    (args : List Value) (heap_out : Heap) (vs : VarStore) :
    allocArgs heap params args = some (heap_out, vs) →
    ∀ y loc, lookup vs y = some (some loc) → loc < heap_out.nextLoc := by
  induction params generalizing heap args heap_out vs with
  | nil =>
    intro halloc y loc hlookup
    cases args with
    | nil =>
      simp [allocArgs] at halloc
      rw [show vs = empty from halloc.2.symm] at hlookup
      simp only [lookup, AssocMap.empty, List.lookup] at hlookup
      cases hlookup
    | cons => simp [allocArgs] at halloc
  | cons p ps ih =>
    intro halloc y loc hlookup
    obtain ⟨x, τ_x⟩ := p
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
        by_cases heq : y = x
        · subst heq; rw [lookup_insert_same] at hlookup
          simp only [Option.some.injEq] at hlookup; rw [← hlookup]
          -- loc = (heap.alloc a).2 = heap.nextLoc
          have : (heap.alloc a).2 = heap.nextLoc := by simp [Heap.alloc]
          rw [this]
          have h1 : heap.nextLoc < (heap.alloc a).1.nextLoc := by simp [Heap.alloc]
          exact Nat.lt_of_lt_of_le h1 (allocArgs_nextLoc_le _ _ _ _ _ hrec)
        · rw [lookup_insert_ne _ x y _ heq] at hlookup
          exact ih _ _ _ _ hrec y loc hlookup

/-- allocArgs succeeds only when params.length = args.length -/
lemma allocArgs_length_eq (heap : Heap) (params : List (Var × MoveType))
    (args : List Value) (heap_out : Heap) (vs : VarStore)
    (halloc : allocArgs heap params args = some (heap_out, vs)) :
    params.length = args.length := by
  induction params generalizing heap args heap_out vs with
  | nil =>
    cases args with
    | nil => rfl
    | cons _ _ => simp [allocArgs] at halloc
  | cons p ps ih =>
    obtain ⟨y, τ_y⟩ := p
    cases args with
    | nil => simp [allocArgs] at halloc
    | cons a as' =>
      simp only [allocArgs, Bind.bind, Option.bind] at halloc
      cases hrec : allocArgs (heap.alloc a).1 ps as' with
      | none => rw [hrec] at halloc; simp at halloc
      | some pair =>
        obtain ⟨h', vs'⟩ := pair
        exact congrArg Nat.succ (ih (heap.alloc a).1 as' h' vs' hrec)

/-- If a ∈ l₁ and l₁.length = l₂.length, then ∃ b, (a, b) ∈ l₁.zip l₂ -/
lemma exists_mem_zip_right {α β : Type} {l₁ : List α} {l₂ : List β}
    {a : α} (hlen : l₁.length = l₂.length) (hmem : a ∈ l₁) :
    ∃ b, (a, b) ∈ l₁.zip l₂ := by
  induction l₁ generalizing l₂ with
  | nil => simp at hmem
  | cons x xs ih =>
    cases l₂ with
    | nil => simp at hlen
    | cons y ys =>
      simp only [List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · exact ⟨y, by simp⟩
      · have ⟨b, hb⟩ := ih (Nat.succ.inj hlen) hmem
        exact ⟨b, List.mem_cons_of_mem _ hb⟩

/-- List.lookup succeeds when the key-value pair is in the list and keys are Nodup. -/
lemma list_lookup_of_mem_nodup {K V : Type} [BEq K] [LawfulBEq K]
    {l : List (K × V)} {k : K} {v : V}
    (hmem : (k, v) ∈ l) (hnodup : (l.map Prod.fst).Nodup) :
    l.lookup k = some v := by
  induction l with
  | nil => simp at hmem
  | cons hd tl ih =>
    simp only [List.map, List.nodup_cons] at hnodup
    obtain ⟨hnotin, hnodup_tl⟩ := hnodup
    simp only [List.mem_cons] at hmem
    rcases hmem with rfl | hmem
    · simp [List.lookup]
    · simp only [List.lookup]
      split
      · rename_i heq
        have hkeq : k = hd.1 := beq_iff_eq.mp heq
        have hk_in_tl : k ∈ tl.map Prod.fst := by
          rw [List.mem_map]; exact ⟨(k, v), hmem, rfl⟩
        exact absurd (hkeq ▸ hk_in_tl) hnotin
      · exact ih hmem hnodup_tl

/-- Ref keys from zip+filterMap form a sublist of ref keys from params-only filterMap. -/
lemma paramRefKeys_sublist (params : List (Var × MoveType)) (args : List Value) :
    List.Sublist
    ((params.zip args).filterMap (fun ((_, τ), v) =>
      match τ, v with
      | .ref _ r _, .ref _ _ => some r
      | _, _ => none))
    (params.filterMap (fun (_, τ) => match τ with
      | .ref _ r _ => some r
      | _ => none)) := by
  induction params generalizing args with
  | nil => exact List.Sublist.slnil
  | cons p ps ih =>
    obtain ⟨_, τ⟩ := p
    cases args with
    | nil => simp only [List.zip_nil_right, List.filterMap_nil]; exact List.nil_sublist _
    | cons a as' =>
      simp only [List.zip_cons_cons, List.filterMap_cons]
      cases τ with
      | basic _ => exact ih as'
      | ref bt r bk =>
        cases a with
        | ref _ _ => exact List.Sublist.cons₂ _ (ih as')
        | int _ => exact List.Sublist.cons _ (ih as')
        | bool _ => exact List.Sublist.cons _ (ih as')
        | unit => exact List.Sublist.cons _ (ih as')
        | record _ => exact List.Sublist.cons _ (ih as')
        | vec _ => exact List.Sublist.cons _ (ih as')
        | variant _ _ _ => exact List.Sublist.cons _ (ih as')

/-- allocArgs stores the exact argument value for each param/arg pair. -/
lemma allocArgs_param_stores_arg (heap : Heap) (params : List (Var × MoveType))
    (args : List Value) (heap_out : Heap) (vs : VarStore)
    (hlb : ∀ loc, heap.read loc ≠ none → loc < heap.nextLoc)
    (halloc : allocArgs heap params args = some (heap_out, vs))
    (hnodup : (params.map Prod.fst).Nodup) :
    ∀ x τ v, ((x, τ), v) ∈ (params.zip args) →
    ∃ loc, lookup vs x = some (some loc) ∧ heap_out.read loc = some v := by
  induction params generalizing heap args heap_out vs with
  | nil => intro x τ v hmem; simp at hmem
  | cons p ps ih =>
    intro x τ v hmem
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
        simp only [List.map, List.nodup_cons] at hnodup
        obtain ⟨hy_notin, hnodup_ps⟩ := hnodup
        simp only [List.zip_cons_cons, List.mem_cons, Prod.mk.injEq] at hmem
        rcases hmem with ⟨⟨rfl, rfl⟩, rfl⟩ | hmem_rest
        · -- head case: x = y, v = a (after rfl, a is replaced by v)
          refine ⟨(heap.alloc v).2, lookup_insert_same _ _ _, ?_⟩
          have hloc : (heap.alloc v).2 < (heap.alloc v).1.nextLoc := by
            simp [Heap.alloc]
          rw [allocArgs_preserves_old_read (heap.alloc v).1 ps as' h' vs' hrec
              (heap.alloc v).2 hloc]
          exact heap_alloc_read_same heap v
        · -- tail case
          have hx_in_ps : x ∈ ps.map Prod.fst := by
            rw [List.mem_map]
            exact ⟨(x, τ), (List.of_mem_zip hmem_rest).1, rfl⟩
          have heq : x ≠ y := fun h => hy_notin (h ▸ hx_in_ps)
          have ⟨loc, hlookup, hread⟩ := ih (heap.alloc a).1 as' h' vs'
            (heap_alloc_preserves_bound heap a hlb) hrec hnodup_ps x τ v hmem_rest
          exact ⟨loc, by rw [lookup_insert_ne _ _ _ _ heq]; exact hlookup, hread⟩

/-- If two params both contribute the same ref r to the filterMap, they must be the same param. -/
lemma nodup_filterMap_params_same_ref
    (params : List (Var × MoveType))
    (hnodup_names : (params.map Prod.fst).Nodup)
    (hnodup_refs : (params.filterMap (fun (_, τ) => match τ with
      | .ref _ r _ => some r | _ => none)).Nodup)
    {x y : Var} {bt bt' : BasicMoveType} {r : Aref} {bk bk' : BorrowingKind}
    (hpx : (x, MoveType.ref bt r bk) ∈ params)
    (hpy : (y, MoveType.ref bt' r bk') ∈ params) :
    x = y := by
  induction params with
  | nil => simp at hpx
  | cons hd tl ih =>
    simp only [List.map, List.nodup_cons] at hnodup_names
    obtain ⟨hnotin_names, hnodup_names_tl⟩ := hnodup_names
    obtain ⟨z, τ_z⟩ := hd
    simp only [List.mem_cons, Prod.mk.injEq] at hpx hpy
    have hnodup_refs_tl : (tl.filterMap (fun (_, τ) => match τ with
        | .ref _ r' _ => some r' | _ => none)).Nodup := by
      cases τ_z with
      | basic _ => simpa only [List.filterMap_cons] using hnodup_refs
      | ref _ _ _ => exact (List.nodup_cons.mp (by simpa only [List.filterMap_cons] using hnodup_refs)).2
    rcases hpx with ⟨rfl, rfl⟩ | hpx_tl
    · -- x is head
      rcases hpy with ⟨rfl, _⟩ | hpy_tl
      · rfl
      · -- y in tail with same r → r ∈ filterMap of tail, but head also contributes r → Nodup contradiction
        exfalso
        have : r ∈ tl.filterMap (fun (_, τ) => match τ with | .ref _ r' _ => some r' | _ => none) :=
          List.mem_filterMap.mpr ⟨(y, .ref bt' r bk'), hpy_tl, by simp⟩
        have := (List.nodup_cons.mp (by simpa only [List.filterMap_cons] using hnodup_refs)).1
        contradiction
    · rcases hpy with ⟨rfl, rfl⟩ | hpy_tl
      · -- y is head, x in tail
        exfalso
        have : r ∈ tl.filterMap (fun (_, τ) => match τ with | .ref _ r' _ => some r' | _ => none) :=
          List.mem_filterMap.mpr ⟨(x, .ref bt r bk), hpx_tl, by simp⟩
        have := (List.nodup_cons.mp (by simpa only [List.filterMap_cons] using hnodup_refs)).1
        contradiction
      · exact ih hnodup_names_tl hnodup_refs_tl hpx_tl hpy_tl

end LeanMove.Typing.TypeSoundness
