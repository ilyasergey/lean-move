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
    funEnv_sig_consistent := hwt.funEnv_sig_consistent
  }

/-- StackSafe is preserved under heap.alloc -/
theorem stackSafe_heap_alloc (stack : List Frame) (ri : Option ReturnInfo)
    (heap : Heap) (v : Value) {calleeRetTypes : List ParamType}
    (hss : StackSafe stack ri heap calleeRetTypes)
    (hlb : ∀ loc, heap.read loc ≠ none → loc < heap.nextLoc) :
    StackSafe stack ri (heap.alloc v).1 calleeRetTypes := by
  cases stack with
  | nil => simp [StackSafe]
  | cons callerFrame rest =>
    cases ri with
    | none => simp [StackSafe]
    | some ri =>
      unfold StackSafe at hss ⊢
      obtain ⟨cE, cL, cR, cM, hfields, hrest⟩ := hss
      -- Extract TypeEnv.WellFormed separately to avoid rcases auto-destructuring the structure
      have henv_wf : TypeEnv.WellFormed cE := hfields.1
      obtain ⟨hstmt, hblocks, hlenv_se, hlenv_wf, hlenv_vt,
        hlenv_vu, hlenv_fe, hfe_typed, hve_refs, hse_refs, hlru, hrmap_root, hno_paths_root,
        hroot_coh, hpfnm, hptnm, hsle, hiso_unmapped, hrru, hvar_con, hsite_con, hrmap_live, hrmap_paths_f,
        hhlb, hrmap_ht, hfe_sig, htc⟩ := hfields.2
      refine ⟨cE, cL, cR, cM, ⟨henv_wf, hstmt, hblocks, hlenv_se, hlenv_wf, hlenv_vt,
        hlenv_vu, hlenv_fe, hfe_typed, hve_refs, hse_refs, hlru, hrmap_root, hno_paths_root,
        hroot_coh, hpfnm, hptnm, hsle, hiso_unmapped, hrru, ?_, ?_, ?_, ?_, ?_, ?_, ?_, htc⟩, ?_⟩
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
        intro r loc path hrmap
        have hlive := hrmap_live r loc path hrmap
        have hlt := hlb loc (readRef_implies_read heap loc path hlive)
        have hne : loc ≠ heap.nextLoc := by intro h; subst h; exact Nat.lt_irrefl _ hlt
        rw [heap_alloc_preserves_readRef heap v loc path hne]; exact hlive
      · -- rmap_paths
        intro r1 r2 hr1 hr2 p hp
        exact pathReflectedInHeap_heap_alloc cM heap v r1 r2 p
          (hrmap_paths_f r1 r2 hr1 hr2 p hp) hrmap_live hlb
      · -- heap_loc_bound
        exact heap_loc_bound_after_alloc heap v hlb
      · -- rmap_has_type
        intro r bt loc path hrmap hcond
        obtain ⟨val, hread, hht⟩ := hrmap_ht r bt loc path hrmap hcond
        have hlt := hlb loc (readRef_implies_read heap loc path (hrmap_live r loc path hrmap))
        have hne : loc ≠ heap.nextLoc := by intro h; subst h; exact Nat.lt_irrefl _ hlt
        rw [heap_alloc_preserves_readRef heap v loc path hne]; exact ⟨val, hread, hht⟩
      · -- funEnv_sig_consistent
        exact hfe_sig
      · exact stackSafe_heap_alloc rest callerFrame.returnInfo heap v hrest hlb

/-- WellTypedState is preserved under heap.writeRef.
    The write at (loc, wpath) changes the root value at loc from baseVal to
    writePath baseVal wpath vval. All WellTypedState invariants are preserved because:
    - For locations ≠ loc: heap reads unchanged
    - For loc with basic-typed vars: writePath_preserves_HasType_general + HasType_transfer
    - For loc with ref-typed vars: impossible (ref can't coexist with writePath success)
    - For rmap_live/rmap_paths: heap_writeRef_preserves_readRef_same_loc + suffix transfer
    - For rmap_has_type: writePath_preserves_readPath_HasType -/
theorem wellTypedState_heap_writeRef
    (frame : Frame) (stack : List Frame) (heap heap' : Heap)
    (loc : Loc) (wpath : List Field) (vval v_leaf : Value) (τ : BasicMoveType)
    (env : TypeEnv) (lenv : LabelEnv) (retTypes : List ParamType) (rmap : RefMap)
    (hwt : WellTypedState ⟨frame, stack, heap⟩ env lenv retTypes rmap)
    (hwr : heap.writeRef loc wpath vval = some heap')
    (hv_leaf_read : heap.readRef loc wpath = some v_leaf)
    (hv_leaf_ht : HasType v_leaf τ)
    (hmval : HasType vval τ) :
    WellTypedState ⟨frame, stack, heap'⟩ env lenv retTypes rmap := by
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
        funEnv_sig_consistent := hwt.funEnv_sig_consistent
      }

/-- StackSafe is preserved under heap.writeRef -/
theorem stackSafe_heap_writeRef (stack : List Frame) (ri : Option ReturnInfo)
    (heap heap' : Heap) (loc : Loc) (wpath : List Field)
    (vval v_leaf : Value) (τ : BasicMoveType)
    {calleeRetTypes : List ParamType}
    (hss : StackSafe stack ri heap calleeRetTypes)
    (hwr : heap.writeRef loc wpath vval = some heap')
    (hv_leaf_read : heap.readRef loc wpath = some v_leaf)
    (hv_leaf_ht : HasType v_leaf τ)
    (hmval : HasType vval τ) :
    StackSafe stack ri heap' calleeRetTypes := by
  cases stack with
  | nil => simp [StackSafe]
  | cons callerFrame rest =>
    cases ri with
    | none => simp [StackSafe]
    | some ri =>
      unfold StackSafe at hss ⊢
      obtain ⟨cE, cL, cR, cM, hfields, hrest⟩ := hss
      -- Extract TypeEnv.WellFormed separately to avoid rcases auto-destructuring the structure
      have henv_wf : TypeEnv.WellFormed cE := hfields.1
      obtain ⟨hstmt, hblocks, hlenv_se, hlenv_wf, hlenv_vt,
        hlenv_vu, hlenv_fe, hfe_typed, hve_refs, hse_refs, hlru, hrmap_root, hno_paths_root,
        hroot_coh, hpfnm, hptnm, hsle, hiso_unmapped, hrru, hvar_con, hsite_con, hrmap_live, hrmap_paths_f,
        hhlb, hrmap_ht, hfe_sig, htc⟩ := hfields.2
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
          refine ⟨cE, cL, cR, cM, ⟨henv_wf, hstmt, hblocks, hlenv_se, hlenv_wf, hlenv_vt,
            hlenv_vu, hlenv_fe, hfe_typed, hve_refs, hse_refs, hlru, hrmap_root, hno_paths_root,
            hroot_coh, hpfnm, hptnm, hsle, hiso_unmapped, hrru, ?_, ?_, ?_, ?_, ?_, ?_, ?_, htc⟩, ?_⟩
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
                  exact writePath_preserves_HasType_general v_x wpath vval newRoot bt_x
                    hmatch_x hwp (by
                      intro bt_leaf htap
                      obtain ⟨bt', htap'⟩ := readPath_ne_none_implies_typeAtPath v_x bt_x
                        wpath hmatch_x (by rw [hv_leaf_read']; exact Option.some_ne_none _)
                      rw [htap'] at htap; simp only [Option.some.injEq] at htap; subst htap
                      obtain ⟨u, hru, hhu⟩ := HasType_typeAtPath v_x bt_x wpath bt' hmatch_x htap'
                      rw [hv_leaf_read'] at hru; simp only [Option.some.injEq] at hru; subst hru
                      exact HasType_transfer hhu hv_leaf_ht hmval)
                | ref bt_ref r_ref bk_ref =>
                  exfalso
                  dsimp only [ValueMatchesType] at hmatch_x
                  obtain ⟨loc', path', hveq, _⟩ := hmatch_x
                  rw [hveq] at hwp hv_leaf_read'
                  cases wpath with
                  | cons f rest => simp [writePath] at hwp
                  | nil =>
                    simp [readPath] at hv_leaf_read'; rw [← hv_leaf_read'] at hv_leaf_ht
                    exact HasType_not_ref loc' path' τ hv_leaf_ht
              · exact ⟨loc_x, v_x, hvarStore, by rw [hread_diff loc_x hloc]; exact hread_x, hmatch_x⟩
            | invalidVar => exact hvc
          · -- site_consistent
            exact hsite_con
          · -- rmap_live
            intro r' loc' path' hrmap'
            have hlive := hrmap_live r' loc' path' hrmap'
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
                    exact HasType_transfer_readPath_ne_none v_leaf vval τ
                      (sf :: srest) hv_leaf_ht hmval hlive)
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
                        simp only [Heap.readRef, bind, Option.bind, hbase] at hne
                        rw [← hsuffix, readPath_append] at hne
                        simp only [hv_leaf_read', Option.bind] at hne
                        exact HasType_transfer_readPath_ne_none v_leaf vval τ
                          (sf :: srest) hv_leaf_ht hmval hne)
                · simp only [Heap.readRef, bind, Option.bind] at hne ⊢
                  rw [hread_diff loc2 (Ne.symm hloc2)]
                  exact hne
          · -- heap_loc_bound
            exact heap_loc_bound_after_writeRef heap loc wpath vval heap' hhlb hwr
          · -- rmap_has_type
            intro r' bt loc' path' hrmap' hcond
            obtain ⟨v_old, hread_old, hht_old⟩ := hrmap_ht r' bt loc' path' hrmap' hcond
            by_cases hloc' : loc = loc'
            · subst hloc'
              simp only [Heap.readRef, bind, Option.bind, hbase] at hread_old
              obtain ⟨vnew, hread_vnew, hht_vnew⟩ := writePath_preserves_readPath_HasType
                baseVal wpath path' vval newRoot v_leaf v_old τ bt
                hwp hread_old hht_old hv_leaf_read' hv_leaf_ht hmval
              exact ⟨vnew, by simp [Heap.readRef, bind, Option.bind, hread_loc, hread_vnew], hht_vnew⟩
            · refine ⟨v_old, ?_, hht_old⟩
              simp only [Heap.readRef, bind, Option.bind] at hread_old ⊢
              rw [hread_diff loc' (Ne.symm hloc')]
              exact hread_old
          · -- funEnv_sig_consistent
            exact hfe_sig
          · exact stackSafe_heap_writeRef rest callerFrame.returnInfo heap heap' loc wpath
              vval v_leaf τ hrest hwr hv_leaf_read hv_leaf_ht hmval

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
theorem HasType_not_ref_basic (loc : Loc) (path : List Field) (bt : BasicMoveType) :
    ¬HasType (.ref loc path) bt := by
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
    (siteEnv : SiteEnv) (siteStore : SiteStore) (rmap : RefMap) (heap : Heap)
    (sites : List Site) (retTypes : List ParamType) (vals : List Value)
    (loc : Loc) (path : List Field)
    (hcsv : collectSiteValues siteStore sites = some vals)
    (htc : types_conform siteEnv sites retTypes)
    (hsc : ∀ s τ, lookup siteEnv s = some τ →
      ∃ v, lookup siteStore s = some v ∧ ValueMatchesType v τ rmap)
    (hrl : ∀ r loc path, rmap.map r = some (loc, path) → heap.readRef loc path ≠ none)
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
    exact hrl r loc path hrmap_eq

/-- Derive ReturnValsWellTyped from callee's typing info.
    Bridges callee's types_conform + site_consistent with caller's types_conform
    to show that returned values match caller's result site types. -/
theorem derive_returnValsWellTyped
    (calleeSiteEnv callerSiteEnv : SiteEnv)
    (calleeSites callerSites : List Site)
    (retTypes : List ParamType)
    (siteStore : SiteStore) (heap : Heap) (rmap : RefMap)
    (vals : List Value)
    (htc_callee : types_conform calleeSiteEnv calleeSites retTypes)
    (htc_caller : types_conform callerSiteEnv callerSites retTypes)
    (hcsv : collectSiteValues siteStore calleeSites = some vals)
    (hsc : ∀ s τ, lookup calleeSiteEnv s = some τ →
      ∃ v, lookup siteStore s = some v ∧ ValueMatchesType v τ rmap)
    (hrt : ∀ r bt loc path, rmap.map r = some (loc, path) →
      (∃ s bk, lookup calleeSiteEnv s = some (.ref bt r bk)) →
      ∃ v, heap.readRef loc path = some v ∧ HasType v bt) :
    ReturnValsWellTyped vals callerSites callerSiteEnv heap := by
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
    (rmap : RefMap) (siteEnv : SiteEnv)
    (sites : List Site) (vals : List Value) (heap : Heap)
    (r : Aref) (loc : Loc) (path : List Field)
    (hrmap : (RefMap.extendWithReturns rmap siteEnv sites vals).map r = some (loc, path))
    (hold : rmap.map r = none)
    (hrvt : ReturnValsWellTyped vals sites siteEnv heap) :
    ∃ bt bk s, s ∈ sites ∧ lookup siteEnv s = some (.ref bt r bk) ∧
      ∃ v, heap.readRef loc path = some v ∧ HasType v bt := by
  -- Prove a stronger version: either rmap already maps r, or some site provided the mapping
  suffices hsuf : ∀ (rmap : RefMap) (vals : List Value),
      (RefMap.extendWithReturns rmap siteEnv sites vals).map r = some (loc, path) →
      ReturnValsWellTyped vals sites siteEnv heap →
      rmap.map r = some (loc, path) ∨
      ∃ bt bk s, s ∈ sites ∧ lookup siteEnv s = some (.ref bt r bk) ∧
        ∃ v, heap.readRef loc path = some v ∧ HasType v bt by
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

/-- Result sites get the correct values after bindReturnValues + extendWithReturns.
    For each result site s with type τ in siteEnv, produces a value in newSiteStore
    that matches the type under the extended rmap. -/
theorem returnVals_site_consistent
    (rmap : RefMap) (siteStore : SiteStore) (siteEnv : SiteEnv)
    (sites : List Site) (vals : List Value) (heap : Heap) (newSiteStore : SiteStore)
    (hbrv : bindReturnValues siteStore sites vals = some newSiteStore)
    (hrvt : ReturnValsWellTyped vals sites siteEnv heap)
    (huniq : ∀ s₁ ∈ sites, ∀ s₂ ∈ sites, s₁ ≠ s₂ →
      ∀ bt₁ bt₂ r bk₁ bk₂,
      lookup siteEnv s₁ = some (.ref bt₁ r bk₁) →
      lookup siteEnv s₂ = some (.ref bt₂ r bk₂) → False) :
    ∀ s ∈ sites, ∀ τ, lookup siteEnv s = some τ →
      ∃ v, lookup newSiteStore s = some v ∧
           ValueMatchesType v τ (RefMap.extendWithReturns rmap siteEnv sites vals) := by
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

-- ============================================================
-- Part 5: StackSafe preservation through allocArgs
-- ============================================================

/-- StackSafe is preserved through allocArgs (a sequence of heap.alloc calls).
    By induction on the params/args list, using stackSafe_heap_alloc at each step. -/
theorem stackSafe_allocArgs (stack : List Frame) (ri : Option ReturnInfo)
    (heap : Heap) (params : List (Var × MoveType)) (args : List Value)
    (heap' : Heap) (vs : VarStore) {calleeRetTypes : List ParamType}
    (hss : StackSafe stack ri heap calleeRetTypes)
    (hlb : ∀ loc, heap.read loc ≠ none → loc < heap.nextLoc)
    (halloc : allocArgs heap params args = some (heap', vs)) :
    StackSafe stack ri heap' calleeRetTypes := by
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
          (stackSafe_heap_alloc stack ri heap a hss hlb)
          (heap_loc_bound_after_alloc heap a hlb)
          hrec

end LeanMove.Typing.TypeSoundness
