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

import LeanMove.Typing.Soundness.StackSafeUtils
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
    (h : typecheck_stmt lenv env (.letBind s (.intLit n) cont) retTypes) :
    typecheck_stmt lenv {env with siteEnv := insert env.siteEnv s (.basic .u64)} cont retTypes :=
  match h with | .let_bind_intLit _ _ _ _ _ _ _ hc => hc

private theorem inv_release
    (h : typecheck_stmt lenv env (.release site cont) retTypes) :
    (∃ τ r isBor,
      lookup env.siteEnv site = some (.ref τ r isBor) ∧
      typecheck_stmt lenv
        {env with siteEnv := delete env.siteEnv site
                  pathEnv := delete_ref_node env.pathEnv r}
        cont retTypes) ∨
    (∃ bt,
      lookup env.siteEnv site = some (.basic bt) ∧
      typecheck_stmt lenv
        {env with siteEnv := delete env.siteEnv site}
        cont retTypes) :=
  match h with
  | .release _ _ _ τ r isBor _ _ hlookup hcont => .inl ⟨τ, r, isBor, hlookup, hcont⟩
  | .release_basic _ _ _ bt _ _ hlookup hcont => .inr ⟨bt, hlookup, hcont⟩

private theorem inv_binop
    (h : typecheck_stmt lenv env (.letBind c (.binop bop a b) cont) retTypes) :
    ∃ bt1 bt2 bt3,
      lookup env.siteEnv a = some (.basic bt1) ∧
      lookup env.siteEnv b = some (.basic bt2) ∧
      binop_type bop bt1 bt2 = some bt3 ∧
      typecheck_stmt lenv
        {env with siteEnv := insert (delete (delete env.siteEnv a) b) c (.basic bt3)}
        cont retTypes :=
  match h with
  | .let_bind_binop _ _ _ bt1 bt2 bt3 _ _ _ _ _ ha hb hbt _ hcont =>
    ⟨bt1, bt2, bt3, ha, hb, hbt, hcont⟩

private theorem inv_unop
    (h : typecheck_stmt lenv env (.letBind c (.unop uop a) cont) retTypes) :
    ∃ bt1 bt2,
      lookup env.siteEnv a = some (.basic bt1) ∧
      unop_type uop bt1 = some bt2 ∧
      typecheck_stmt lenv
        {env with siteEnv := insert (delete env.siteEnv a) c (.basic bt2)}
        cont retTypes :=
  match h with
  | .let_bind_unop _ _ _ bt1 bt2 _ _ _ _ ha huop _ hcont =>
    ⟨bt1, bt2, ha, huop, hcont⟩

private theorem inv_copy
    (h : typecheck_stmt lenv env (.letBind a (.usage (.copy x)) cont) retTypes) :
    (∃ bt ms,
      lookup env.varEnv x = some (.validVar, .basic bt, ms) ∧
      typecheck_stmt lenv
        {env with siteEnv := insert env.siteEnv a (.basic bt)}
        cont retTypes) ∨
    (∃ τ ms s t isBor,
      lookup env.varEnv x = some (.validVar, .ref τ s isBor, ms) ∧
      freshRefInEnv t env ∧
      typecheck_stmt lenv
        {env with siteEnv := insert env.siteEnv a (.ref τ t isBor)
                  pathEnv := update_with_epsilon t s env.pathEnv}
        cont retTypes) :=
  match h with
  | .let_bind_copy_val _ _ _ _ bt ms _ _ hlookup _ hcont =>
    .inl ⟨bt, ms, hlookup, hcont⟩
  | .let_bind_copy_ref _ _ _ _ τ ms s t isBor _ _ hlookup _ hfresh hcont =>
    .inr ⟨τ, ms, s, t, isBor, hlookup, hfresh, hcont⟩

private theorem inv_move
    (h : typecheck_stmt lenv env (.letBind a (.usage (.move x)) cont) retTypes) :
    ∃ τ ms,
      lookup env.varEnv x = some (.validVar, τ, ms) ∧
      typecheck_stmt lenv
        {env with varEnv := update env.varEnv x (.invalidVar, τ, ms)
                  siteEnv := insert env.siteEnv a τ}
        cont retTypes :=
  match h with
  | .let_bind_move _ _ _ _ τ ms _ _ hlookup _ _ hcont => ⟨τ, ms, hlookup, hcont⟩

private theorem inv_borrowImm
    (h : typecheck_stmt lenv env (.letBind a (.usage (.borrowImm x)) cont) retTypes) :
    ∃ τ ms r,
      lookup env.varEnv x = some (.validVar, .basic τ, ms) ∧
      freshRefInEnv r env ∧
      typecheck_stmt lenv
        {env with siteEnv := insert env.siteEnv a (.ref τ r .siteBorrowImm)
                  pathEnv := update_with_extension r .root [.root_to_var x]
                              (update_with_epsilon r r env.pathEnv)}
        cont retTypes :=
  match h with
  | .let_bind_borrowImm _ _ _ _ τ ms r _ _ hlookup _ hfresh hcont =>
    ⟨τ, ms, r, hlookup, hfresh, hcont⟩

private theorem inv_borrowMut
    (h : typecheck_stmt lenv env (.letBind a (.usage (.borrowMut x)) cont) retTypes) :
    ∃ τ ms r,
      lookup env.varEnv x = some (.validVar, .basic τ, ms) ∧
      freshRefInEnv r env ∧
      typecheck_stmt lenv
        {env with siteEnv := insert env.siteEnv a (.ref τ r .siteBorrowMut)
                  pathEnv := update_with_extension r .root [.root_to_var x]
                              (update_with_epsilon r r env.pathEnv)}
        cont retTypes :=
  match h with
  | .let_bind_borrowMut _ _ _ _ τ ms r _ _ _ hlookup _ hfresh hcont =>
    ⟨τ, ms, r, hlookup, hfresh, hcont⟩

private theorem inv_readRef
    (h : typecheck_stmt lenv env (.letBind c (.readRef src) cont) retTypes) :
    ∃ r τ isBor,
      lookup env.siteEnv src = some (.ref τ r isBor) ∧
      typecheck_stmt lenv
        {env with siteEnv := insert (delete env.siteEnv src) c (.basic τ)
                  pathEnv := delete_ref_node env.pathEnv r}
        cont retTypes :=
  match h with
  | .let_bind_readRef _ _ _ _ r τ isBor _ _ hlookup _ hcont => ⟨r, τ, isBor, hlookup, hcont⟩

private theorem inv_freeze
    (h : typecheck_stmt lenv env (.letBind c (.freeze src) cont) retTypes) :
    ∃ τ r r' isBor,
      lookup env.siteEnv src = some (.ref τ r isBor) ∧
      freshRefInEnv r' env ∧
      typecheck_stmt lenv
        {env with siteEnv := insert (delete env.siteEnv src) c (.ref τ r' .siteBorrowImm)
                  pathEnv := consume_ref_transfer env.pathEnv r r'}
        cont retTypes :=
  match h with
  | .let_bind_freeze _ _ _ _ τ r r' isBor _ _ hlookup _ hfresh hcont =>
    ⟨τ, r, r', isBor, hlookup, hfresh, hcont⟩

private theorem inv_pack
    (h : typecheck_stmt lenv env (.letBind b (.pack recName fieldSites) cont) retTypes) :
    ∃ fentries,
      (∀ f a, (f, a) ∈ fieldSites →
        ∃ bt, lookup env.siteEnv a = some (.basic bt) ∧ lookup fentries f = some bt) ∧
      (∀ f, lookup fentries f ≠ none → ∃ a, (f, a) ∈ fieldSites) ∧
      typecheck_stmt lenv
        {env with siteEnv := insert (deleteAll env.siteEnv (fieldSites.map Prod.snd)) b
                                (.basic (.trecord fentries))}
        cont retTypes :=
  match h with
  | .let_bind_pack _ _ _ _ _ fentries _ _ _ hfields hcomplete _ hcont =>
    ⟨fentries, hfields, hcomplete, hcont⟩

private theorem inv_borrowField
    (h : typecheck_stmt lenv env (.letBind af (.borrowField src bt field) cont) retTypes) :
    ∃ bt' isBor fentries s rf,
      lookup env.siteEnv src = some (.ref bt s isBor) ∧
      bt = .trecord fentries ∧
      lookup fentries field = some bt' ∧
      freshRefInEnv rf env ∧
      typecheck_stmt lenv
        {env with siteEnv := insert (delete env.siteEnv src) af (.ref bt' rf isBor)
                  pathEnv := update_with_extension rf s [.field field] env.pathEnv}
        cont retTypes :=
  match h with
  | .let_bind_borrowField _ _ _ _ _ _ bt' isBor fentries s rf _ _ hlookup hbt hf _ hfresh hcont =>
    ⟨bt', isBor, fentries, s, rf, hlookup, hbt, hf, hfresh, hcont⟩

private theorem inv_borrowMutField
    (h : typecheck_stmt lenv env (.letBind af (.borrowMutField src bt field) cont) retTypes) :
    ∃ btf fentries s rf,
      lookup env.siteEnv src = some (.ref bt s .siteBorrowMut) ∧
      bt = .trecord fentries ∧
      lookup fentries field = some btf ∧
      freshRefInEnv rf env ∧
      typecheck_stmt lenv
        {env with siteEnv := insert (delete env.siteEnv src) af (.ref btf rf .siteBorrowMut)
                  pathEnv := update_with_extension rf s [.field field] env.pathEnv}
        cont retTypes :=
  match h with
  | .let_bind_borrowMutField _ _ _ _ _ _ btf fentries s rf _ _ hlookup hbt hf _ hfresh hcont =>
    ⟨btf, fentries, s, rf, hlookup, hbt, hf, hfresh, hcont⟩

private theorem inv_writeRef
    (h : typecheck_stmt lenv env (.writeRef dst val cont) retTypes) :
    ∃ τ r,
      lookup env.siteEnv dst = some (.ref τ r .siteBorrowMut) ∧
      lookup env.siteEnv val = some (.basic τ) ∧
      check_outbound env.pathEnv r (fun re => only_matches_empty (simplify re)) ∧
      typecheck_stmt lenv
        {env with siteEnv := delete (delete env.siteEnv val) dst
                  pathEnv := garbage_collect env.pathEnv r}
        cont retTypes :=
  match h with
  | .write_ref _ _ _ _ τ r _ _ hdst hval hcheck hcont => ⟨τ, r, hdst, hval, hcheck, hcont⟩

private theorem inv_jump
    (h : typecheck_stmt lenv env (.jump L) retTypes) :
    ∃ envL, lookup lenv L = some envL ∧ TypeEnv.subsumes envL env :=
  match h with
  | .jump _ _ _ envL _ hlookup hsub => ⟨envL, hlookup, hsub⟩

private theorem inv_branch
    (h : typecheck_stmt lenv env (.branch c L1 L2) retTypes) :
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
    (h : typecheck_stmt lenv env (.ret sites) retTypes) :
    types_conform env.siteEnv sites retTypes ∧
    (∀ a ∈ sites, ∀ bt r bk, lookup env.siteEnv a = some (.ref bt r bk) →
      ∀ p, ¬interpret_regex (env.pathEnv.paths (.root, r)) p) ∧
    (∀ a ∈ sites, ∀ bt r, lookup env.siteEnv a = some (.ref bt r .siteBorrowMut) →
      ∀ b, b ∉ sites →
        ∀ bt' r' bk', lookup env.siteEnv b = some (.ref bt' r' bk') →
          ∀ p, interpret_regex (env.pathEnv.paths (r, r')) p → p = []) ∧
    (∀ a₁ ∈ sites, ∀ bt₁ r₁, lookup env.siteEnv a₁ = some (.ref bt₁ r₁ .siteBorrowMut) →
      ∀ a₂ ∈ sites, a₁ ≠ a₂ → ∀ bt₂ r₂ bk₂, lookup env.siteEnv a₂ = some (.ref bt₂ r₂ bk₂) →
        ∀ p, ¬interpret_regex (env.pathEnv.paths (r₂, r₁)) p) :=
  match h with
  | .ret _ _ _ _ htc hnlb hwrit hnoal => ⟨htc, hnlb, hwrit, hnoal⟩

private theorem inv_call
    (h : typecheck_stmt lenv env (.call results fname args cont) retTypes) :
    ∃ params rets outRefs env',
      lookup env.funEnv fname = some ⟨params, rets⟩ ∧
      types_conform env.siteEnv args params ∧
      all_fresh_sites env results ∧
      List.Nodup results ∧
      all_refs_fresh_in_env env outRefs ∧
      List.Nodup outRefs ∧
      populate_call_outputs env results rets outRefs = some env' ∧
      check_mutable_inputs_isolated env args ∧
      typecheck_stmt lenv
        (let env'' := call_connect_inputs_outputs env' results args
         {env'' with siteEnv := AssocMap.deleteAll env''.siteEnv args})
        cont retTypes :=
  match h with
  | .call _ _ _ _ _ params rets outRefs env' _ _ hfun htc hfs hnd_sites hfr hnd hpop hiso hcont =>
    ⟨params, rets, outRefs, env', hfun, htc, hfs, hnd_sites, hfr, hnd, hpop, hiso, hcont⟩

private theorem inv_unpack
    (h : typecheck_stmt lenv env (.unpack fields src cont) retTypes) :
    ∃ fentries,
      lookup env.siteEnv src = some (.basic (.trecord fentries)) ∧
      (∀ f a, (f, a) ∈ fields → AssocMap.notIn env.siteEnv a) ∧
      (∀ a₁ a₂, (∃ f₁ f₂, (f₁, a₁) ∈ fields ∧ (f₂, a₂) ∈ fields ∧ f₁ ≠ f₂) → a₁ ≠ a₂) ∧
      (∀ f a, (f, a) ∈ fields → ∃ bt, lookup fentries f = some bt) ∧
      typecheck_stmt lenv
        {env with siteEnv := addFieldSites fentries (delete env.siteEnv src) fields}
        cont retTypes :=
  match h with
  | .unpack _ _ _ _ fentries _ _ hlookup hfresh hdistinct hfields hcont =>
    ⟨fentries, hlookup, hfresh, hdistinct, hfields, hcont⟩

-- Enum operation inversions

private theorem inv_packVariant
    (h : typecheck_stmt lenv env (.letBind b (.packVariant enumName variantName fieldSites) cont) retTypes) :
    ∃ enumDef variantDef,
      notIn env.siteEnv b ∧
      AssocMap.lookup env.enumEnv enumName = some enumDef ∧
      AssocMap.lookup enumDef.variants variantName = some variantDef ∧
      (∀ f a, (f, a) ∈ fieldSites →
        ∃ bt, lookup env.siteEnv a = some (.basic bt) ∧ lookup variantDef.fields f = some bt) ∧
      (∀ f, lookup variantDef.fields f ≠ none → ∃ a, (f, a) ∈ fieldSites) ∧
      (∀ a₁ a₂, (∃ f₁ f₂, (f₁, a₁) ∈ fieldSites ∧ (f₂, a₂) ∈ fieldSites ∧ f₁ ≠ f₂) → a₁ ≠ a₂) ∧
      typecheck_stmt lenv
        {env with siteEnv := insert (deleteAll env.siteEnv (fieldSites.map Prod.snd)) b
                                (.basic (.tenum enumName))}
        cont retTypes :=
  match h with
  | .let_bind_packVariant _ _ _ _ _ _ enumDef variantDef _ _ hnotIn hlookup_enum hlookup_var hfields hcomplete hdistinct hcont =>
    ⟨enumDef, variantDef, hnotIn, hlookup_enum, hlookup_var, hfields, hcomplete, hdistinct, hcont⟩

private theorem inv_unpackVariant
    (h : typecheck_stmt lenv env (.unpackVariant variantName fields src cont) retTypes) :
    (∃ ename enumDef variantDef,
      lookup env.siteEnv src = some (.basic (.tenum ename)) ∧
      AssocMap.lookup env.enumEnv ename = some enumDef ∧
      AssocMap.lookup enumDef.variants variantName = some variantDef ∧
      (∀ f a, (f, a) ∈ fields → AssocMap.notIn env.siteEnv a) ∧
      (∀ a₁ a₂, (∃ f₁ f₂, (f₁, a₁) ∈ fields ∧ (f₂, a₂) ∈ fields ∧ f₁ ≠ f₂) → a₁ ≠ a₂) ∧
      (∀ f a, (f, a) ∈ fields → ∃ bt, lookup variantDef.fields f = some bt) ∧
      typecheck_stmt lenv
        {env with siteEnv := addFieldSites variantDef.fields (delete env.siteEnv src) fields}
        cont retTypes) ∨
    (∃ ename enumDef variantDef r bk,
      lookup env.siteEnv src = some (.ref (.tenum ename) r bk) ∧
      AssocMap.lookup env.enumEnv ename = some enumDef ∧
      AssocMap.lookup enumDef.variants variantName = some variantDef ∧
      (∀ f a, (f, a) ∈ fields → AssocMap.notIn env.siteEnv a) ∧
      (∀ a₁ a₂, (∃ f₁ f₂, (f₁, a₁) ∈ fields ∧ (f₂, a₂) ∈ fields ∧ f₁ ≠ f₂) → a₁ ≠ a₂) ∧
      (∀ f a, (f, a) ∈ fields → ∃ bt, lookup variantDef.fields f = some bt) ∧
      typecheck_stmt lenv
        (addRefFieldSites r bk variantDef.fields (MoveLight.qualifyField variantName) fields {env with siteEnv := delete env.siteEnv src})
        cont retTypes) := by
  cases h with
  | unpackVariant_rule _ _ _ _ ename enumDef variantDef _ _ hlookup hlookup_enum hlookup_var hfresh hdistinct hexist hcont =>
    exact .inl ⟨ename, enumDef, variantDef, hlookup, hlookup_enum, hlookup_var, hfresh, hdistinct, hexist, hcont⟩
  | unpackVariant_ref_rule _ _ _ _ ename enumDef variantDef r bk _ _ hlookup hlookup_enum hlookup_var hfresh hdistinct hexist hcont =>
    exact .inr ⟨ename, enumDef, variantDef, r, bk, hlookup, hlookup_enum, hlookup_var, hfresh, hdistinct, hexist, hcont⟩

private theorem inv_variantSwitch
    (h : typecheck_stmt lenv env (.variantSwitch src cases) retTypes) :
    ∃ ename enumDef r bk,
      lookup env.siteEnv src = some (.ref (.tenum ename) r bk) ∧
      AssocMap.lookup env.enumEnv ename = some enumDef ∧
      (∀ vname, AssocMap.lookup enumDef.variants vname ≠ none → ∃ label, (vname, label) ∈ cases) ∧
      (∀ vname label, (vname, label) ∈ cases →
         ∃ envL, AssocMap.lookup lenv label = some envL ∧
                 TypeEnv.subsumes envL
                   {env with siteEnv := delete env.siteEnv src
                             pathEnv := delete_ref_node env.pathEnv r}) :=
  match h with
  | .variantSwitch_rule _ _ _ _ ename enumDef r bk _ hlookup hlookup_enum hcoverage hcases =>
    ⟨ename, enumDef, r, bk, hlookup, hlookup_enum, hcoverage, hcases⟩

-- Vector operation inversions

private theorem inv_vecPack
    (h : typecheck_stmt lenv env (.letBind b (.vecPack T elems) cont) retTypes) :
    notIn env.siteEnv b ∧
    (∀ a, a ∈ elems → lookup env.siteEnv a = some (.basic T)) ∧
    List.Nodup elems ∧
    typecheck_stmt lenv
      {env with siteEnv := insert (deleteAll env.siteEnv elems) b (.basic (.tvec T))}
      cont retTypes :=
  match h with
  | .let_bind_vecPack _ _ _ _ _ _ _ hnotIn hforall hnodup hcont =>
    ⟨hnotIn, hforall, hnodup, hcont⟩

private theorem inv_vecUnpack
    (h : typecheck_stmt lenv env (.vecUnpack T results src cont) retTypes) :
    lookup env.siteEnv src = some (.basic (.tvec T)) ∧
    (∀ a, a ∈ results → notIn env.siteEnv a) ∧
    List.Nodup results ∧
    typecheck_stmt lenv
      {env with siteEnv := addVecSites T (delete env.siteEnv src) results}
      cont retTypes :=
  match h with
  | .vecUnpack_rule _ _ _ _ _ _ _ hlook hfresh hnodup hcont =>
    ⟨hlook, hfresh, hnodup, hcont⟩

private theorem inv_vecLen
    (h : typecheck_stmt lenv env (.letBind a (.vecLen src) cont) retTypes) :
    ∃ T r isBor,
      lookup env.siteEnv src = some (.ref (.tvec T) r isBor) ∧
      notIn env.siteEnv a ∧
      typecheck_stmt lenv
        {env with siteEnv := insert (delete env.siteEnv src) a (.basic .u64),
                  pathEnv := delete_ref_node env.pathEnv r}
        cont retTypes :=
  match h with
  | .let_bind_vecLen _ _ _ _ _ _ _ _ _ hlook hnotIn hcont =>
    ⟨_, _, _, hlook, hnotIn, hcont⟩

private theorem inv_vecImmBorrow
    (h : typecheck_stmt lenv env (.letBind a (.vecImmBorrow src idx) cont) retTypes) :
    ∃ T s rf isBor,
      lookup env.siteEnv src = some (.ref (.tvec T) s isBor) ∧
      lookup env.siteEnv idx = some (.basic .u64) ∧
      notIn env.siteEnv a ∧
      (isBor = .siteBorrowMut →
        check_outbound env.pathEnv s (fun re => only_matches_empty (simplify re))) ∧
      freshRefInEnv rf env ∧
      typecheck_stmt lenv
        {env with siteEnv := insert (delete (delete env.siteEnv src) idx) a (.ref T rf .siteBorrowImm),
                  pathEnv := update_with_extension rf s [.vecElem] env.pathEnv}
        cont retTypes :=
  match h with
  | .let_bind_vecImmBorrow _ _ _ _ _ _ _ _ _ _ _ hlook_src hlook_idx hnotIn houtbound hfresh hcont =>
    ⟨_, _, _, _, hlook_src, hlook_idx, hnotIn, houtbound, hfresh, hcont⟩

private theorem inv_vecMutBorrow
    (h : typecheck_stmt lenv env (.letBind a (.vecMutBorrow src idx) cont) retTypes) :
    ∃ T s rf,
      lookup env.siteEnv src = some (.ref (.tvec T) s .siteBorrowMut) ∧
      lookup env.siteEnv idx = some (.basic .u64) ∧
      notIn env.siteEnv a ∧
      check_outbound env.pathEnv s (fun re => only_matches_empty (simplify re)) ∧
      freshRefInEnv rf env ∧
      typecheck_stmt lenv
        {env with siteEnv := insert (delete (delete env.siteEnv src) idx) a (.ref T rf .siteBorrowMut),
                  pathEnv := update_with_extension rf s [.vecElem] env.pathEnv}
        cont retTypes :=
  match h with
  | .let_bind_vecMutBorrow _ _ _ _ _ _ _ _ _ _ hlook_src hlook_idx hnotIn houtbound hfresh hcont =>
    ⟨_, _, _, hlook_src, hlook_idx, hnotIn, houtbound, hfresh, hcont⟩

private theorem inv_vecPopBack
    (h : typecheck_stmt lenv env (.letBind a (.vecPopBack src) cont) retTypes) :
    ∃ T r,
      lookup env.siteEnv src = some (.ref (.tvec T) r .siteBorrowMut) ∧
      check_outbound env.pathEnv r (fun re => only_matches_empty (simplify re)) ∧
      notIn env.siteEnv a ∧
      typecheck_stmt lenv
        {env with siteEnv := insert (delete env.siteEnv src) a (.basic T),
                  pathEnv := garbage_collect env.pathEnv r}
        cont retTypes :=
  match h with
  | .let_bind_vecPopBack _ _ _ _ _ _ _ _ hlook houtbound hnotIn hcont =>
    ⟨_, _, hlook, houtbound, hnotIn, hcont⟩

private theorem inv_vecPushBack
    (h : typecheck_stmt lenv env (.vecPushBack refSite val cont) retTypes) :
    ∃ T r,
      lookup env.siteEnv refSite = some (.ref (.tvec T) r .siteBorrowMut) ∧
      lookup env.siteEnv val = some (.basic T) ∧
      check_outbound env.pathEnv r (fun re => only_matches_empty (simplify re)) ∧
      typecheck_stmt lenv
        {env with siteEnv := delete (delete env.siteEnv val) refSite,
                  pathEnv := garbage_collect env.pathEnv r}
        cont retTypes :=
  match h with
  | .vecPushBack_rule _ _ _ _ _ _ _ _ hlook_ref hlook_val houtbound hcont =>
    ⟨_, _, hlook_ref, hlook_val, houtbound, hcont⟩

private theorem inv_vecSwap
    (h : typecheck_stmt lenv env (.vecSwap refSite idx1 idx2 cont) retTypes) :
    ∃ T r,
      lookup env.siteEnv refSite = some (.ref (.tvec T) r .siteBorrowMut) ∧
      lookup env.siteEnv idx1 = some (.basic .u64) ∧
      lookup env.siteEnv idx2 = some (.basic .u64) ∧
      check_outbound env.pathEnv r (fun re => only_matches_empty (simplify re)) ∧
      typecheck_stmt lenv
        {env with siteEnv := delete (delete (delete env.siteEnv idx2) idx1) refSite,
                  pathEnv := garbage_collect env.pathEnv r}
        cont retTypes :=
  match h with
  | .vecSwap_rule _ _ _ _ _ _ _ _ _ hlook_ref hlook_idx1 hlook_idx2 houtbound hcont =>
    ⟨_, _, hlook_ref, hlook_idx1, hlook_idx2, houtbound, hcont⟩

private theorem inv_assign
    (h : typecheck_stmt lenv env (.assign x a cont) retTypes) :
    (∃ ax τ ms r,
      lookup env.varEnv x = some (.validVar, .basic τ, ms) ∧
      lookup env.siteEnv a = some (.basic τ) ∧
      freshRefInEnv r env ∧
      notIn env.siteEnv ax ∧
      typecheck_stmt lenv
        {env with siteEnv := delete (delete (insert env.siteEnv ax (.ref τ r .siteBorrowMut)) a) ax
                  pathEnv := garbage_collect (update_with_extension r .root [.root_to_var x]
                              (update_with_epsilon r r env.pathEnv)) r}
        cont retTypes) ∨
    (∃ τ_old r_old bk_old τ' ms,
      LE.le .mutable ms ∧
      lookup env.varEnv x = some (.validVar, .ref τ_old r_old bk_old, ms) ∧
      lookup env.siteEnv a = some τ' ∧
      typecheck_stmt lenv
        {env with varEnv := update env.varEnv x (.validVar, τ', ms)
                  siteEnv := delete env.siteEnv a
                  pathEnv := delete_ref_node env.pathEnv r_old}
        cont retTypes) ∨
    (∃ τ τ',
      lookup env.varEnv x = some (.invalidVar, τ, .mutable) ∧
      lookup env.siteEnv a = some τ' ∧
      MoveType.compatible τ τ' ∧
      typecheck_stmt lenv
        {env with varEnv := update env.varEnv x (.validVar, τ', .mutable)
                  siteEnv := delete env.siteEnv a}
        cont retTypes) ∨
    (∃ isv τ,
      lookup env.varEnv x = some (isv, .basic τ, .mutable) ∧
      lookup env.siteEnv a = some (.basic τ) ∧
      typecheck_stmt lenv
        {env with varEnv := update env.varEnv x (.validVar, .basic τ, .mutable)
                  siteEnv := delete env.siteEnv a}
        cont retTypes) :=
  match h with
  | .var_assign_valid _ _ _ _ ax τ ms r _ _ _ hlookup ha_type hnotin hfresh hcont =>
    .inl ⟨ax, τ, ms, r, hlookup, ha_type, hfresh, hnotin, hcont⟩
  | .var_assign_valid_ref _ _ _ _ τ_old r_old bk_old τ' ms _ _ hle hlookup_var hlookup_site hcont =>
    .inr (.inl ⟨τ_old, r_old, bk_old, τ', ms, hle, hlookup_var, hlookup_site, hcont⟩)
  | .var_assign_invalid _ _ _ _ τ τ' _ _ hlookup_var hlookup_site hcompat hcont =>
    .inr (.inr (.inl ⟨τ, τ', hlookup_var, hlookup_site, hcompat, hcont⟩))
  | .var_assign_overwrite_basic _ _ _ _ isv τ _ _ hlookup_var hlookup_site hcont =>
    .inr (.inr (.inr ⟨isv, τ, hlookup_var, hlookup_site, hcont⟩))

-- ============================================================
-- Part 8: Preservation — extracted case lemmas
-- ============================================================

/-- Reusable helper: inserting one site into siteStore preserves site_consistent
    for the new env where that site maps to a basic type matching the inserted value. -/
private theorem site_consistent_insert_basic (m : Machine) (env : TypeEnv)
    (rmap : RefMap) (s : Site) (v : Value) (τ : MoveType)
    (hwt_sc : ∀ s' τ', lookup env.siteEnv s' = some τ' →
        ∃ v, lookup m.frame.siteStore s' = some v ∧ ValueMatchesType env.enumEnv v τ' rmap)
    (hmatch : ValueMatchesType env.enumEnv v τ rmap) :
    ∀ s' τ', lookup (insert env.siteEnv s τ) s' = some τ' →
      ∃ v', lookup (insert m.frame.siteStore s v) s' = some v' ∧ ValueMatchesType env.enumEnv v' τ' rmap := by
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
    {m : Machine} {env : TypeEnv} {lenv : LabelEnv} {retTypes : List ParamType} {rmap : RefMap}
    (hwt : WellTypedState m env lenv retTypes rmap) (s : Site) (bt : BasicMoveType) :
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
    {m : Machine} {env : TypeEnv} {lenv : LabelEnv} {retTypes : List ParamType} {rmap : RefMap}
    (hwt : WellTypedState m env lenv retTypes rmap) (s : Site) (bt : BasicMoveType) :
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

/-- Helper: lookup on delete returns some → lookup on original returns some -/
private lemma lookup_delete_some' {K V : Type} [DecidableEq K] (m : AssocMap K V) (k k' : K) (v : V)
    (h : lookup (delete m k) k' = some v) : lookup m k' = some v := by
  by_cases heq : k' = k
  · subst heq; rw [lookup_delete_same] at h; cases h
  · rwa [lookup_delete_ne _ k k' heq] at h

/-- Helper: addFieldSites only adds .basic entries, so ref lookups pass through -/
private lemma addFieldSites_ref_lookup (fentries : AssocMap Field BasicMoveType)
    (se : AssocMap Site MoveType) (fields : List (Field × Site))
    (s : Site) (bt : BasicMoveType) (r : Aref)
    (h : lookup (addFieldSites fentries se fields) s = some (.ref bt r .siteBorrowMut)) :
    lookup se s = some (.ref bt r .siteBorrowMut) := by
  induction fields generalizing se with
  | nil => exact h
  | cons fld rest ih =>
    unfold addFieldSites at h
    simp only [List.foldl] at h
    cases hlook : AssocMap.lookup fentries fld.1 with
    | none =>
      simp only [hlook] at h
      exact ih se h
    | some bt' =>
      simp only [hlook] at h
      have h' := ih (insert se fld.2 (.basic bt')) h
      by_cases heq : s = fld.2
      · subst heq; simp [lookup_insert_same] at h'
      · rwa [lookup_insert_ne _ fld.2 s _ heq] at h'

/-- Helper: addVecSites only adds .basic entries, so ref lookups pass through -/
private lemma addVecSites_ref_lookup (T : BasicMoveType)
    (se : AssocMap Site MoveType) (sites : List Site)
    (s : Site) (bt : BasicMoveType) (r : Aref)
    (h : lookup (addVecSites T se sites) s = some (.ref bt r .siteBorrowMut)) :
    lookup se s = some (.ref bt r .siteBorrowMut) := by
  induction sites generalizing se with
  | nil => exact h
  | cons site rest ih =>
    have h' := ih (insert se site (.basic T)) h
    by_cases heq : s = site
    · subst heq; simp [lookup_insert_same] at h'
    · rwa [lookup_insert_ne _ site s _ heq] at h'

private theorem preservation_intLit (m m' : Machine) (env : TypeEnv) (lenv : LabelEnv)
    (retTypes : List ParamType) (rmap : RefMap)
    (hwt : WellTypedState m env lenv retTypes rmap)
    (hss : StackSafe env.enumEnv m.stack m.frame.returnInfo m.heap retTypes)
    (s : Site) (n : Nat) (cont : Stmt)
    (hstmt : m.frame.stmt = .letBind s (.intLit n) cont)
    (hstep : step (.running m) = .running m') :
    ∃ env' lenv' retTypes' rmap',
      env'.enumEnv = env.enumEnv ∧ WellTypedState m' env' lenv' retTypes' rmap' ∧
      StackSafe env.enumEnv m'.stack m'.frame.returnInfo m'.heap retTypes' := by
  simp only [step, hstmt, ExecState.running.injEq] at hstep; subst hstep
  have hcont := inv_intLit (by rw [← hstmt]; exact hwt.stmt_typed)
  refine ⟨{env with siteEnv := insert env.siteEnv s (.basic .u64)},
          lenv, retTypes, rmap, rfl, ?_, hss⟩
  exact {
    env_wf := TypeEnv.insert_siteEnv_wf env s (.basic .u64) hwt.env_wf trivial
    enumEnv_consistent := hwt.enumEnv_consistent
    enum_qualified_nodup := hwt.enum_qualified_nodup
    enum_names_nodup := hwt.enum_names_nodup
    enum_variant_nodup := hwt.enum_variant_nodup
    enum_fields_nodup := hwt.enum_fields_nodup
    defaultValues_typed := hwt.defaultValues_typed
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
    funEnv_sig_consistent := hwt.funEnv_sig_consistent
    refs_tracked_mapped := hwt.refs_tracked_mapped
    lenv_labels_in_blocks := hwt.lenv_labels_in_blocks
    has_return_info := hwt.has_return_info
    varStore_locs_bound := hwt.varStore_locs_bound
  }

private theorem preservation_copy_val (m m' : Machine) (env : TypeEnv) (lenv : LabelEnv)
    (retTypes : List ParamType) (rmap : RefMap)
    (hwt : WellTypedState m env lenv retTypes rmap)
    (hss : StackSafe env.enumEnv m.stack m.frame.returnInfo m.heap retTypes)
    (s : Site) (x : Var) (cont : Stmt) (bt : BasicMoveType) (ms : Mut)
    (hstmt : m.frame.stmt = .letBind s (.usage (.copy x)) cont)
    (hvar : lookup env.varEnv x = some (.validVar, .basic bt, ms))
    (hcont : typecheck_stmt lenv {env with siteEnv := insert env.siteEnv s (.basic bt)} cont retTypes)
    (hstep : step (.running m) = .running m') :
    ∃ env' lenv' retTypes' rmap',
      env'.enumEnv = env.enumEnv ∧ WellTypedState m' env' lenv' retTypes' rmap' ∧
      StackSafe env.enumEnv m'.stack m'.frame.returnInfo m'.heap retTypes' := by
  obtain ⟨loc, val, hloc, hread, hht_val⟩ := hwt.var_consistent x .validVar (.basic bt) ms hvar
  have hrv : readVar m x = some val := by unfold readVar; simp [hloc, hread]
  simp only [step, hstmt, hrv, ExecState.running.injEq] at hstep; subst hstep
  refine ⟨{env with siteEnv := insert env.siteEnv s (.basic bt)},
          lenv, retTypes, rmap, rfl, ?_, hss⟩
  exact {
    env_wf := TypeEnv.insert_siteEnv_wf env s (.basic bt) hwt.env_wf trivial
    enumEnv_consistent := hwt.enumEnv_consistent
    enum_qualified_nodup := hwt.enum_qualified_nodup
    enum_names_nodup := hwt.enum_names_nodup
    enum_variant_nodup := hwt.enum_variant_nodup
    enum_fields_nodup := hwt.enum_fields_nodup
    defaultValues_typed := hwt.defaultValues_typed
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
    funEnv_sig_consistent := hwt.funEnv_sig_consistent
    refs_tracked_mapped := hwt.refs_tracked_mapped
    lenv_labels_in_blocks := hwt.lenv_labels_in_blocks
    has_return_info := hwt.has_return_info
    varStore_locs_bound := hwt.varStore_locs_bound
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
    {m : Machine} {env : TypeEnv} {lenv : LabelEnv} {retTypes : List ParamType} {rmap : RefMap}
    (hwt : WellTypedState m env lenv retTypes rmap)
    (t : Aref) (loc_t : Loc) (path_t : List Field)
    (hfresh : freshRefInEnv t env) :
    let rmap' : RefMap := { map := fun r => if r = t then some (loc_t, path_t) else rmap.map r }
    ∀ y isv τ ms,
      lookup env.varEnv y = some (isv, τ, ms) →
      match isv with
      | .validVar =>
        ∃ loc v, lookup m.frame.varStore y = some (some loc) ∧
                 m.heap.read loc = some v ∧ ValueMatchesType env.enumEnv v τ rmap'
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
      · exact absurd hrt.symm (freshRefInEnv_ne_varEnv_ref t env y .validVar bt r_y bk ms hfresh hvy)
      · refine ⟨loc_v, path_v, hv_eq, ?_⟩
        show (if r_y = t then some (loc_t, path_t) else rmap.map r_y) = some (loc_v, path_v)
        rw [if_neg hrt]; exact hrmap_r

/-- When rmap is extended by a fresh ref t, site_consistent is preserved
    for old siteEnv entries (whose refs aren't t). -/
private lemma site_consistent_old_entry_extend_rmap
    {m : Machine} {env : TypeEnv} {lenv : LabelEnv} {retTypes : List ParamType} {rmap : RefMap}
    (hwt : WellTypedState m env lenv retTypes rmap)
    (t : Aref) (loc_t : Loc) (path_t : List Field)
    (hfresh : freshRefInEnv t env)
    (s' : Site) (τ' : MoveType) (hl : lookup env.siteEnv s' = some τ') :
    let rmap' : RefMap := { map := fun r => if r = t then some (loc_t, path_t) else rmap.map r }
    ∃ v', lookup m.frame.siteStore s' = some v' ∧ ValueMatchesType env.enumEnv v' τ' rmap' := by
  intro rmap'
  obtain ⟨v', hv', hm⟩ := hwt.site_consistent s' τ' hl
  refine ⟨v', hv', ?_⟩
  cases τ' with
  | basic _ => exact hm
  | ref bt r_s bk =>
    obtain ⟨loc_v, path_v, hv_eq', hrmap_r⟩ := hm
    by_cases hrt : r_s = t
    · exact absurd hrt.symm (freshRefInEnv_ne_siteEnv_ref t env s' bt r_s bk hfresh (hrt ▸ hl))
    · refine ⟨loc_v, path_v, hv_eq', ?_⟩
      show (if r_s = t then some (loc_t, path_t) else rmap.map r_s) = some (loc_v, path_v)
      rw [if_neg hrt]; exact hrmap_r

/-- When rmap is extended by a fresh ref t mapped to (loc_t, path_t),
    rmap_live is preserved if readRef at (loc_t, path_t) is live. -/
private lemma rmap_live_extend_fresh
    {m : Machine} {env : TypeEnv} {lenv : LabelEnv} {retTypes : List ParamType} {rmap : RefMap}
    (hwt : WellTypedState m env lenv retTypes rmap)
    (t : Aref) (loc_t : Loc) (path_t : List Field)
    (hlive_t : m.heap.readRef loc_t path_t ≠ none)
    {refs' : List Aref}
    (hrefs_sub : ∀ r, r ∈ refs' → r = t ∨ r ∈ env.pathEnv.refs) :
    let rmap' : RefMap := { map := fun r => if r = t then some (loc_t, path_t) else rmap.map r }
    ∀ r' loc path, r' ∈ refs' → rmap'.map r' = some (loc, path) → m.heap.readRef loc path ≠ none := by
  intro rmap' r' loc path hr_tracked hrmap_r'
  by_cases hrt : r' = t
  · subst hrt
    simp only [rmap', ite_true] at hrmap_r'
    have h := Option.some.inj hrmap_r'
    have ⟨h1, h2⟩ := Prod.mk.inj h
    subst h1; subst h2
    exact hlive_t
  · simp only [rmap', if_neg hrt] at hrmap_r'
    have hr_old : r' ∈ env.pathEnv.refs :=
      (hrefs_sub r' hr_tracked).resolve_left hrt
    exact hwt.rmap_live r' loc path hr_old hrmap_r'

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
    {m : Machine} {env : TypeEnv} {lenv : LabelEnv} {retTypes : List ParamType} {rmap : RefMap}
    (hwt : WellTypedState m env lenv retTypes rmap)
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
    (retTypes : List ParamType) (rmap : RefMap)
    (hwt : WellTypedState m env lenv retTypes rmap)
    (hss : StackSafe env.enumEnv m.stack m.frame.returnInfo m.heap retTypes)
    (s : Site) (x : Var) (cont : Stmt)
    (τ_ref : BasicMoveType) (ms : Mut) (s_orig t : Aref) (isBor : BorrowingKind)
    (hvar : lookup env.varEnv x = some (.validVar, .ref τ_ref s_orig isBor, ms))
    (hfresh_t : freshRefInEnv t env)
    (hcont : typecheck_stmt lenv
        {env with siteEnv := insert env.siteEnv s (.ref τ_ref t isBor)
                  pathEnv := update_with_epsilon t s_orig env.pathEnv}
        cont retTypes)
    (hstmt : m.frame.stmt = .letBind s (.usage (.copy x)) cont)
    (hstep : step (.running m) = .running m') :
    ∃ env' lenv' retTypes' rmap',
      env'.enumEnv = env.enumEnv ∧ WellTypedState m' env' lenv' retTypes' rmap' ∧
      StackSafe env.enumEnv m'.stack m'.frame.returnInfo m'.heap retTypes' := by
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
    freshRefInEnvBool_implies_freshRefBool t env ((freshRefInEnv_iff_freshRefInEnvBool t env).mp hfresh_t)
  have ht_not_root : t ≠ Aref.root := freshRef_not_root hwt.env_wf.pathEnv_wf t hfresh_t_pathEnv
  -- 6. Construct WellTypedState
  refine ⟨{env with siteEnv := insert env.siteEnv s (.ref τ_ref t isBor),
                     pathEnv := update_with_epsilon t s_orig env.pathEnv},
          lenv, retTypes, rmap', rfl, ?_, hss⟩
  exact {
    env_wf := by
      have hpe' := update_with_epsilon_wellformed t s_orig env.pathEnv hwt.env_wf.pathEnv_wf
        ht_not_root
      exact TypeEnv.insert_pathEnv_wf env s (.ref τ_ref t isBor) _ hwt.env_wf hpe' ht_not_root
    enumEnv_consistent := hwt.enumEnv_consistent
    enum_qualified_nodup := hwt.enum_qualified_nodup
    enum_names_nodup := hwt.enum_names_nodup
    enum_variant_nodup := hwt.enum_variant_nodup
    enum_fields_nodup := hwt.enum_fields_nodup
    defaultValues_typed := hwt.defaultValues_typed
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
    rmap_live :=
      have hs_in_refs : s_orig ∈ env.pathEnv.refs :=
        hwt.varEnv_refs_in_pathEnv x τ_ref s_orig isBor ms hvar
      rmap_live_extend_fresh hwt t loc' path
        (hwt.rmap_live s_orig loc' path hs_in_refs hrmap_s_orig)
        (by intro r hr
            simp only [update_with_epsilon, update_with_extension] at hr
            simp only [show ¬t ∈ env.pathEnv.refs from
              (freshRef_iff_freshRefBool t env.pathEnv).mpr hfresh_t_pathEnv,
              not_false_eq_true, ↓reduceIte] at hr
            simp only [List.mem_cons] at hr
            exact hr)
    rmap_paths :=
      have ht_fresh_pe : t ∉ env.pathEnv.refs :=
        (freshRef_iff_freshRefBool t env.pathEnv).mpr hfresh_t_pathEnv
      have hs_in_refs : s_orig ∈ env.pathEnv.refs :=
        hwt.varEnv_refs_in_pathEnv x τ_ref s_orig isBor ms hvar
      rmap_paths_update_with_epsilon rmap m.heap env.pathEnv t s_orig loc' path
        ht_fresh_pe hs_in_refs hrmap_s_orig
        (hwt.rmap_live s_orig loc' path hs_in_refs hrmap_s_orig)
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
    funEnv_sig_consistent := hwt.funEnv_sig_consistent
    refs_tracked_mapped := by
      intro ref href
      by_cases heq : ref = t
      · rw [heq]; right
        show (if t = t then some (loc', path) else rmap.map t) ≠ none
        simp
      · have href_old : ref ∈ env.pathEnv.refs := by
          simp only [update_with_epsilon, update_with_extension] at href
          have : t ∉ env.pathEnv.refs :=
            (freshRef_iff_freshRefBool t env.pathEnv).mpr hfresh_t_pathEnv
          simp only [this, not_false_eq_true, ↓reduceIte, List.mem_cons] at href
          exact href.resolve_left heq
        cases hwt.refs_tracked_mapped ref href_old with
        | inl h => exact Or.inl h
        | inr h =>
          right
          show (if ref = t then some (loc', path) else rmap.map ref) ≠ none
          simp [heq]; exact h
    lenv_labels_in_blocks := hwt.lenv_labels_in_blocks
    has_return_info := hwt.has_return_info
    varStore_locs_bound := hwt.varStore_locs_bound
  } -- end copy_ref

private theorem preservation_move (m m' : Machine) (env : TypeEnv) (lenv : LabelEnv)
    (retTypes : List ParamType) (rmap : RefMap)
    (hwt : WellTypedState m env lenv retTypes rmap)
    (hss : StackSafe env.enumEnv m.stack m.frame.returnInfo m.heap retTypes)
    (s : Site) (x : Var) (cont : Stmt)
    (hstmt : m.frame.stmt = .letBind s (.usage (.move x)) cont)
    (hstep : step (.running m) = .running m') :
    ∃ env' lenv' retTypes' rmap',
      env'.enumEnv = env.enumEnv ∧ WellTypedState m' env' lenv' retTypes' rmap' ∧
      StackSafe env.enumEnv m'.stack m'.frame.returnInfo m'.heap retTypes' := by
  obtain ⟨τ, ms, hvar, hcont⟩ := inv_move (by rw [← hstmt]; exact hwt.stmt_typed)
  obtain ⟨loc, val, hloc, hread, hmatch⟩ := hwt.var_consistent x .validVar τ ms hvar
  have hrv : readVar m x = some val := by unfold readVar; simp [hloc, hread]
  simp only [step, hstmt, hrv, ExecState.running.injEq] at hstep; subst hstep
  have hfresh : moveTypeRefNotRoot τ := hwt.env_wf.varEnv_wf x (.validVar, τ, ms) hvar
  refine ⟨{env with varEnv := update env.varEnv x (.invalidVar, τ, ms),
                     siteEnv := insert env.siteEnv s τ},
          lenv, retTypes, rmap, rfl, ?_, hss⟩
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
    enumEnv_consistent := hwt.enumEnv_consistent
    enum_qualified_nodup := hwt.enum_qualified_nodup
    enum_names_nodup := hwt.enum_names_nodup
    enum_variant_nodup := hwt.enum_variant_nodup
    enum_fields_nodup := hwt.enum_fields_nodup
    defaultValues_typed := hwt.defaultValues_typed
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
    funEnv_sig_consistent := hwt.funEnv_sig_consistent
    refs_tracked_mapped := hwt.refs_tracked_mapped
    lenv_labels_in_blocks := hwt.lenv_labels_in_blocks
    has_return_info := hwt.has_return_info
    varStore_locs_bound := by
      intro y loc_y hvar
      by_cases heq : y = x
      · subst heq; rw [lookup_insert_same] at hvar; cases hvar
      · rw [lookup_insert_ne _ x y _ heq] at hvar
        exact hwt.varStore_locs_bound y loc_y hvar
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
    (hrmap_live : ∀ r' loc' path', r' ∈ pe.refs → rmap.map r' = some (loc', path') →
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
      · exact hrmap_live r2 loc2 path2 hr2_mem hrmap_r2
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
    Parameters: inversion results (τ, r, hfresh, hcont) and
    var_consistent results (loc, val, hloc, hread) are pre-computed by the wrappers. -/
private theorem preservation_borrow (m : Machine) (env : TypeEnv) (lenv : LabelEnv)
    (retTypes : List ParamType) (rmap : RefMap)
    (hwt : WellTypedState m env lenv retTypes rmap)
    (hss : StackSafe env.enumEnv m.stack m.frame.returnInfo m.heap retTypes)
    (s : Site) (x : Var) (cont : Stmt) (bk : BorrowingKind)
    -- Inversion results
    (τ : BasicMoveType) (r : Aref)
    (hfresh : freshRefInEnv r env)
    -- VarEnv for continuation (may differ from env.varEnv for borrowMut with enum types)
    (ve' : VarEnv)
    (hve_valid : ∀ y isv τ' ms',
      lookup ve' y = some (isv, τ', ms') → isv = .validVar →
      lookup env.varEnv y = some (isv, τ', ms'))
    (hve_invalid_consistent : ∀ y τ' ms',
      lookup ve' y = some (.invalidVar, τ', ms') →
      lookup m.frame.varStore y = some none ∨ ∃ loc, lookup m.frame.varStore y = some (some loc))
    (hve_wf : VarEnv.RefsNotRoot ve')
    (hcont : typecheck_stmt lenv
      {env with varEnv := ve',
                siteEnv := insert env.siteEnv s (.ref τ r bk),
                pathEnv := update_with_extension r .root [.root_to_var x]
                            (update_with_epsilon r r env.pathEnv)}
      cont retTypes)
    -- Var consistent results
    (loc : Loc) (val : Value)
    (hloc : lookup m.frame.varStore x = some (some loc))
    (hread : m.heap.read loc = some val)
    (hht : HasType env.enumEnv val τ) :
    let m' : Machine := { m with frame := { m.frame with
                siteStore := insert m.frame.siteStore s (Value.ref loc []),
                stmt := cont } }
    ∃ env' lenv' retTypes' rmap',
      env'.enumEnv = env.enumEnv ∧ WellTypedState m' env' lenv' retTypes' rmap' ∧
      StackSafe env.enumEnv m'.stack m'.frame.returnInfo m'.heap retTypes' := by
  intro m'
  -- 1. Define the new rmap extending with r → (loc, [])
  let rmap' : RefMap := { map := fun r' => if r' = r then some (loc, []) else rmap.map r' }
  -- 2. Freshness facts
  have hfresh_pathEnv : freshRefBool r env.pathEnv :=
    freshRefInEnvBool_implies_freshRefBool r env ((freshRefInEnv_iff_freshRefInEnvBool r env).mp hfresh)
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
  refine ⟨{env with varEnv := ve',
                     siteEnv := insert env.siteEnv s (.ref τ r bk),
                     pathEnv := pe'},
          lenv, retTypes, rmap', rfl, ?_, hss⟩
  exact {
    env_wf := by
      have hpe_eps := update_with_epsilon_wellformed r r env.pathEnv hwt.env_wf.pathEnv_wf
        hr_not_root
      have hpe' := update_with_extension_wellformed r .root [.root_to_var x]
        (update_with_epsilon r r env.pathEnv) hpe_eps hr_not_root
      exact ⟨hpe', SiteEnv.insert_refs_not_root env.siteEnv s _ hwt.env_wf.siteEnv_wf hr_not_root, hve_wf⟩
    enumEnv_consistent := hwt.enumEnv_consistent
    enum_qualified_nodup := hwt.enum_qualified_nodup
    enum_names_nodup := hwt.enum_names_nodup
    enum_variant_nodup := hwt.enum_variant_nodup
    enum_fields_nodup := hwt.enum_fields_nodup
    defaultValues_typed := hwt.defaultValues_typed
    stmt_typed := hcont
    var_consistent := by
      intro y isv τ_y ms_y hlook_y
      cases isv with
      | validVar =>
        have hlook_orig := hve_valid y .validVar τ_y ms_y hlook_y rfl
        have ⟨loc_y, v_y, hloc_y, hread_y, hht_y⟩ := hwt.var_consistent y .validVar τ_y ms_y hlook_orig
        refine ⟨loc_y, v_y, hloc_y, hread_y, ?_⟩
        cases τ_y with
        | basic _ => exact hht_y
        | ref bt r_y bk_y =>
          obtain ⟨loc_v, path_v, hv_eq, hrmap_r⟩ := hht_y
          have hrt : r_y ≠ r := Ne.symm (freshRefInEnv_ne_varEnv_ref r env y .validVar bt r_y bk_y ms_y hfresh hlook_orig)
          refine ⟨loc_v, path_v, hv_eq, ?_⟩
          show (if r_y = r then some (loc, []) else rmap.map r_y) = some (loc_v, path_v)
          rw [if_neg hrt]; exact hrmap_r
      | invalidVar =>
        exact hve_invalid_consistent y τ_y ms_y hlook_y
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
        (by intro r' hr'
            rw [hrefs_eq] at hr'
            simp only [List.mem_cons] at hr'
            exact hr')
    rmap_paths :=
      rmap_paths_update_with_borrow rmap m.heap env.pathEnv r x loc
        m.frame.varStore hr_fresh_pe hr_not_root hreadref hloc
        hwt.rmap_root_none hwt.no_paths_to_root hwt.root_path_coherence
        hwt.rmap_live hwt.rmap_paths
    varEnv_refs_in_pathEnv := by
      intro x' bt' r' bk' ms' hv
      have hv_orig := hve_valid x' .validVar (.ref bt' r' bk') ms' hv rfl
      have hold := hwt.varEnv_refs_in_pathEnv x' bt' r' bk' ms' hv_orig
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
    live_refs_unique := by
      have hold := live_refs_unique_insert_fresh_ref hwt s (.ref τ r bk) r
        hr_fresh_pe (fun _ r' _ h => by simp only [MoveType.ref.injEq] at h; exact h.2.1.symm)
      intro r'
      refine ⟨fun x' bt' bk' ms' s' bt'' bk'' hv hs => ?_,
              (hold r').2.1,
              fun x' y bt' bt'' bk' bk'' ms' ms'' hne hx hy => ?_⟩
      · have hv_orig := hve_valid x' .validVar (.ref bt' r' bk') ms' hv rfl
        exact (hold r').1 x' bt' bk' ms' s' bt'' bk'' hv_orig hs
      · have hx_orig := hve_valid x' .validVar (.ref bt' r' bk') ms' hx rfl
        have hy_orig := hve_valid y .validVar (.ref bt'' r' bk'') ms'' hy rfl
        exact (hold r').2.2 x' y bt' bt'' bk' bk'' ms' ms'' hne hx_orig hy_orig
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
          · have hvar_orig := hve_valid x' .validVar (.ref bt r' bk') ms' hvar' rfl
            exact absurd (hwt.varEnv_refs_in_pathEnv x' bt r' bk' ms' hvar_orig) hr_fresh_pe
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
        · have hvar_orig := hve_valid x' .validVar (.ref bt r' bk') ms' hvar' rfl
          exact Or.inl ⟨x', bk', ms', hvar_orig⟩
        · by_cases heqs : s' = s
          · subst heqs; rw [lookup_insert_same] at hsite'
            simp only [Option.some.injEq, MoveType.ref.injEq] at hsite'
            exact absurd hsite'.2.1.symm hrt
          · rw [lookup_insert_ne _ s s' _ heqs] at hsite'
            exact Or.inr ⟨s', bk', hsite'⟩
    funEnv_sig_consistent := hwt.funEnv_sig_consistent
    refs_tracked_mapped := by
      intro ref href
      rw [hrefs_eq] at href
      simp only [List.mem_cons] at href
      rcases href with heq | href_old
      · rw [heq]; right
        show (if r = r then some (loc, []) else rmap.map r) ≠ none
        simp
      · cases hwt.refs_tracked_mapped ref href_old with
        | inl h => exact Or.inl h
        | inr h =>
          right
          show (if ref = r then some (loc, []) else rmap.map ref) ≠ none
          have hne : ref ≠ r := fun heq => hr_fresh_pe (heq ▸ href_old)
          simp [hne]; exact h
    lenv_labels_in_blocks := hwt.lenv_labels_in_blocks
    has_return_info := hwt.has_return_info
    varStore_locs_bound := hwt.varStore_locs_bound
  }

/-- Preservation for borrowImm: thin wrapper around preservation_borrow. -/
private theorem preservation_borrowImm (m m' : Machine) (env : TypeEnv) (lenv : LabelEnv)
    (retTypes : List ParamType) (rmap : RefMap)
    (hwt : WellTypedState m env lenv retTypes rmap)
    (hss : StackSafe env.enumEnv m.stack m.frame.returnInfo m.heap retTypes)
    (s : Site) (x : Var) (cont : Stmt)
    (hstmt : m.frame.stmt = .letBind s (.usage (.borrowImm x)) cont)
    (hstep : step (.running m) = .running m') :
    ∃ env' lenv' retTypes' rmap',
      env'.enumEnv = env.enumEnv ∧ WellTypedState m' env' lenv' retTypes' rmap' ∧
      StackSafe env.enumEnv m'.stack m'.frame.returnInfo m'.heap retTypes' := by
  obtain ⟨τ, ms, r, hlookup, hfresh, hcont⟩ :=
    inv_borrowImm (by rw [← hstmt]; exact hwt.stmt_typed)
  obtain ⟨loc, val, hloc, hread, hht_val⟩ :=
    hwt.var_consistent x .validVar (.basic τ) ms hlookup
  have hgl : getVarLoc m x = some loc := by unfold getVarLoc; simp [hloc]
  simp only [step, hstmt, hgl, ExecState.running.injEq] at hstep; subst hstep
  exact preservation_borrow m env lenv retTypes rmap hwt hss s x cont .siteBorrowImm
    τ r hfresh env.varEnv
    (fun _ _ _ _ h _ => h) (fun y τ' ms' h => hwt.var_consistent y .invalidVar τ' ms' h)
    hwt.env_wf.varEnv_wf hcont loc val hloc hread hht_val

/-- Preservation for borrowMut: thin wrapper around preservation_borrow. -/
private theorem preservation_borrowMut (m m' : Machine) (env : TypeEnv) (lenv : LabelEnv)
    (retTypes : List ParamType) (rmap : RefMap)
    (hwt : WellTypedState m env lenv retTypes rmap)
    (hss : StackSafe env.enumEnv m.stack m.frame.returnInfo m.heap retTypes)
    (s : Site) (x : Var) (cont : Stmt)
    (hstmt : m.frame.stmt = .letBind s (.usage (.borrowMut x)) cont)
    (hstep : step (.running m) = .running m') :
    ∃ env' lenv' retTypes' rmap',
      env'.enumEnv = env.enumEnv ∧ WellTypedState m' env' lenv' retTypes' rmap' ∧
      StackSafe env.enumEnv m'.stack m'.frame.returnInfo m'.heap retTypes' := by
  obtain ⟨τ, ms, r, hlookup, hfresh, hcont⟩ :=
    inv_borrowMut (by rw [← hstmt]; exact hwt.stmt_typed)
  obtain ⟨loc, val, hloc, hread, hht_val⟩ :=
    hwt.var_consistent x .validVar (.basic τ) ms hlookup
  have hgl : getVarLoc m x = some loc := by unfold getVarLoc; simp [hloc]
  simp only [step, hstmt, hgl, ExecState.running.injEq] at hstep; subst hstep
  exact preservation_borrow m env lenv retTypes rmap hwt hss s x cont .siteBorrowMut
    τ r hfresh env.varEnv
    (fun _ _ _ _ h _ => h) (fun y τ' ms' h => hwt.var_consistent y .invalidVar τ' ms' h)
    hwt.env_wf.varEnv_wf hcont loc val hloc hread hht_val

/-- fieldPathOf distributes over append. -/
private theorem fieldPathOf_append (l₁ l₂ : List PathElement) :
    fieldPathOf (l₁ ++ l₂) = fieldPathOf l₁ ++ fieldPathOf l₂ := by
  induction l₁ with
  | nil => simp [fieldPathOf]
  | cons hd tl ih =>
    cases hd with
    | field f => simp [fieldPathOf, ih]
    | root_to_var y => simp [fieldPathOf, ih]
    | vecElem => simp [fieldPathOf, ih]
    | variantField => simp [fieldPathOf, ih]

/-- Unified preservation for borrowField/borrowMutField.
    Both have identical runtime semantics (extend ref with field) and identical
    proof structure — only the BorrowingKind differs.
    The source site is deleted and a new site is created with a fresh ref rf
    pointing to (loc, path ++ [field]) where (loc, path) is the source ref's rmap entry.
    rmap_live for the new ref rf requires heap.readRef loc (path ++ [field]) ≠ none,
    which follows from the rmap_has_type invariant on the parent ref s. -/
private theorem preservation_borrowField (m : Machine) (env : TypeEnv) (lenv : LabelEnv)
    (retTypes : List ParamType) (rmap : RefMap)
    (hwt : WellTypedState m env lenv retTypes rmap)
    (hss : StackSafe env.enumEnv m.stack m.frame.returnInfo m.heap retTypes)
    (af src : Site) (field : Field) (cont : Stmt) (bk : BorrowingKind)
    -- Inversion results
    (bt' : BasicMoveType) (fentries : AssocMap Field BasicMoveType) (s rf : Aref)
    (hlookup_src : lookup env.siteEnv src = some (.ref (.trecord fentries) s bk))
    (hfield : lookup fentries field = some bt')
    (hfresh : freshRefInEnv rf env)
    (hcont : typecheck_stmt lenv
      {env with siteEnv := insert (delete env.siteEnv src) af (.ref bt' rf bk),
                pathEnv := update_with_extension rf s [.field field] env.pathEnv}
      cont retTypes)
    -- Site consistent results
    (loc : Loc) (path : List Field)
    (hrmap_s : rmap.map s = some (loc, path)) :
    let m' : Machine := { m with frame := { m.frame with
                siteStore := insert m.frame.siteStore af (Value.ref loc (path ++ [field])),
                stmt := cont } }
    ∃ env' lenv' retTypes' rmap',
      env'.enumEnv = env.enumEnv ∧ WellTypedState m' env' lenv' retTypes' rmap' ∧
      StackSafe env.enumEnv m'.stack m'.frame.returnInfo m'.heap retTypes' := by
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
  have hlive_s : m.heap.readRef loc path ≠ none := hwt.rmap_live s loc path hs_in_refs hrmap_s
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
          lenv, retTypes, rmap', rfl, ?_, hss⟩
  exact {
    env_wf := TypeEnv.delete_insert_pathEnv_wf env src af (.ref bt' rf bk) pe' hwt.env_wf
      (update_with_extension_wellformed rf s [.field field] env.pathEnv hwt.env_wf.pathEnv_wf
        hrf_not_root) hrf_not_root
    enumEnv_consistent := hwt.enumEnv_consistent
    enum_qualified_nodup := hwt.enum_qualified_nodup
    enum_names_nodup := hwt.enum_names_nodup
    enum_variant_nodup := hwt.enum_variant_nodup
    enum_fields_nodup := hwt.enum_fields_nodup
    defaultValues_typed := hwt.defaultValues_typed
    stmt_typed := hcont
    var_consistent := var_consistent_extend_rmap_fresh hwt rf loc (path ++ [field]) hfresh
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
        have ⟨v', hv', hm⟩ := site_consistent_old_entry_extend_rmap hwt rf loc (path ++ [field]) hfresh s' τ' hl
        exact ⟨v', by rw [lookup_insert_ne _ af s' _ heq]; exact hv', hm⟩
    rmap_live := rmap_live_extend_fresh hwt rf loc (path ++ [field]) hreadref_field
        (by intro r' hr'; rw [hrefs_eq] at hr'; simp only [List.mem_cons] at hr'; exact hr')
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
    funEnv_sig_consistent := hwt.funEnv_sig_consistent
    refs_tracked_mapped := by
      intro ref href
      rw [hrefs_eq] at href
      simp only [List.mem_cons] at href
      rcases href with heq | href_old
      · rw [heq]; right
        show (if rf = rf then some (loc, path ++ [field]) else rmap.map rf) ≠ none
        simp
      · cases hwt.refs_tracked_mapped ref href_old with
        | inl h => exact Or.inl h
        | inr h =>
          right
          show (if ref = rf then some (loc, path ++ [field]) else rmap.map ref) ≠ none
          have hne : ref ≠ rf := fun heq => hrf_fresh_pe (heq ▸ href_old)
          simp [hne]; exact h
    lenv_labels_in_blocks := hwt.lenv_labels_in_blocks
    has_return_info := hwt.has_return_info
    varStore_locs_bound := hwt.varStore_locs_bound
  }

/-- Preservation for borrowField: thin wrapper around preservation_borrowField. -/
private theorem preservation_borrowFieldImm (m m' : Machine) (env : TypeEnv) (lenv : LabelEnv)
    (retTypes : List ParamType) (rmap : RefMap)
    (hwt : WellTypedState m env lenv retTypes rmap)
    (hss : StackSafe env.enumEnv m.stack m.frame.returnInfo m.heap retTypes)
    (af : Site) (src : Site) (bt : BasicMoveType) (field : Field) (cont : Stmt)
    (hstmt : m.frame.stmt = .letBind af (.borrowField src bt field) cont)
    (hstep : step (.running m) = .running m') :
    ∃ env' lenv' retTypes' rmap',
      env'.enumEnv = env.enumEnv ∧ WellTypedState m' env' lenv' retTypes' rmap' ∧
      StackSafe env.enumEnv m'.stack m'.frame.returnInfo m'.heap retTypes' := by
  obtain ⟨bt', isBor, fentries, s, rf, hlookup_src, hbt, hfield, hfresh, hcont⟩ :=
    inv_borrowField (by rw [← hstmt]; exact hwt.stmt_typed)
  subst hbt
  obtain ⟨vref, hvref, hmatch⟩ := hwt.site_consistent src (.ref (.trecord fentries) s isBor) hlookup_src
  obtain ⟨loc, path, hveq, hrmap_s⟩ := hmatch
  have hrs : readSite m src = some vref := hvref
  rw [hveq] at hrs
  simp only [step, hstmt, hrs, ExecState.running.injEq] at hstep; subst hstep
  exact preservation_borrowField m env lenv retTypes rmap hwt hss af src field cont isBor
    bt' fentries s rf hlookup_src hfield hfresh hcont loc path hrmap_s

/-- Preservation for borrowMutField: thin wrapper around preservation_borrowField. -/
private theorem preservation_borrowMutField (m m' : Machine) (env : TypeEnv) (lenv : LabelEnv)
    (retTypes : List ParamType) (rmap : RefMap)
    (hwt : WellTypedState m env lenv retTypes rmap)
    (hss : StackSafe env.enumEnv m.stack m.frame.returnInfo m.heap retTypes)
    (af : Site) (src : Site) (bt : BasicMoveType) (field : Field) (cont : Stmt)
    (hstmt : m.frame.stmt = .letBind af (.borrowMutField src bt field) cont)
    (hstep : step (.running m) = .running m') :
    ∃ env' lenv' retTypes' rmap',
      env'.enumEnv = env.enumEnv ∧ WellTypedState m' env' lenv' retTypes' rmap' ∧
      StackSafe env.enumEnv m'.stack m'.frame.returnInfo m'.heap retTypes' := by
  obtain ⟨btf, fentries, s, rf, hlookup_src, hbt, hfield, hfresh, hcont⟩ :=
    inv_borrowMutField (by rw [← hstmt]; exact hwt.stmt_typed)
  subst hbt
  obtain ⟨vref, hvref, hmatch⟩ := hwt.site_consistent src (.ref (.trecord fentries) s .siteBorrowMut) hlookup_src
  obtain ⟨loc, path, hveq, hrmap_s⟩ := hmatch
  have hrs : readSite m src = some vref := hvref
  rw [hveq] at hrs
  simp only [step, hstmt, hrs, ExecState.running.injEq] at hstep; subst hstep
  exact preservation_borrowField m env lenv retTypes rmap hwt hss af src field cont .siteBorrowMut
    btf fentries s rf hlookup_src hfield hfresh hcont loc path hrmap_s

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

/-- After delete_ref_node, no_paths_to_root is preserved. -/
private lemma no_paths_to_root_delete_ref_node'
    {m : Machine} {env : TypeEnv} {lenv : LabelEnv} {retTypes : List ParamType} {rmap : RefMap}
    (hwt : WellTypedState m env lenv retTypes rmap)
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
    {m : Machine} {env : TypeEnv} {lenv : LabelEnv} {retTypes : List ParamType} {rmap : RefMap}
    (hwt : WellTypedState m env lenv retTypes rmap)
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
    {m : Machine} {env : TypeEnv} {lenv : LabelEnv} {retTypes : List ParamType} {rmap : RefMap}
    (hwt : WellTypedState m env lenv retTypes rmap)
    (site : Site) :
    ∀ s' τ',
      lookup (delete env.siteEnv site) s' = some τ' →
      ∃ v', lookup m.frame.siteStore s' = some v' ∧ ValueMatchesType env.enumEnv v' τ' rmap := by
  intro s' τ' hl
  have hne : s' ≠ site := by
    intro heq; subst heq; rw [lookup_delete_same] at hl; simp at hl
  rw [lookup_delete_ne env.siteEnv site s' hne] at hl
  exact hwt.site_consistent s' τ' hl

/-- After delete_ref_node r, varEnv refs remain in the filtered pathEnv.refs.
    Uses live_refs_unique to show any varEnv ref r' ≠ r. -/
private lemma varEnv_refs_in_pathEnv_delete_ref_node
    {m : Machine} {env : TypeEnv} {lenv : LabelEnv} {retTypes : List ParamType} {rmap : RefMap}
    (hwt : WellTypedState m env lenv retTypes rmap)
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
    {m : Machine} {env : TypeEnv} {lenv : LabelEnv} {retTypes : List ParamType} {rmap : RefMap}
    (hwt : WellTypedState m env lenv retTypes rmap)
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
    {m : Machine} {env : TypeEnv} {lenv : LabelEnv} {retTypes : List ParamType} {rmap : RefMap}
    (hwt : WellTypedState m env lenv retTypes rmap)
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
    (retTypes : List ParamType) (rmap : RefMap)
    (hwt : WellTypedState m env lenv retTypes rmap)
    (hss : StackSafe env.enumEnv m.stack m.frame.returnInfo m.heap retTypes)
    (s : Site) (src : Site) (cont : Stmt)
    (hstmt : m.frame.stmt = .letBind s (.readRef src) cont)
    (hstep : step (.running m) = .running m') :
    ∃ env' lenv' retTypes' rmap',
      env'.enumEnv = env.enumEnv ∧ WellTypedState m' env' lenv' retTypes' rmap' ∧
      StackSafe env.enumEnv m'.stack m'.frame.returnInfo m'.heap retTypes' := by
  obtain ⟨r, τ, isBor, hlookup, hcont⟩ := inv_readRef (by rw [← hstmt]; exact hwt.stmt_typed)
  obtain ⟨vref, hvref, hmatch⟩ := hwt.site_consistent src (.ref τ r isBor) hlookup
  obtain ⟨loc, path, hveq, hrmap⟩ := hmatch
  have hr_tracked : r ∈ env.pathEnv.refs := hwt.siteEnv_refs_in_pathEnv src τ r isBor hlookup
  have hheap := hwt.rmap_live r loc path hr_tracked hrmap
  cases hrd : m.heap.readRef loc path with
  | none => exact absurd hrd hheap
  | some val =>
    have hrs : readSite m src = some (.ref loc path) := by rw [readSite, hvref, hveq]
    simp only [step, hstmt, hrs, hrd, ExecState.running.injEq] at hstep; subst hstep
    have hr_not_root : r ≠ .root := hwt.env_wf.siteEnv_wf src (.ref τ r isBor) hlookup
    refine ⟨{env with siteEnv := insert (delete env.siteEnv src) s (.basic τ),
                       pathEnv := delete_ref_node env.pathEnv r},
            lenv, retTypes, rmap, rfl, ?_, hss⟩
    exact {
      env_wf := ⟨delete_ref_node_wellformed env.pathEnv r hwt.env_wf.pathEnv_wf hr_not_root,
                 SiteEnv.insert_refs_not_root (delete env.siteEnv src) s (.basic τ)
                   (SiteEnv.delete_refs_not_root env.siteEnv src hwt.env_wf.siteEnv_wf) trivial,
                 hwt.env_wf.varEnv_wf⟩
      enumEnv_consistent := hwt.enumEnv_consistent
      enum_qualified_nodup := hwt.enum_qualified_nodup
      enum_names_nodup := hwt.enum_names_nodup
      enum_variant_nodup := hwt.enum_variant_nodup
      enum_fields_nodup := hwt.enum_fields_nodup
      defaultValues_typed := hwt.defaultValues_typed
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
      rmap_live := by
        intro r' loc' path' hr' hrmap'
        have hr'_old : r' ∈ env.pathEnv.refs := by
          simp only [delete_ref_node_refs, List.mem_filter, decide_eq_true_eq] at hr'; exact hr'.1
        exact hwt.rmap_live r' loc' path' hr'_old hrmap'
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
      funEnv_sig_consistent := hwt.funEnv_sig_consistent
      refs_tracked_mapped := by
        intro ref href
        simp only [delete_ref_node_refs, List.mem_filter, decide_eq_true_eq] at href
        exact hwt.refs_tracked_mapped ref href.1
      lenv_labels_in_blocks := hwt.lenv_labels_in_blocks
      has_return_info := hwt.has_return_info
      varStore_locs_bound := hwt.varStore_locs_bound
    }

/-- If evalBinop succeeds and binop_type determines the output type,
    the result value has the output type. -/
private lemma evalBinop_has_type (enumEnv : EnumEnv) (op : Binop) (bt1 bt2 bt3 : BasicMoveType)
    (na nb : Nat) (result : Value)
    (hbt : binop_type op bt1 bt2 = some bt3)
    (heval : evalBinop op na nb = some result) :
    HasType enumEnv result bt3 := by
  -- `binop_type` pins `bt3` down from the operator, so case on the operator and
  -- then read the result type straight off `evalBinop`.
  -- Note: no alternative below may use a nested `by`, since an unsolved goal
  -- inside one is *reported* rather than failing the enclosing `first`/`try`.
  cases op <;> simp only [binop_type] at hbt <;>
    (try (cases bt1 <;> cases bt2 <;> simp at hbt)) <;>
    subst hbt <;>
    simp only [evalBinop] at heval <;>
    first
    -- `and`/`or` have no integer instantiation: `evalBinop` returned `none`
    | exact Option.noConfusion heval
    -- add/sub/mul
    | (simp only [Option.some.injEq] at heval; subst heval; exact HasType.int _)
    -- the comparisons eq/neq/lt/gt/le/ge, all of which yield `tbool`
    | (simp only [Option.some.injEq] at heval; subst heval; exact HasType.bool _)
    | (-- div/mod: heval still has a match on the divisor
       cases nb with
       | zero => simp at heval
       | succ n =>
         -- `simp` substitutes `result` and may already discharge the goal
         simp at heval
         all_goals (subst heval; exact HasType.int _))

private theorem preservation_binop (m m' : Machine) (env : TypeEnv) (lenv : LabelEnv)
    (retTypes : List ParamType) (rmap : RefMap)
    (hwt : WellTypedState m env lenv retTypes rmap)
    (hss : StackSafe env.enumEnv m.stack m.frame.returnInfo m.heap retTypes)
    (s : Site) (op : Binop) (sA sB : Site) (cont : Stmt)
    (hstmt : m.frame.stmt = .letBind s (.binop op sA sB) cont)
    (hstep : step (.running m) = .running m') :
    ∃ env' lenv' retTypes' rmap',
      env'.enumEnv = env.enumEnv ∧ WellTypedState m' env' lenv' retTypes' rmap' ∧
      StackSafe env.enumEnv m'.stack m'.frame.returnInfo m'.heap retTypes' := by
  obtain ⟨bt1, bt2, bt3, ha, hb, hbt, hcont⟩ := inv_binop (by rw [← hstmt]; exact hwt.stmt_typed)
  obtain ⟨va, hva, hma⟩ := hwt.site_consistent sA (.basic bt1) ha
  obtain ⟨vb, hvb, hmb⟩ := hwt.site_consistent sB (.basic bt2) hb
  have hrsa : readSite m sA = some va := hva
  have hrsb : readSite m sB = some vb := hvb
  -- Prove site_consistent before destructive case analysis (sA/sB go out of scope)
  have hsc : ∀ result, HasType env.enumEnv result bt3 → ∀ s' τ',
      lookup (insert (delete (delete env.siteEnv sA) sB) s (.basic bt3)) s' = some τ' →
      ∃ v', lookup (insert m.frame.siteStore s result) s' = some v' ∧
            ValueMatchesType env.enumEnv v' τ' rmap := by
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
  -- Case-split on va/vb: both ints or both bools (use type info to eliminate cross cases)
  have ⟨result, hht_result, hm'_eq⟩ : ∃ result, HasType env.enumEnv result bt3 ∧
      m' = { frame := { m.frame with
                siteStore := AssocMap.insert m.frame.siteStore s result
                stmt := cont },
             stack := m.stack, heap := m.heap, enumEnv := m.enumEnv } := by
    -- Case-split on va and vb to reduce the match in hstep
    cases hva_eq : va with
    | int na =>
      cases hvb_eq : vb with
      | int nb =>
        simp only [hva_eq, hvb_eq] at hstep
        cases heval : evalBinop op na nb <;> simp [heval] at hstep
        exact ⟨_, evalBinop_has_type env.enumEnv op bt1 bt2 bt3 na nb _ hbt heval, hstep.symm⟩
      | bool _ => simp only [hva_eq, hvb_eq] at hstep; nomatch hstep
      | unit => simp only [hva_eq, hvb_eq] at hstep; nomatch hstep
      | record _ => simp only [hva_eq, hvb_eq] at hstep; nomatch hstep
      | ref _ _ => simp only [hva_eq, hvb_eq] at hstep; nomatch hstep
      | vec _ => simp only [hva_eq, hvb_eq] at hstep; nomatch hstep
      | variant _ _ _ => simp only [hva_eq, hvb_eq] at hstep; nomatch hstep
    | bool ba =>
      cases hvb_eq : vb with
      | bool bb =>
        simp only [hva_eq, hvb_eq] at hstep
        cases heval : evalBinopBool op ba bb <;> simp [heval] at hstep
        rename_i result
        refine ⟨result, ?_, hstep.symm⟩
        have hbt1 : bt1 = .tbool := by
          rw [hva_eq] at hma; cases hma with | bool => rfl
        subst hbt1
        cases op <;> simp only [binop_type] at hbt <;>
          (try (cases bt2 <;> simp at hbt)) <;>
          subst hbt <;>
          simp only [evalBinopBool, Option.some.injEq] at heval <;>
          subst heval <;> exact HasType.bool _
      | int _ => simp only [hva_eq, hvb_eq] at hstep; nomatch hstep
      | unit => simp only [hva_eq, hvb_eq] at hstep; nomatch hstep
      | record _ => simp only [hva_eq, hvb_eq] at hstep; nomatch hstep
      | ref _ _ => simp only [hva_eq, hvb_eq] at hstep; nomatch hstep
      | vec _ => simp only [hva_eq, hvb_eq] at hstep; nomatch hstep
      | variant _ _ _ => simp only [hva_eq, hvb_eq] at hstep; nomatch hstep
    | unit => simp only [hva_eq] at hstep; nomatch hstep
    | record _ => simp only [hva_eq] at hstep; nomatch hstep
    | ref _ _ => simp only [hva_eq] at hstep; nomatch hstep
    | vec _ => simp only [hva_eq] at hstep; nomatch hstep
    | variant _ _ _ => simp only [hva_eq] at hstep; nomatch hstep
  subst hm'_eq
  refine ⟨{env with siteEnv := insert (delete (delete env.siteEnv sA) sB) s (.basic bt3)},
          lenv, retTypes, rmap, rfl, ?_, hss⟩
  exact {
    env_wf := TypeEnv.delete_delete_insert_wf env sA sB s (.basic bt3) hwt.env_wf trivial
    enumEnv_consistent := hwt.enumEnv_consistent
    enum_qualified_nodup := hwt.enum_qualified_nodup
    enum_names_nodup := hwt.enum_names_nodup
    enum_variant_nodup := hwt.enum_variant_nodup
    enum_fields_nodup := hwt.enum_fields_nodup
    defaultValues_typed := hwt.defaultValues_typed
    stmt_typed := hcont
    var_consistent := hwt.var_consistent
    site_consistent := hsc result hht_result
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
    funEnv_sig_consistent := hwt.funEnv_sig_consistent
    refs_tracked_mapped := hwt.refs_tracked_mapped
    lenv_labels_in_blocks := hwt.lenv_labels_in_blocks
    has_return_info := hwt.has_return_info
    varStore_locs_bound := hwt.varStore_locs_bound
  }

/-- If evalUnop succeeds and unop_type determines the output type,
    the result value has the output type. -/
private lemma evalUnop_has_type (enumEnv : EnumEnv) (uop : Unop) (bt1 bt2 : BasicMoveType)
    (va result : Value)
    (hbt : unop_type uop bt1 = some bt2)
    (heval : evalUnop uop va = some result) :
    HasType enumEnv result bt2 := by
  cases uop with
  | not =>
    cases bt1 with
    | tbool =>
      simp only [unop_type, Option.some.injEq] at hbt
      subst hbt
      cases va with
      | bool b =>
        simp only [evalUnop, Option.some.injEq] at heval
        subst heval; exact HasType.bool _
      | int _ => simp [evalUnop] at heval
      | unit => simp [evalUnop] at heval
      | record _ => simp [evalUnop] at heval
      | ref _ _ => simp [evalUnop] at heval
      | vec _ _ => simp [evalUnop] at heval
      | variant _ _ _ => simp [evalUnop] at heval
    | u64 => simp [unop_type] at hbt
    | u8 => simp [unop_type] at hbt
    | tunit => simp [unop_type] at hbt
    | trecord _ => simp [unop_type] at hbt
    | tvec _ => simp [unop_type] at hbt
    | tenum _ => simp [unop_type] at hbt

private theorem preservation_unop (m m' : Machine) (env : TypeEnv) (lenv : LabelEnv)
    (retTypes : List ParamType) (rmap : RefMap)
    (hwt : WellTypedState m env lenv retTypes rmap)
    (hss : StackSafe env.enumEnv m.stack m.frame.returnInfo m.heap retTypes)
    (s : Site) (op : Unop) (sA : Site) (cont : Stmt)
    (hstmt : m.frame.stmt = .letBind s (.unop op sA) cont)
    (hstep : step (.running m) = .running m') :
    ∃ env' lenv' retTypes' rmap',
      env'.enumEnv = env.enumEnv ∧ WellTypedState m' env' lenv' retTypes' rmap' ∧
      StackSafe env.enumEnv m'.stack m'.frame.returnInfo m'.heap retTypes' := by
  obtain ⟨bt1, bt2, ha, hbt, hcont⟩ := inv_unop (by rw [← hstmt]; exact hwt.stmt_typed)
  obtain ⟨va, hva, hma⟩ := hwt.site_consistent sA (.basic bt1) ha
  have hrsa : readSite m sA = some va := hva
  -- Prove site_consistent before destructive case analysis (sA goes out of scope)
  have hsc : ∀ result, HasType env.enumEnv result bt2 → ∀ s' τ',
      lookup (insert (delete env.siteEnv sA) s (.basic bt2)) s' = some τ' →
      ∃ v', lookup (insert m.frame.siteStore s result) s' = some v' ∧
            ValueMatchesType env.enumEnv v' τ' rmap := by
    intro result hht_result s' τ' hl
    by_cases heq : s' = s
    · subst heq; simp only [lookup_insert_same, Option.some.injEq] at hl; subst hl
      exact ⟨result, lookup_insert_same _ _ _, hht_result⟩
    · rw [lookup_insert_ne _ s s' _ heq] at hl
      have hne_a : s' ≠ sA := by
        intro h; rw [h, lookup_delete_same] at hl; simp at hl
      rw [lookup_delete_ne _ sA s' hne_a] at hl
      obtain ⟨v, hvs, hm⟩ := hwt.site_consistent s' τ' hl
      exact ⟨v, by rw [lookup_insert_ne _ s s' _ heq]; exact hvs, hm⟩
  simp only [step, hstmt, hrsa] at hstep
  have ⟨result, hht_result, hm'_eq⟩ : ∃ result, HasType env.enumEnv result bt2 ∧
      m' = { frame := { m.frame with
                siteStore := AssocMap.insert m.frame.siteStore s result
                stmt := cont },
             stack := m.stack, heap := m.heap, enumEnv := m.enumEnv } := by
    cases heval : evalUnop op va with
    | none => rw [heval] at hstep; nomatch hstep
    | some v =>
      rw [heval] at hstep
      simp only [ExecState.running.injEq] at hstep
      exact ⟨v, evalUnop_has_type env.enumEnv op bt1 bt2 va v hbt heval, hstep.symm⟩
  subst hm'_eq
  refine ⟨{env with siteEnv := insert (delete env.siteEnv sA) s (.basic bt2)},
          lenv, retTypes, rmap, rfl, ?_, hss⟩
  exact {
    env_wf := TypeEnv.delete_insert_wf env sA s (.basic bt2) hwt.env_wf trivial
    enumEnv_consistent := hwt.enumEnv_consistent
    enum_qualified_nodup := hwt.enum_qualified_nodup
    enum_names_nodup := hwt.enum_names_nodup
    enum_variant_nodup := hwt.enum_variant_nodup
    enum_fields_nodup := hwt.enum_fields_nodup
    defaultValues_typed := hwt.defaultValues_typed
    stmt_typed := hcont
    var_consistent := hwt.var_consistent
    site_consistent := hsc result hht_result
    rmap_live := hwt.rmap_live
    rmap_paths := hwt.rmap_paths
    varEnv_refs_in_pathEnv := hwt.varEnv_refs_in_pathEnv
    siteEnv_refs_in_pathEnv := by
      intro s' bt r bk hl
      by_cases heq : s' = s
      · subst heq; simp [lookup_insert_same] at hl
      · rw [lookup_insert_ne _ s s' _ heq] at hl
        have hne_a : s' ≠ sA := by
          intro h; rw [h, lookup_delete_same] at hl; simp at hl
        rw [lookup_delete_ne _ sA s' hne_a] at hl
        exact hwt.siteEnv_refs_in_pathEnv s' bt r bk hl
    live_refs_unique := by
      intro r'
      refine ⟨fun x bt bk ms s' bt' bk' hv hs => ?_,
              fun s1 s2 bt1' bt2' bk1 bk2 hne hs1 hs2 => ?_,
              fun x y bt1' bt2' bk1 bk2 ms1 ms2 hne hx hy =>
                (hwt.live_refs_unique r').2.2 x y bt1' bt2' bk1 bk2 ms1 ms2 hne hx hy⟩
      · by_cases heq : s' = s
        · subst heq; simp [lookup_insert_same] at hs
        · rw [lookup_insert_ne _ s s' _ heq] at hs
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
            have hne1_a : s1 ≠ sA := by
              intro h; rw [h, lookup_delete_same] at hs1; simp at hs1
            have hne2_a : s2 ≠ sA := by
              intro h; rw [h, lookup_delete_same] at hs2; simp at hs2
            rw [lookup_delete_ne _ sA s1 hne1_a] at hs1
            rw [lookup_delete_ne _ sA s2 hne2_a] at hs2
            exact (hwt.live_refs_unique r').2.1 s1 s2 bt1' bt2' bk1 bk2 hne hs1 hs2
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
          have hne_a : s' ≠ sA := by
            intro h; rw [h, lookup_delete_same] at hsite; simp at hsite
          rw [lookup_delete_ne _ sA s' hne_a] at hsite
          exact Or.inr ⟨s', bk, hsite⟩
    funEnv_sig_consistent := hwt.funEnv_sig_consistent
    refs_tracked_mapped := hwt.refs_tracked_mapped
    lenv_labels_in_blocks := hwt.lenv_labels_in_blocks
    has_return_info := hwt.has_return_info
    varStore_locs_bound := hwt.varStore_locs_bound
  }

private theorem preservation_release (m m' : Machine) (env : TypeEnv) (lenv : LabelEnv)
    (retTypes : List ParamType) (rmap : RefMap)
    (hwt : WellTypedState m env lenv retTypes rmap)
    (hss : StackSafe env.enumEnv m.stack m.frame.returnInfo m.heap retTypes)
    (site : Site) (cont : Stmt)
    (hstmt : m.frame.stmt = .release site cont)
    (hstep : step (.running m) = .running m') :
    ∃ env' lenv' retTypes' rmap',
      env'.enumEnv = env.enumEnv ∧ WellTypedState m' env' lenv' retTypes' rmap' ∧
      StackSafe env.enumEnv m'.stack m'.frame.returnInfo m'.heap retTypes' := by
  simp only [step, hstmt, ExecState.running.injEq] at hstep; subst hstep
  rcases inv_release (by rw [← hstmt]; exact hwt.stmt_typed) with
    ⟨τ, r, isBor, hlookup, hcont⟩ | ⟨bt, hlookup, hcont⟩
  · -- Case 1: release of a ref site
    have hr_not_root : r ≠ .root := hwt.env_wf.siteEnv_wf site (.ref τ r isBor) hlookup
    refine ⟨{env with siteEnv := delete env.siteEnv site,
                       pathEnv := delete_ref_node env.pathEnv r},
            lenv, retTypes, rmap, rfl, ?_, hss⟩
    exact {
      env_wf := ⟨delete_ref_node_wellformed env.pathEnv r hwt.env_wf.pathEnv_wf hr_not_root,
                 SiteEnv.delete_refs_not_root env.siteEnv site hwt.env_wf.siteEnv_wf,
                 hwt.env_wf.varEnv_wf⟩
      enumEnv_consistent := hwt.enumEnv_consistent
      enum_qualified_nodup := hwt.enum_qualified_nodup
      enum_names_nodup := hwt.enum_names_nodup
      enum_variant_nodup := hwt.enum_variant_nodup
      enum_fields_nodup := hwt.enum_fields_nodup
      defaultValues_typed := hwt.defaultValues_typed
      stmt_typed := hcont
      var_consistent := hwt.var_consistent
      site_consistent := site_consistent_delete_site hwt site
      rmap_live := by
        intro r' loc' path' hr' hrmap'
        have hr'_old : r' ∈ env.pathEnv.refs := by
          simp only [delete_ref_node_refs, List.mem_filter, decide_eq_true_eq] at hr'; exact hr'.1
        exact hwt.rmap_live r' loc' path' hr'_old hrmap'
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
      funEnv_sig_consistent := hwt.funEnv_sig_consistent
      refs_tracked_mapped := by
        intro ref href
        simp only [delete_ref_node_refs, List.mem_filter, decide_eq_true_eq] at href
        exact hwt.refs_tracked_mapped ref href.1
      lenv_labels_in_blocks := hwt.lenv_labels_in_blocks
      has_return_info := hwt.has_return_info
      varStore_locs_bound := hwt.varStore_locs_bound
    }
  · -- Case 2: release of a basic-typed site (no pathEnv change)
    refine ⟨{env with siteEnv := delete env.siteEnv site},
            lenv, retTypes, rmap, rfl, ?_, hss⟩
    exact {
      env_wf := ⟨hwt.env_wf.pathEnv_wf,
                 SiteEnv.delete_refs_not_root env.siteEnv site hwt.env_wf.siteEnv_wf,
                 hwt.env_wf.varEnv_wf⟩
      enumEnv_consistent := hwt.enumEnv_consistent
      enum_qualified_nodup := hwt.enum_qualified_nodup
      enum_names_nodup := hwt.enum_names_nodup
      enum_variant_nodup := hwt.enum_variant_nodup
      enum_fields_nodup := hwt.enum_fields_nodup
      defaultValues_typed := hwt.defaultValues_typed
      stmt_typed := hcont
      var_consistent := hwt.var_consistent
      site_consistent := site_consistent_delete_site hwt site
      rmap_live := hwt.rmap_live
      rmap_paths := hwt.rmap_paths
      varEnv_refs_in_pathEnv := hwt.varEnv_refs_in_pathEnv
      siteEnv_refs_in_pathEnv := by
        intro s' bt' r bk hl
        have hne : s' ≠ site := by
          intro h; subst h; rw [lookup_delete_same] at hl; simp at hl
        rw [lookup_delete_ne env.siteEnv site s' hne] at hl
        exact hwt.siteEnv_refs_in_pathEnv s' bt' r bk hl
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
        · have hne : s' ≠ site := by
            intro h; subst h; rw [lookup_delete_same] at hsite; simp at hsite
          rw [lookup_delete_ne env.siteEnv site s' hne] at hsite
          exact Or.inr ⟨s', bk, hsite⟩
      funEnv_sig_consistent := hwt.funEnv_sig_consistent
      refs_tracked_mapped := hwt.refs_tracked_mapped
      lenv_labels_in_blocks := hwt.lenv_labels_in_blocks
      has_return_info := hwt.has_return_info
      varStore_locs_bound := hwt.varStore_locs_bound
    }

private theorem preservation_writeRef (m m' : Machine) (env : TypeEnv) (lenv : LabelEnv)
    (retTypes : List ParamType) (rmap : RefMap)
    (hwt : WellTypedState m env lenv retTypes rmap)
    (hss : StackSafe env.enumEnv m.stack m.frame.returnInfo m.heap retTypes)
    (dst val : Site) (cont : Stmt)
    (hstmt : m.frame.stmt = .writeRef dst val cont)
    (hstep : step (.running m) = .running m') :
    ∃ env' lenv' retTypes' rmap',
      env'.enumEnv = env.enumEnv ∧ WellTypedState m' env' lenv' retTypes' rmap' ∧
      StackSafe env.enumEnv m'.stack m'.frame.returnInfo m'.heap retTypes' := by
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
  have hr_tracked : r ∈ env.pathEnv.refs := hwt.siteEnv_refs_in_pathEnv dst τ r .siteBorrowMut hdst_type
  have hheap := hwt.rmap_live r loc wpath hr_tracked hrmap
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
          lenv, retTypes, rmap, rfl, ?_,
          stackSafe_heap_writeRef env.enumEnv m.stack m.frame.returnInfo m.heap heap' loc wpath
            vval v_leaf τ hss hwr hv_leaf_read hv_leaf_ht hmval
            (fun suffix hne_s => readPath_HasType_transfer v_leaf vval τ suffix hv_leaf_ht hmval)
            (fun suffix hne_s => typeAtPathV_HasType_determined vval v_leaf τ suffix hmval hv_leaf_ht)⟩
  exact {
    env_wf := ⟨delete_ref_node_wellformed env.pathEnv r hwt.env_wf.pathEnv_wf hr_not_root,
               SiteEnv.delete_refs_not_root _ dst
                 (SiteEnv.delete_refs_not_root _ val hwt.env_wf.siteEnv_wf),
               hwt.env_wf.varEnv_wf⟩
    enumEnv_consistent := hwt.enumEnv_consistent
    enum_qualified_nodup := hwt.enum_qualified_nodup
    enum_names_nodup := hwt.enum_names_nodup
    enum_variant_nodup := hwt.enum_variant_nodup
    enum_fields_nodup := hwt.enum_fields_nodup
    defaultValues_typed := hwt.defaultValues_typed
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
            exact writePath_preserves_HasType_generalV v_x wpath vval newRootVal bt_x
              hmatch_x hwp (by
                intro bt_leaf htapV
                have hread_leaf : readPath v_x wpath = some v_leaf := by
                  simp only [Heap.readRef, bind, Option.bind, hread_x] at hv_leaf_read
                  exact hv_leaf_read
                obtain ⟨u, hread_u, hht_u⟩ :=
                  HasType_typeAtPathV v_x bt_x wpath bt_leaf hmatch_x htapV
                rw [hread_leaf] at hread_u
                simp only [Option.some.injEq] at hread_u; subst hread_u
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
      intro r' loc' path' hr'_tracked hrmap'
      have hr'_old : r' ∈ env.pathEnv.refs := by
        simp only [delete_ref_node_refs, List.mem_filter, decide_eq_true_eq] at hr'_tracked
        exact hr'_tracked.1
      have hlive := hwt.rmap_live r' loc' path' hr'_old hrmap'
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
              exact readPath_HasType_transfer v_leaf vval τ (sf :: srest) hv_leaf_ht hmval hleaf_suffix)
      · rw [heap_writeRef_preserves_readRef_diff_loc m.heap loc loc' wpath path' vval heap'
             hloc hwr]
        exact hlive
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
                  simp only [Heap.readRef, bind, Option.bind] at hne hv_leaf_read
                  cases hbase : m.heap.read loc with
                  | none => simp [hbase] at hv_leaf_read
                  | some baseVal =>
                    simp only [hbase] at hne hv_leaf_read
                    rw [← hsuffix, readPath_append] at hne
                    simp only [hv_leaf_read, Option.bind] at hne
                    exact readPath_HasType_transfer v_leaf vval τ (sf :: srest) hv_leaf_ht hmval hne)
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
            by_cases hr'r : r' = r
            · -- r' = r: path' = wpath, after writeRef we read vval with type τ
              subst hr'r
              rw [hrmap] at hrmap'; simp only [Option.some.injEq, Prod.mk.injEq] at hrmap'
              obtain ⟨_, rfl⟩ := hrmap'
              -- After writePath, readPath at wpath gives the new value vval
              have hread_vnew : readPath newRoot wpath = some vval :=
                readPath_after_writePath_same baseVal wpath vval newRoot hwp2
              -- bt = τ because both v_old and v_leaf are at the same path
              have hveq : v_old = v_leaf := by
                rw [hread_old] at hv_leaf_read; simp only [Option.some.injEq] at hv_leaf_read; exact hv_leaf_read
              subst hveq
              refine ⟨vval, ?_, HasType_transfer hht_old hv_leaf_ht hmval⟩
              rw [← hwr']
              simp only [Heap.readRef, bind, Option.bind, Heap.write, Heap.read,
                          lookup_insert_same, hread_vnew]
            · -- r' ≠ r
              have hr'_old : r' ∈ env.pathEnv.refs := by
                rcases hcond' with ⟨x, bk, ms, hvar⟩ | ⟨s', bk, hsite⟩
                · exact hwt.varEnv_refs_in_pathEnv x bt r' bk ms hvar
                · exact hwt.siteEnv_refs_in_pathEnv s' bt r' bk hsite
              have h_rpath :=
                writePath_preserves_readPath_HasType
                  baseVal wpath path' vval newRoot v_leaf v_old τ bt
                  hwp2 hread_old hht_old hv_leaf_read hv_leaf_ht hmval
                  (fun suffix hsne => typeAtPathV_HasType_determined vval v_leaf τ suffix hmval hv_leaf_ht)
              obtain ⟨vnew, hread_vnew, hht_vnew⟩ := h_rpath
              refine ⟨vnew, ?_, hht_vnew⟩
              rw [← hwr']
              simp only [Heap.readRef, bind, Option.bind, Heap.write, Heap.read,
                          lookup_insert_same, hread_vnew]
      · have hread' : heap'.readRef loc' path' = some v_old := by
          rw [heap_writeRef_preserves_readRef_diff_loc m.heap loc loc' wpath path' vval heap'
                hloc' hwr]
          exact hread_old
        exact ⟨v_old, hread', hht_old⟩
    funEnv_sig_consistent := hwt.funEnv_sig_consistent
    refs_tracked_mapped := by
      intro ref href
      simp only [delete_ref_node_refs, List.mem_filter, decide_eq_true_eq] at href
      exact hwt.refs_tracked_mapped ref href.1
    lenv_labels_in_blocks := hwt.lenv_labels_in_blocks
    has_return_info := hwt.has_return_info
    varStore_locs_bound := by
      intro y loc_y hvar
      rw [writeRef_preserves_nextLoc m.heap loc wpath vval heap' hwr]; exact hwt.varStore_locs_bound y loc_y hvar
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

-- ============================================================
-- Variant unpack foldl helpers (uses qualifyField)
-- ============================================================

private theorem variant_unpack_foldl_lookup_not_in_fields
    (vname : Id) (recFields : List (Field × Value)) (siteStore : AssocMap Site Value)
    (fields : List (Field × Site)) (a : Site)
    (hnotin : a ∉ fields.map Prod.snd) :
    lookup (fields.foldl (fun ss (fa : Field × Site) =>
      match recFields.lookup (qualifyField vname fa.1) with
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
    cases hlookup : recFields.lookup (qualifyField vname f) with
    | none => rfl
    | some v => exact lookup_insert_ne siteStore s a v hne

private theorem variant_unpack_foldl_lookup_mem
    (vname : Id) (recFields : List (Field × Value)) (siteStore : AssocMap Site Value)
    (fields : List (Field × Site)) (f : Field) (a : Site) (v : Value)
    (hmem : (f, a) ∈ fields)
    (hfval : recFields.lookup (qualifyField vname f) = some v)
    (huniq : ∀ f', (f', a) ∈ fields → f' = f) :
    lookup (fields.foldl (fun ss (fa : Field × Site) =>
      match recFields.lookup (qualifyField vname fa.1) with
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
      · rw [variant_unpack_foldl_lookup_not_in_fields _ _ _ _ _ ha_tl]
        exact lookup_insert_same siteStore a v
    · have huniq_tl : ∀ f', (f', a) ∈ tl → f' = f :=
        fun f' hf' => huniq f' (List.mem_cons_of_mem _ hf')
      cases hlookup : recFields.lookup (qualifyField vname f') with
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

/-- Helper: if k ∉ ks, then lookup on deleteAll is the same as on the original -/
private lemma lookup_deleteAll_not_mem (l : AssocMap Site MoveType) (ks : List Site)
    (k : Site) (hnotin : k ∉ ks) :
    lookup (deleteAll l ks) k = lookup l k := by
  simp only [AssocMap.deleteAll, AssocMap.lookup]
  rw [← List.lookup_filter_notin l.entries k ks hnotin]

/-- Helper: types_conform is preserved when lookups agree on all listed sites -/
private lemma types_conform_ext {se1 se2 : SiteEnv} {sites : List Site} {pts : List ParamType}
    (htc : types_conform se1 sites pts)
    (heq : ∀ s ∈ sites, lookup se1 s = lookup se2 s) :
    types_conform se2 sites pts := by
  induction sites generalizing pts with
  | nil => cases pts <;> simp_all [types_conform]
  | cons s ss ih =>
    cases pts with
    | nil => simp [types_conform] at htc
    | cons p ps =>
      simp only [types_conform] at htc ⊢
      have hs_mem : s ∈ s :: ss := List.Mem.head ss
      rw [← heq s hs_mem]
      have heq' : ∀ s' ∈ ss, lookup se1 s' = lookup se2 s' :=
        fun s' hs' => heq s' (List.Mem.tail s hs')
      cases hlook : lookup se1 s with
      | none => rw [hlook] at htc; exact htc
      | some τ =>
        rw [hlook] at htc
        match p, τ with
        | ⟨_, none⟩, .basic _ => exact ⟨htc.1, ih htc.2 heq'⟩
        | ⟨_, some _⟩, .ref _ _ _ => exact ⟨htc.1, htc.2.1, ih htc.2.2 heq'⟩
        | ⟨_, none⟩, .ref _ _ _ => exact htc
        | ⟨_, some _⟩, .basic _ => exact htc

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
    (retTypes : List ParamType) (rmap : RefMap)
    (hwt : WellTypedState m env lenv retTypes rmap)
    (hss : StackSafe env.enumEnv m.stack m.frame.returnInfo m.heap retTypes)
    (s : Site) (name : Id) (fieldSites : List (Field × Site)) (cont : Stmt)
    (hstmt : m.frame.stmt = .letBind s (.pack name fieldSites) cont)
    (hstep : step (.running m) = .running m') :
    ∃ env' lenv' retTypes' rmap',
      env'.enumEnv = env.enumEnv ∧ WellTypedState m' env' lenv' retTypes' rmap' ∧
      StackSafe env.enumEnv m'.stack m'.frame.returnInfo m'.heap retTypes' := by
  obtain ⟨fentries, hfield_map, hcomplete, hcont⟩ := inv_pack (by rw [← hstmt]; exact hwt.stmt_typed)
  simp only [step, hstmt] at hstep
  split at hstep
  · simp at hstep
  · rename_i fieldVals hcpf
    simp only [ExecState.running.injEq] at hstep; subst hstep
    refine ⟨{env with siteEnv := insert (deleteAll env.siteEnv (fieldSites.map Prod.snd)) s
                                    (.basic (.trecord fentries))},
            lenv, retTypes, rmap, rfl, ?_, hss⟩
    exact {
      env_wf := TypeEnv.deleteAll_insert_wf env (fieldSites.map Prod.snd) s
                  (.basic (.trecord fentries)) hwt.env_wf trivial
      enumEnv_consistent := hwt.enumEnv_consistent
      enum_qualified_nodup := hwt.enum_qualified_nodup
      enum_names_nodup := hwt.enum_names_nodup
      enum_variant_nodup := hwt.enum_variant_nodup
      enum_fields_nodup := hwt.enum_fields_nodup
      defaultValues_typed := hwt.defaultValues_typed
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
      funEnv_sig_consistent := hwt.funEnv_sig_consistent
      refs_tracked_mapped := hwt.refs_tracked_mapped
      lenv_labels_in_blocks := hwt.lenv_labels_in_blocks
      has_return_info := hwt.has_return_info
      varStore_locs_bound := hwt.varStore_locs_bound
    }

private theorem preservation_assign_valid (m m' : Machine) (env : TypeEnv) (lenv : LabelEnv)
    (retTypes : List ParamType) (rmap : RefMap)
    (hwt : WellTypedState m env lenv retTypes rmap)
    (hss : StackSafe env.enumEnv m.stack m.frame.returnInfo m.heap retTypes)
    (x : Var) (a : Site) (cont : Stmt)
    (ax : Site) (τ : BasicMoveType) (ms : Mut) (r : Aref)
    (hvar : lookup env.varEnv x = some (.validVar, .basic τ, ms))
    (ha_type : lookup env.siteEnv a = some (.basic τ))
    (hfresh : freshRefInEnv r env)
    (hnotin : notIn env.siteEnv ax)
    (hcont : typecheck_stmt lenv
      {env with siteEnv := delete (delete (insert env.siteEnv ax (.ref τ r .siteBorrowMut)) a) ax
                pathEnv := garbage_collect (update_with_extension r .root [.root_to_var x]
                            (update_with_epsilon r r env.pathEnv)) r}
      cont retTypes)
    (hstmt : m.frame.stmt = .assign x a cont)
    (hstep : step (.running m) = .running m') :
    ∃ env' lenv' retTypes' rmap',
      env'.enumEnv = env.enumEnv ∧ WellTypedState m' env' lenv' retTypes' rmap' ∧
      StackSafe env.enumEnv m'.stack m'.frame.returnInfo m'.heap retTypes' := by
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
    have hfresh_bool : freshRefInEnvBool r env = true :=
      (freshRefInEnv_iff_freshRefInEnvBool r env).mp hfresh
    have hr_fresh : freshRef r env.pathEnv :=
      freshRefBool_implies_freshRef r env.pathEnv (freshRefInEnvBool_implies_freshRefBool r env hfresh_bool)
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
    refine ⟨env', lenv, retTypes, rmap, rfl, ?_,
            stackSafe_heap_alloc env.enumEnv m.stack m.frame.returnInfo m.heap v hss hwt.heap_loc_bound⟩
    exact {
      env_wf := ⟨hpe_wf, hse_wf, hwt.env_wf.varEnv_wf⟩
      enumEnv_consistent := hwt.enumEnv_consistent
      enum_qualified_nodup := hwt.enum_qualified_nodup
      enum_names_nodup := hwt.enum_names_nodup
      enum_variant_nodup := hwt.enum_variant_nodup
      enum_fields_nodup := hwt.enum_fields_nodup
      defaultValues_typed := hwt.defaultValues_typed
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
        intro r' loc path hr'_tracked hrmap
        have hr'_orig : r' ∈ env.pathEnv.refs := hgc_refs ▸ hr'_tracked
        have hlive := hwt.rmap_live r' loc path hr'_orig hrmap
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
          (hwt.rmap_paths r1 r2 hr1_orig hr2_orig p hp_orig)
          (fun loc path hrmap => hwt.rmap_live r2 loc path hr2_orig hrmap)
          hwt.heap_loc_bound
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
            (hwt.rmap_live v' loc_v path_v hv_orig hrmap))
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
        have hr'_tracked : r' ∈ env.pathEnv.refs := by
          rcases hold_cond with ⟨x', bk, ms', hvar'⟩ | ⟨s', bk, hsite'⟩
          · exact hwt.varEnv_refs_in_pathEnv x' bt r' bk ms' hvar'
          · exact hwt.siteEnv_refs_in_pathEnv s' bt r' bk hsite'
        have hlt := hwt.heap_loc_bound loc (readRef_implies_read m.heap loc path
          (hwt.rmap_live r' loc path hr'_tracked hrmap))
        have hne : loc ≠ m.heap.nextLoc := by intro h; subst h; exact Nat.lt_irrefl _ hlt
        rw [heap_alloc_preserves_readRef m.heap v loc path hne]
        exact ⟨val, hread, hht⟩
      funEnv_sig_consistent := hwt.funEnv_sig_consistent
      refs_tracked_mapped := by
        intro ref href
        rw [hgc_refs] at href
        exact hwt.refs_tracked_mapped ref href
      lenv_labels_in_blocks := hwt.lenv_labels_in_blocks
      has_return_info := hwt.has_return_info
      varStore_locs_bound := by
        intro y loc_y hvar
        by_cases heq : y = x
        · subst heq; rw [lookup_insert_same] at hvar
          simp only [Option.some.injEq] at hvar; rw [← hvar]; simp [Heap.alloc]
        · rw [lookup_insert_ne _ x y _ heq] at hvar
          have hlt := hwt.varStore_locs_bound y loc_y hvar
          exact Nat.lt_trans hlt (by simp [Heap.alloc])
    }

private theorem preservation_assign_invalid (m m' : Machine) (env : TypeEnv) (lenv : LabelEnv)
    (retTypes : List ParamType) (rmap : RefMap)
    (hwt : WellTypedState m env lenv retTypes rmap)
    (hss : StackSafe env.enumEnv m.stack m.frame.returnInfo m.heap retTypes)
    (x : Var) (a : Site) (cont : Stmt) (τ τ' : MoveType)
    (hvar : lookup env.varEnv x = some (.invalidVar, τ, .mutable))
    (hsite : lookup env.siteEnv a = some τ')
    (hcompat : MoveType.compatible τ τ')
    (hcont : typecheck_stmt lenv
      {env with varEnv := update env.varEnv x (.validVar, τ', .mutable)
                siteEnv := delete env.siteEnv a} cont retTypes)
    (hstmt : m.frame.stmt = .assign x a cont)
    (hstep : step (.running m) = .running m') :
    ∃ env' lenv' retTypes' rmap',
      env'.enumEnv = env.enumEnv ∧ WellTypedState m' env' lenv' retTypes' rmap' ∧
      StackSafe env.enumEnv m'.stack m'.frame.returnInfo m'.heap retTypes' := by
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
          lenv, retTypes, rmap, rfl, ?_,
          stackSafe_heap_alloc env.enumEnv m.stack m.frame.returnInfo m.heap v hss hwt.heap_loc_bound⟩
  exact {
    env_wf := ⟨hwt.env_wf.pathEnv_wf,
               SiteEnv.delete_refs_not_root env.siteEnv a hwt.env_wf.siteEnv_wf,
               VarEnv.update_refs_not_root env.varEnv x (.validVar, τ', .mutable)
                 hwt.env_wf.varEnv_wf hfresh_τ'⟩
    enumEnv_consistent := hwt.enumEnv_consistent
    enum_qualified_nodup := hwt.enum_qualified_nodup
    enum_names_nodup := hwt.enum_names_nodup
    enum_variant_nodup := hwt.enum_variant_nodup
    enum_fields_nodup := hwt.enum_fields_nodup
    defaultValues_typed := hwt.defaultValues_typed
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
      intro r loc path hr_tracked hrmap
      have hlive := hwt.rmap_live r loc path hr_tracked hrmap
      have hlt := hwt.heap_loc_bound loc (readRef_implies_read m.heap loc path hlive)
      have hne : loc ≠ m.heap.nextLoc := by intro h; subst h; exact Nat.lt_irrefl _ hlt
      rw [heap_alloc_preserves_readRef m.heap v loc path hne]; exact hlive
    rmap_paths := by
      intro r1 r2 hr1 hr2 p hp
      exact pathReflectedInHeap_heap_alloc rmap m.heap v r1 r2 p
        (hwt.rmap_paths r1 r2 hr1 hr2 p hp)
        (fun loc path hrmap => hwt.rmap_live r2 loc path hr2 hrmap)
        hwt.heap_loc_bound
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
          (hwt.rmap_live v' loc_v path_v hv_mem hrmap))
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
      have hr'_tracked : r' ∈ env.pathEnv.refs := by
        rcases hold_cond with ⟨x', bk, ms', hvar'⟩ | ⟨s', bk, hsite'⟩
        · exact hwt.varEnv_refs_in_pathEnv x' bt r' bk ms' hvar'
        · exact hwt.siteEnv_refs_in_pathEnv s' bt r' bk hsite'
      have hlt := hwt.heap_loc_bound loc (readRef_implies_read m.heap loc path
        (hwt.rmap_live r' loc path hr'_tracked hrmap))
      have hne : loc ≠ m.heap.nextLoc := by intro h; subst h; exact Nat.lt_irrefl _ hlt
      rw [heap_alloc_preserves_readRef m.heap v loc path hne]
      exact ⟨val, hread, hht⟩
    funEnv_sig_consistent := hwt.funEnv_sig_consistent
    refs_tracked_mapped := hwt.refs_tracked_mapped
    lenv_labels_in_blocks := hwt.lenv_labels_in_blocks
    has_return_info := hwt.has_return_info
    varStore_locs_bound := by
      intro y loc_y hvar
      by_cases heq : y = x
      · subst heq; rw [lookup_insert_same] at hvar
        simp only [Option.some.injEq] at hvar; rw [← hvar]; simp [Heap.alloc]
      · rw [lookup_insert_ne _ x y _ heq] at hvar
        have hlt := hwt.varStore_locs_bound y loc_y hvar
        exact Nat.lt_trans hlt (by simp [Heap.alloc])
  }

private theorem preservation_assign_valid_ref (m m' : Machine) (env : TypeEnv) (lenv : LabelEnv)
    (retTypes : List ParamType) (rmap : RefMap)
    (hwt : WellTypedState m env lenv retTypes rmap)
    (hss : StackSafe env.enumEnv m.stack m.frame.returnInfo m.heap retTypes)
    (x : Var) (a : Site) (cont : Stmt)
    (τ_old : BasicMoveType) (r_old : Aref) (bk_old : BorrowingKind) (τ' : MoveType) (ms : Mut)
    (_ : LE.le .mutable ms)
    (hvar : lookup env.varEnv x = some (.validVar, .ref τ_old r_old bk_old, ms))
    (hsite : lookup env.siteEnv a = some τ')
    (hcont : typecheck_stmt lenv
      {env with varEnv := update env.varEnv x (.validVar, τ', ms)
                siteEnv := delete env.siteEnv a
                pathEnv := delete_ref_node env.pathEnv r_old}
      cont retTypes)
    (hstmt : m.frame.stmt = .assign x a cont)
    (hstep : step (.running m) = .running m') :
    ∃ env' lenv' retTypes' rmap',
      env'.enumEnv = env.enumEnv ∧ WellTypedState m' env' lenv' retTypes' rmap' ∧
      StackSafe env.enumEnv m'.stack m'.frame.returnInfo m'.heap retTypes' := by
  -- Extract runtime values
  obtain ⟨v, hv, hmatch⟩ := hwt.site_consistent a τ' hsite
  have hrs : readSite m a = some v := hv
  simp only [step, hstmt, hrs, ExecState.running.injEq] at hstep; subst hstep
  -- r_old is not root (from varEnv_wf)
  have hr_not_root : r_old ≠ .root :=
    VarEnv.lookup_type_refs_not_root env.varEnv x .validVar (.ref τ_old r_old bk_old) ms
      hwt.env_wf.varEnv_wf hvar
  -- τ' refs are not root (from siteEnv_wf)
  have hfresh_τ' : moveTypeRefNotRoot τ' := hwt.env_wf.siteEnv_wf a τ' hsite
  -- Abbreviations
  let pe' := delete_ref_node env.pathEnv r_old
  let ve' := update env.varEnv x (.validVar, τ', ms)
  let se' := delete env.siteEnv a
  let env' : TypeEnv := {env with varEnv := ve', siteEnv := se', pathEnv := pe'}
  have hsite_a := hsite
  have hlive_old := hwt.live_refs_unique
  have hvar_x := hvar
  refine ⟨env', lenv, retTypes, rmap, rfl, ?_,
          stackSafe_heap_alloc env.enumEnv m.stack m.frame.returnInfo m.heap v hss hwt.heap_loc_bound⟩
  exact {
    env_wf := ⟨delete_ref_node_wellformed env.pathEnv r_old hwt.env_wf.pathEnv_wf hr_not_root,
               SiteEnv.delete_refs_not_root env.siteEnv a hwt.env_wf.siteEnv_wf,
               VarEnv.update_refs_not_root env.varEnv x (.validVar, τ', ms)
                 hwt.env_wf.varEnv_wf hfresh_τ'⟩
    enumEnv_consistent := hwt.enumEnv_consistent
    enum_qualified_nodup := hwt.enum_qualified_nodup
    enum_names_nodup := hwt.enum_names_nodup
    enum_variant_nodup := hwt.enum_variant_nodup
    enum_fields_nodup := hwt.enum_fields_nodup
    defaultValues_typed := hwt.defaultValues_typed
    stmt_typed := hcont
    var_consistent := by
      intro y isv τy ms' hvy
      have hvy' : lookup (insert env.varEnv x (.validVar, τ', ms)) y =
          some (isv, τy, ms') := hvy
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
      have hne : s ≠ a := by
        intro h; subst h; rw [lookup_delete_same] at hl; simp at hl
      rw [lookup_delete_ne env.siteEnv a s hne] at hl
      exact hwt.site_consistent s τs hl
    rmap_live := by
      intro r loc path hr_tracked hrmap
      have hr_tracked' : r ∈ (delete_ref_node env.pathEnv r_old).refs := hr_tracked
      simp only [delete_ref_node_refs, List.mem_filter, decide_eq_true_eq] at hr_tracked'
      have hlive := hwt.rmap_live r loc path hr_tracked'.1 hrmap
      have hlt := hwt.heap_loc_bound loc (readRef_implies_read m.heap loc path hlive)
      have hne : loc ≠ m.heap.nextLoc := by intro h; subst h; exact Nat.lt_irrefl _ hlt
      rw [heap_alloc_preserves_readRef m.heap v loc path hne]; exact hlive
    rmap_paths := by
      intro r1 r2 hr1 hr2 p hp
      have hr1' : r1 ∈ (delete_ref_node env.pathEnv r_old).refs := hr1
      have hr2' : r2 ∈ (delete_ref_node env.pathEnv r_old).refs := hr2
      simp only [delete_ref_node_refs, List.mem_filter, decide_eq_true_eq] at hr1' hr2'
      obtain ⟨hr1_mem, hr1_ne⟩ := hr1'
      obtain ⟨hr2_mem, hr2_ne⟩ := hr2'
      have hp' : interpret_regex ((delete_ref_node env.pathEnv r_old).paths (r1, r2)) p := hp
      rw [delete_ref_node_paths_not_involving_r env.pathEnv r_old r1 r2 hr1_ne hr2_ne] at hp'
      exact pathReflectedInHeap_heap_alloc rmap m.heap v r1 r2 p
        (hwt.rmap_paths r1 r2 hr1_mem hr2_mem p hp')
        (fun loc path hrmap => hwt.rmap_live r2 loc path hr2_mem hrmap)
        hwt.heap_loc_bound
    varEnv_refs_in_pathEnv := by
      intro y bt r' bk ms' hvy
      have hvy' : lookup (insert env.varEnv x (.validVar, τ', ms)) y =
          some (.validVar, .ref bt r' bk, ms') := hvy
      show r' ∈ (delete_ref_node env.pathEnv r_old).refs
      by_cases heq : y = x
      · subst heq; rw [lookup_insert_same] at hvy'
        have hτ : τ' = .ref bt r' bk := by
          simp only [Option.some.injEq, Prod.mk.injEq] at hvy'; exact hvy'.2.1
        rw [hτ] at hsite_a
        have hr'_ne : r' ≠ r_old := by
          intro heq; rw [heq] at hsite_a
          exact (hlive_old r_old).1 y τ_old bk_old ms a bt bk hvar_x hsite_a
        have hr'_in := hwt.siteEnv_refs_in_pathEnv a bt r' bk hsite_a
        simp only [delete_ref_node_refs, List.mem_filter, decide_eq_true_eq]
        exact ⟨hr'_in, hr'_ne⟩
      · rw [lookup_insert_ne _ x y _ heq] at hvy'
        have hr'_in := hwt.varEnv_refs_in_pathEnv y bt r' bk ms' hvy'
        have hr'_ne : r' ≠ r_old := by
          intro hr_eq; rw [hr_eq] at hvy'
          exact (hlive_old r_old).2.2 x y τ_old bt bk_old bk ms ms' (Ne.symm heq) hvar_x hvy'
        simp only [delete_ref_node_refs, List.mem_filter, decide_eq_true_eq]
        exact ⟨hr'_in, hr'_ne⟩
    siteEnv_refs_in_pathEnv := by
      intro s' bt r' bk hl
      have hne : s' ≠ a := by
        intro h; subst h; rw [lookup_delete_same] at hl; simp at hl
      rw [lookup_delete_ne env.siteEnv a s' hne] at hl
      show r' ∈ (delete_ref_node env.pathEnv r_old).refs
      have hr'_in := hwt.siteEnv_refs_in_pathEnv s' bt r' bk hl
      have hr'_ne : r' ≠ r_old := by
        intro heq; rw [heq] at hl
        exact (hlive_old r_old).1 x τ_old bk_old ms s' bt bk hvar_x hl
      simp only [delete_ref_node_refs, List.mem_filter, decide_eq_true_eq]
      exact ⟨hr'_in, hr'_ne⟩
    live_refs_unique := by
      intro r'
      refine ⟨fun x' bt bk ms' s' bt' bk' hvar' hs' => ?_,
              fun s1 s2 bt1 bt2 bk1 bk2 hne hs1 hs2 => ?_,
              fun x1 x2 bt1 bt2 bk1 bk2 ms1 ms2 hne hx1 hx2 => ?_⟩
      · -- var-site
        have hne_a : s' ≠ a := by
          intro h; subst h; rw [lookup_delete_same] at hs'; simp at hs'
        rw [lookup_delete_ne env.siteEnv a s' hne_a] at hs'
        have hvar'' : lookup (insert env.varEnv x (.validVar, τ', ms)) x' =
            some (.validVar, .ref bt r' bk, ms') := hvar'
        by_cases heq : x' = x
        · subst heq; rw [lookup_insert_same] at hvar''
          have hτ : τ' = .ref bt r' bk := by
            simp only [Option.some.injEq, Prod.mk.injEq] at hvar''; exact hvar''.2.1
          rw [hτ] at hsite_a
          -- site a and s' both have ref r' → but a is deleted, so reduce to site-site
          exact (hlive_old r').2.1 a s' bt bt' bk bk' (Ne.symm hne_a) hsite_a hs'
        · rw [lookup_insert_ne _ x x' _ heq] at hvar''
          exact (hlive_old r').1 x' bt bk ms' s' bt' bk' hvar'' hs'
      · -- site-site
        have hne1 : s1 ≠ a := by
          intro h; subst h; rw [lookup_delete_same] at hs1; simp at hs1
        have hne2 : s2 ≠ a := by
          intro h; subst h; rw [lookup_delete_same] at hs2; simp at hs2
        rw [lookup_delete_ne env.siteEnv a s1 hne1] at hs1
        rw [lookup_delete_ne env.siteEnv a s2 hne2] at hs2
        exact (hlive_old r').2.1 s1 s2 bt1 bt2 bk1 bk2 hne hs1 hs2
      · -- var-var
        have hx1' : lookup (insert env.varEnv x (.validVar, τ', ms)) x1 =
            some (.validVar, .ref bt1 r' bk1, ms1) := hx1
        have hx2' : lookup (insert env.varEnv x (.validVar, τ', ms)) x2 =
            some (.validVar, .ref bt2 r' bk2, ms2) := hx2
        by_cases heq1 : x1 = x
        · rw [heq1, lookup_insert_same] at hx1'
          have hτ : τ' = .ref bt1 r' bk1 := by
            simp only [Option.some.injEq, Prod.mk.injEq] at hx1'; exact hx1'.2.1
          rw [hτ] at hsite_a
          have hne2 : x2 ≠ x := by rw [← heq1]; exact hne.symm
          rw [lookup_insert_ne _ x x2 _ hne2] at hx2'
          -- x2 valid with ref r', site a has ref r' → var-site contradiction
          exact (hlive_old r').1 x2 bt2 bk2 ms2 a bt1 bk1 hx2' hsite_a
        · by_cases heq2 : x2 = x
          · rw [heq2, lookup_insert_same] at hx2'
            have hτ : τ' = .ref bt2 r' bk2 := by
              simp only [Option.some.injEq, Prod.mk.injEq] at hx2'; exact hx2'.2.1
            rw [hτ] at hsite_a
            rw [lookup_insert_ne _ x x1 _ heq1] at hx1'
            exact (hlive_old r').1 x1 bt1 bk1 ms1 a bt2 bk2 hx1' hsite_a
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
    no_paths_to_root := no_paths_to_root_delete_ref_node' hwt r_old hr_not_root
    root_path_coherence := by
      -- pathEnv changes via delete_ref_node; varStore(x) → fresh alloc location
      intro v' y rest hv_mem hp loc_v path_v hrmap loc_y hloc heq
      -- v' ∈ pe'.refs means v' ∈ env.pathEnv.refs and v' ≠ r_old
      have hv_mem' : v' ∈ (delete_ref_node env.pathEnv r_old).refs := hv_mem
      simp only [delete_ref_node_refs, List.mem_filter, decide_eq_true_eq] at hv_mem'
      have hv_orig := hv_mem'.1
      have hv_ne := hv_mem'.2
      -- pe'.paths(.root, v') = env.pathEnv.paths(.root, v') (root ≠ r_old, v' ≠ r_old)
      have hroot_ne : Aref.root ≠ r_old := Ne.symm hr_not_root
      have hp' : interpret_regex ((delete_ref_node env.pathEnv r_old).paths (.root, v')) (.root_to_var y :: rest) := hp
      have hp_orig : interpret_regex (env.pathEnv.paths (.root, v')) (.root_to_var y :: rest) := by
        rw [← delete_ref_node_paths_not_involving_r env.pathEnv r_old .root v' hroot_ne hv_ne]
        exact hp'
      by_cases heqx : y = x
      · subst heqx
        simp only [lookup_insert_same, Option.some.injEq] at hloc
        have halloc_eq : (m.heap.alloc v).2 = m.heap.nextLoc := rfl
        have hlt := hwt.heap_loc_bound loc_v (readRef_implies_read m.heap loc_v path_v
          (hwt.rmap_live v' loc_v path_v hv_orig hrmap))
        rw [← hloc, halloc_eq] at heq
        exact absurd heq (Nat.ne_of_lt hlt)
      · rw [lookup_insert_ne _ x y _ heqx] at hloc
        exact hwt.root_path_coherence v' y rest hv_orig hp_orig loc_v path_v hrmap loc_y hloc heq
    paths_from_non_member_empty :=
      delete_ref_node_paths_from_non_member env.pathEnv r_old hwt.paths_from_non_member_empty
    paths_to_non_member_empty :=
      delete_ref_node_paths_to_non_member env.pathEnv r_old hwt.paths_to_non_member_empty
    self_loop_only_empty := by
      intro u p hp
      have hp' : interpret_regex ((delete_ref_node env.pathEnv r_old).paths (u, u)) p := hp
      simp only [delete_ref_node] at hp'
      by_cases hu : u = r_old
      · subst hu; rw [if_pos ⟨rfl, rfl⟩] at hp'; exact hp'
      · simp only [hu, false_or, ↓reduceIte] at hp'
        exact hwt.self_loop_only_empty u p hp'
    rmap_has_type := by
      intro r' bt loc path hrmap hcond
      -- Reduce new env condition to old env condition
      have hold_cond : ((∃ x' bk ms', lookup env.varEnv x' = some (.validVar, .ref bt r' bk, ms')) ∨
          (∃ s' bk, lookup env.siteEnv s' = some (.ref bt r' bk))) := by
        rcases hcond with ⟨y, bk, ms', hvy⟩ | ⟨s', bk, hsite'⟩
        · -- varEnv: y has validVar in updated env
          have hvy' : lookup (insert env.varEnv x (.validVar, τ', ms)) y =
              some (.validVar, .ref bt r' bk, ms') := hvy
          by_cases heq : y = x
          · subst heq; rw [lookup_insert_same] at hvy'
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
      have hr'_tracked : r' ∈ env.pathEnv.refs := by
        rcases hold_cond with ⟨x', bk, ms', hvar'⟩ | ⟨s', bk, hsite'⟩
        · exact hwt.varEnv_refs_in_pathEnv x' bt r' bk ms' hvar'
        · exact hwt.siteEnv_refs_in_pathEnv s' bt r' bk hsite'
      have hlt := hwt.heap_loc_bound loc (readRef_implies_read m.heap loc path
        (hwt.rmap_live r' loc path hr'_tracked hrmap))
      have hne : loc ≠ m.heap.nextLoc := by intro h; subst h; exact Nat.lt_irrefl _ hlt
      rw [heap_alloc_preserves_readRef m.heap v loc path hne]
      exact ⟨val, hread, hht⟩
    funEnv_sig_consistent := hwt.funEnv_sig_consistent
    refs_tracked_mapped := by
      intro ref href
      have href' : ref ∈ (delete_ref_node env.pathEnv r_old).refs := href
      simp only [delete_ref_node_refs, List.mem_filter, decide_eq_true_eq] at href'
      exact hwt.refs_tracked_mapped ref href'.1
    lenv_labels_in_blocks := hwt.lenv_labels_in_blocks
    has_return_info := hwt.has_return_info
    varStore_locs_bound := by
      intro y loc_y hvar'
      by_cases heq : y = x
      · subst heq; rw [lookup_insert_same] at hvar'
        simp only [Option.some.injEq] at hvar'; rw [← hvar']; simp [Heap.alloc]
      · rw [lookup_insert_ne _ x y _ heq] at hvar'
        have hlt := hwt.varStore_locs_bound y loc_y hvar'
        exact Nat.lt_trans hlt (by simp [Heap.alloc])
  }

/-- Preservation for freeze: converts a (possibly mutable) reference to an immutable one.
    At runtime this is a no-op (value copy). The typing env deletes the old site, inserts a new
    site with a fresh ref r', and applies consume_ref_transfer to transfer paths from r to r'. -/
private theorem preservation_freeze (m m' : Machine) (env : TypeEnv) (lenv : LabelEnv)
    (retTypes : List ParamType) (rmap : RefMap)
    (hwt : WellTypedState m env lenv retTypes rmap)
    (hss : StackSafe env.enumEnv m.stack m.frame.returnInfo m.heap retTypes)
    (s : Site) (src : Site) (cont : Stmt)
    (hstmt : m.frame.stmt = .letBind s (.freeze src) cont)
    (hstep : step (.running m) = .running m') :
    ∃ env' lenv' retTypes' rmap',
      env'.enumEnv = env.enumEnv ∧ WellTypedState m' env' lenv' retTypes' rmap' ∧
      StackSafe env.enumEnv m'.stack m'.frame.returnInfo m'.heap retTypes' := by
  -- 1. Invert typing
  obtain ⟨τ, r, r', isBor, hlookup, hfresh, hcont⟩ :=
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
  have hlive_r : m.heap.readRef loc path ≠ none := hwt.rmap_live r loc path hr_in_refs hrmap
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
          lenv, retTypes, rmap', rfl, ?_, hss⟩
  exact {
    env_wf := TypeEnv.delete_insert_pathEnv_wf env src s (.ref τ r' .siteBorrowImm) pe' hwt.env_wf
      (consume_ref_transfer_wellformed env.pathEnv r r' hwt.env_wf.pathEnv_wf
        hr_not_root hr'_fresh_pe hfresh.2.2.2) hr'_not_root
    enumEnv_consistent := hwt.enumEnv_consistent
    enum_qualified_nodup := hwt.enum_qualified_nodup
    enum_names_nodup := hwt.enum_names_nodup
    enum_variant_nodup := hwt.enum_variant_nodup
    enum_fields_nodup := hwt.enum_fields_nodup
    defaultValues_typed := hwt.defaultValues_typed
    stmt_typed := hcont
    var_consistent := var_consistent_extend_rmap_fresh hwt r' loc path hfresh
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
        have ⟨v', hv', hm⟩ := site_consistent_old_entry_extend_rmap hwt r' loc path hfresh s' τ' hl
        exact ⟨v', by rw [lookup_insert_ne _ s s' _ heq]; exact hv', hm⟩
    rmap_live := rmap_live_extend_fresh hwt r' loc path hlive_r
        (by intro ref href
            rw [hpe_refs] at href
            simp only [List.mem_filter, decide_eq_true_eq, List.mem_cons] at href
            exact href.1)
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
    funEnv_sig_consistent := hwt.funEnv_sig_consistent
    refs_tracked_mapped := by
      intro ref href
      rw [hpe_refs] at href
      simp only [List.mem_filter, decide_eq_true_eq, List.mem_cons] at href
      obtain ⟨href_mem, href_ne_r⟩ := href
      rcases href_mem with heq | href_old
      · rw [heq]; right
        show (if r' = r' then some (loc, path) else rmap.map r') ≠ none
        simp
      · cases hwt.refs_tracked_mapped ref href_old with
        | inl h => exact Or.inl h
        | inr h =>
          right
          show (if ref = r' then some (loc, path) else rmap.map ref) ≠ none
          have hne : ref ≠ r' := fun heq => hr'_fresh_pe (heq ▸ href_old)
          simp [hne]; exact h
    lenv_labels_in_blocks := hwt.lenv_labels_in_blocks
    has_return_info := hwt.has_return_info
    varStore_locs_bound := hwt.varStore_locs_bound
  }

-- ============================================================
-- Part 8a-assign-overwrite: Preservation for var_assign_overwrite_basic
-- ============================================================

private theorem preservation_assign_overwrite_basic (m m' : Machine) (env : TypeEnv) (lenv : LabelEnv)
    (retTypes : List ParamType) (rmap : RefMap)
    (hwt : WellTypedState m env lenv retTypes rmap)
    (hss : StackSafe env.enumEnv m.stack m.frame.returnInfo m.heap retTypes)
    (x : Var) (a : Site) (cont : Stmt) (isv : IsValid) (τ : BasicMoveType)
    (hvar : lookup env.varEnv x = some (isv, .basic τ, .mutable))
    (hsite : lookup env.siteEnv a = some (.basic τ))
    (hcont : typecheck_stmt lenv
      {env with varEnv := update env.varEnv x (.validVar, .basic τ, .mutable)
                siteEnv := delete env.siteEnv a} cont retTypes)
    (hstmt : m.frame.stmt = .assign x a cont)
    (hstep : step (.running m) = .running m') :
    ∃ env' lenv' retTypes' rmap',
      env'.enumEnv = env.enumEnv ∧ WellTypedState m' env' lenv' retTypes' rmap' ∧
      StackSafe env.enumEnv m'.stack m'.frame.returnInfo m'.heap retTypes' := by
  -- Extract runtime value from site_consistent
  obtain ⟨v, hv, hmatch⟩ := hwt.site_consistent a (.basic τ) hsite
  have hrs : readSite m a = some v := hv
  simp only [step, hstmt, hrs, ExecState.running.injEq] at hstep; subst hstep
  -- Capture site lookup for use in struct blocks
  have hsite_a := hsite
  have hlive_old := hwt.live_refs_unique
  refine ⟨{env with varEnv := update env.varEnv x (.validVar, .basic τ, .mutable),
                     siteEnv := delete env.siteEnv a},
          lenv, retTypes, rmap, rfl, ?_,
          stackSafe_heap_alloc env.enumEnv m.stack m.frame.returnInfo m.heap v hss hwt.heap_loc_bound⟩
  exact {
    env_wf := ⟨hwt.env_wf.pathEnv_wf,
               SiteEnv.delete_refs_not_root env.siteEnv a hwt.env_wf.siteEnv_wf,
               VarEnv.update_refs_not_root env.varEnv x (.validVar, .basic τ, .mutable)
                 hwt.env_wf.varEnv_wf (by simp)⟩
    enumEnv_consistent := hwt.enumEnv_consistent
    enum_qualified_nodup := hwt.enum_qualified_nodup
    enum_names_nodup := hwt.enum_names_nodup
    enum_variant_nodup := hwt.enum_variant_nodup
    enum_fields_nodup := hwt.enum_fields_nodup
    defaultValues_typed := hwt.defaultValues_typed
    stmt_typed := hcont
    var_consistent := by
      intro y isv_y τy ms hvy
      have hvy' : lookup (insert env.varEnv x (.validVar, .basic τ, .mutable)) y =
          some (isv_y, τy, ms) := hvy
      by_cases heq : y = x
      · subst heq
        rw [lookup_insert_same] at hvy'
        have hisv : isv_y = .validVar := (congrArg Prod.fst (Option.some.inj hvy')).symm
        subst hisv
        have hτy : τy = .basic τ :=
          (congrArg Prod.fst (Prod.mk.inj (Option.some.inj hvy')).2).symm
        subst hτy
        exact ⟨(m.heap.alloc v).2, v, lookup_insert_same _ _ _,
               heap_alloc_read_new m.heap v, hmatch⟩
      · rw [lookup_insert_ne _ x y _ heq] at hvy'
        have hold := hwt.var_consistent y isv_y τy ms hvy'
        have hne_vs : lookup (insert m.frame.varStore x (some (m.heap.alloc v).2)) y =
            lookup m.frame.varStore y := lookup_insert_ne _ x y _ heq
        cases isv_y with
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
      intro r loc path hr_tracked hrmap
      have hlive := hwt.rmap_live r loc path hr_tracked hrmap
      have hlt := hwt.heap_loc_bound loc (readRef_implies_read m.heap loc path hlive)
      have hne : loc ≠ m.heap.nextLoc := by intro h; subst h; exact Nat.lt_irrefl _ hlt
      rw [heap_alloc_preserves_readRef m.heap v loc path hne]; exact hlive
    rmap_paths := by
      intro r1 r2 hr1 hr2 p hp
      exact pathReflectedInHeap_heap_alloc rmap m.heap v r1 r2 p
        (hwt.rmap_paths r1 r2 hr1 hr2 p hp)
        (fun loc path hrmap => hwt.rmap_live r2 loc path hr2 hrmap)
        hwt.heap_loc_bound
    varEnv_refs_in_pathEnv := by
      intro y bt r' bk ms' hvy
      have hvy' : lookup (insert env.varEnv x (.validVar, .basic τ, .mutable)) y =
          some (.validVar, .ref bt r' bk, ms') := hvy
      by_cases heq : y = x
      · subst heq; rw [lookup_insert_same] at hvy'
        simp only [Option.some.injEq, Prod.mk.injEq] at hvy'
        exact absurd hvy'.2.1 (by simp)
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
      · -- var-site
        have hne_a : s' ≠ a := by
          intro h; subst h; rw [lookup_delete_same] at hs'; simp at hs'
        rw [lookup_delete_ne env.siteEnv a s' hne_a] at hs'
        have hvar' : lookup (insert env.varEnv x (.validVar, .basic τ, .mutable)) x' =
            some (.validVar, .ref bt r' bk, ms') := hvar_x'
        by_cases heq : x' = x
        · subst heq; rw [lookup_insert_same] at hvar'
          simp only [Option.some.injEq, Prod.mk.injEq] at hvar'
          exact absurd hvar'.2.1 (by simp)
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
        have hx1' : lookup (insert env.varEnv x (.validVar, .basic τ, .mutable)) x1 =
            some (.validVar, .ref bt1 r' bk1, ms1) := hx1
        have hx2' : lookup (insert env.varEnv x (.validVar, .basic τ, .mutable)) x2 =
            some (.validVar, .ref bt2 r' bk2, ms2) := hx2
        by_cases heq1 : x1 = x
        · subst heq1; rw [lookup_insert_same] at hx1'
          simp only [Option.some.injEq, Prod.mk.injEq] at hx1'
          exact absurd hx1'.2.1 (by simp)
        · by_cases heq2 : x2 = x
          · subst heq2; rw [lookup_insert_same] at hx2'
            simp only [Option.some.injEq, Prod.mk.injEq] at hx2'
            exact absurd hx2'.2.1 (by simp)
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
      intro v' y rest hv_mem hp loc_v path_v hrmap loc_y hloc heq
      by_cases heqx : y = x
      · subst heqx
        simp only [lookup_insert_same, Option.some.injEq] at hloc
        have halloc_eq : (m.heap.alloc v).2 = m.heap.nextLoc := rfl
        have hlt := hwt.heap_loc_bound loc_v (readRef_implies_read m.heap loc_v path_v
          (hwt.rmap_live v' loc_v path_v hv_mem hrmap))
        rw [← hloc, halloc_eq] at heq
        exact absurd heq (Nat.ne_of_lt hlt)
      · rw [lookup_insert_ne _ x y _ heqx] at hloc
        exact hwt.root_path_coherence v' y rest hv_mem hp loc_v path_v hrmap loc_y hloc heq
    paths_from_non_member_empty := hwt.paths_from_non_member_empty
    paths_to_non_member_empty := hwt.paths_to_non_member_empty
    self_loop_only_empty := hwt.self_loop_only_empty
    rmap_has_type := by
      intro r' bt loc path hrmap hcond
      have hold_cond : ((∃ x' bk ms', lookup env.varEnv x' = some (.validVar, .ref bt r' bk, ms')) ∨
          (∃ s' bk, lookup env.siteEnv s' = some (.ref bt r' bk))) := by
        rcases hcond with ⟨y, bk, ms', hvy⟩ | ⟨s', bk, hsite'⟩
        · have hvy' : lookup (insert env.varEnv x (.validVar, .basic τ, .mutable)) y =
              some (.validVar, .ref bt r' bk, ms') := hvy
          by_cases heq : y = x
          · subst heq; rw [lookup_insert_same] at hvy'
            simp only [Option.some.injEq, Prod.mk.injEq] at hvy'
            exact absurd hvy'.2.1 (by simp)
          · rw [lookup_insert_ne _ x y _ heq] at hvy'
            exact .inl ⟨y, bk, ms', hvy'⟩
        · have hne : s' ≠ a := by
            intro h; subst h; rw [lookup_delete_same] at hsite'; simp at hsite'
          rw [lookup_delete_ne env.siteEnv a s' hne] at hsite'
          exact .inr ⟨s', bk, hsite'⟩
      obtain ⟨val, hread, hht⟩ := hwt.rmap_has_type r' bt loc path hrmap hold_cond
      have hr'_tracked : r' ∈ env.pathEnv.refs := by
        rcases hold_cond with ⟨x', bk, ms', hvar'⟩ | ⟨s', bk, hsite'⟩
        · exact hwt.varEnv_refs_in_pathEnv x' bt r' bk ms' hvar'
        · exact hwt.siteEnv_refs_in_pathEnv s' bt r' bk hsite'
      have hlt := hwt.heap_loc_bound loc (readRef_implies_read m.heap loc path
        (hwt.rmap_live r' loc path hr'_tracked hrmap))
      have hne : loc ≠ m.heap.nextLoc := by intro h; subst h; exact Nat.lt_irrefl _ hlt
      rw [heap_alloc_preserves_readRef m.heap v loc path hne]
      exact ⟨val, hread, hht⟩
    funEnv_sig_consistent := hwt.funEnv_sig_consistent
    refs_tracked_mapped := hwt.refs_tracked_mapped
    lenv_labels_in_blocks := hwt.lenv_labels_in_blocks
    has_return_info := hwt.has_return_info
    varStore_locs_bound := by
      intro y loc_y hvar_y
      by_cases heq : y = x
      · subst heq; rw [lookup_insert_same] at hvar_y
        simp only [Option.some.injEq] at hvar_y; rw [← hvar_y]; simp [Heap.alloc]
      · rw [lookup_insert_ne _ x y _ heq] at hvar_y
        have hlt := hwt.varStore_locs_bound y loc_y hvar_y
        exact Nat.lt_trans hlt (by simp [Heap.alloc])
  }

-- ============================================================
-- Part 8a-unpack: Preservation for unpack
-- ============================================================

private theorem preservation_unpack (m m' : Machine) (env : TypeEnv) (lenv : LabelEnv)
    (retTypes : List ParamType) (rmap : RefMap)
    (hwt : WellTypedState m env lenv retTypes rmap)
    (hss : StackSafe env.enumEnv m.stack m.frame.returnInfo m.heap retTypes)
    (fields : List (Field × Site)) (src : Site) (cont : Stmt)
    (hstmt : m.frame.stmt = .unpack fields src cont)
    (hstep : step (.running m) = .running m') :
    ∃ env' lenv' retTypes' rmap',
      env'.enumEnv = env.enumEnv ∧ WellTypedState m' env' lenv' retTypes' rmap' ∧
      StackSafe env.enumEnv m'.stack m'.frame.returnInfo m'.heap retTypes' := by
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
          lenv, retTypes, rmap, rfl, ?_, hss⟩
  exact {
    env_wf := by
      constructor
      · exact hwt.env_wf.pathEnv_wf
      · exact addFieldSites_refs_not_root fentries _ fields
              (SiteEnv.delete_refs_not_root env.siteEnv src hwt.env_wf.siteEnv_wf)
      · exact hwt.env_wf.varEnv_wf
    enumEnv_consistent := hwt.enumEnv_consistent
    enum_qualified_nodup := hwt.enum_qualified_nodup
    enum_names_nodup := hwt.enum_names_nodup
    enum_variant_nodup := hwt.enum_variant_nodup
    enum_fields_nodup := hwt.enum_fields_nodup
    defaultValues_typed := hwt.defaultValues_typed
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
    funEnv_sig_consistent := hwt.funEnv_sig_consistent
    refs_tracked_mapped := hwt.refs_tracked_mapped
    lenv_labels_in_blocks := hwt.lenv_labels_in_blocks
    has_return_info := hwt.has_return_info
    varStore_locs_bound := hwt.varStore_locs_bound
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
    (retTypes : List ParamType) (rmap : RefMap)
    (hwt : WellTypedState m env lenv retTypes rmap)
    (hss : StackSafe env.enumEnv m.stack m.frame.returnInfo m.heap retTypes)
    (label : Label)
    (hstmt : m.frame.stmt = .jump label)
    (hstep : step (.running m) = .running m') :
    ∃ env' lenv' retTypes' rmap',
      env'.enumEnv = env.enumEnv ∧ WellTypedState m' env' lenv' retTypes' rmap' ∧
      StackSafe env.enumEnv m'.stack m'.frame.returnInfo m'.heap retTypes' := by
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
    have hstmt' := typecheck_stmt_weaken lenv envL env block.body retTypes
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
    refine ⟨env, lenv, retTypes, rmap, rfl, ?_, hss⟩
    exact {
      env_wf := hwt.env_wf
      enumEnv_consistent := hwt.enumEnv_consistent
      enum_qualified_nodup := hwt.enum_qualified_nodup
      enum_names_nodup := hwt.enum_names_nodup
      enum_variant_nodup := hwt.enum_variant_nodup
      enum_fields_nodup := hwt.enum_fields_nodup
      defaultValues_typed := hwt.defaultValues_typed
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
      funEnv_sig_consistent := hwt.funEnv_sig_consistent
      refs_tracked_mapped := hwt.refs_tracked_mapped
      lenv_labels_in_blocks := hwt.lenv_labels_in_blocks
      has_return_info := hwt.has_return_info
      varStore_locs_bound := hwt.varStore_locs_bound
    }

-- ============================================================
-- Part 8a-iv: Preservation for branch
-- ============================================================

private theorem preservation_branch (m m' : Machine) (env : TypeEnv) (lenv : LabelEnv)
    (retTypes : List ParamType) (rmap : RefMap)
    (hwt : WellTypedState m env lenv retTypes rmap)
    (hss : StackSafe env.enumEnv m.stack m.frame.returnInfo m.heap retTypes)
    (c : Site) (l1 l2 : Label)
    (hstmt : m.frame.stmt = .branch c l1 l2)
    (hstep : step (.running m) = .running m') :
    ∃ env' lenv' retTypes' rmap',
      env'.enumEnv = env.enumEnv ∧ WellTypedState m' env' lenv' retTypes' rmap' ∧
      StackSafe env.enumEnv m'.stack m'.frame.returnInfo m'.heap retTypes' := by
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
        have hstmt' := typecheck_stmt_weaken lenv envL1 env' block.body retTypes
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
        refine ⟨env', lenv, retTypes, rmap, rfl, ?_, hss⟩
        exact {
          env_wf := hwf'
          enumEnv_consistent := hwt.enumEnv_consistent
          enum_qualified_nodup := hwt.enum_qualified_nodup
          enum_names_nodup := hwt.enum_names_nodup
          enum_variant_nodup := hwt.enum_variant_nodup
          enum_fields_nodup := hwt.enum_fields_nodup
          defaultValues_typed := hwt.defaultValues_typed
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
          funEnv_sig_consistent := hwt.funEnv_sig_consistent
          refs_tracked_mapped := hwt.refs_tracked_mapped
          lenv_labels_in_blocks := hwt.lenv_labels_in_blocks
          has_return_info := hwt.has_return_info
          varStore_locs_bound := hwt.varStore_locs_bound
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
        have hstmt' := typecheck_stmt_weaken lenv envL2 env' block.body retTypes
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
        refine ⟨env', lenv, retTypes, rmap, rfl, ?_, hss⟩
        exact {
          env_wf := hwf'
          enumEnv_consistent := hwt.enumEnv_consistent
          enum_qualified_nodup := hwt.enum_qualified_nodup
          enum_names_nodup := hwt.enum_names_nodup
          enum_variant_nodup := hwt.enum_variant_nodup
          enum_fields_nodup := hwt.enum_fields_nodup
          defaultValues_typed := hwt.defaultValues_typed
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
          funEnv_sig_consistent := hwt.funEnv_sig_consistent
          refs_tracked_mapped := hwt.refs_tracked_mapped
          lenv_labels_in_blocks := hwt.lenv_labels_in_blocks
          has_return_info := hwt.has_return_info
          varStore_locs_bound := hwt.varStore_locs_bound
        }

-- ============================================================
-- Part 8a2: preservation_ret
-- ============================================================

private theorem preservation_ret (m m' : Machine) (env : TypeEnv) (lenv : LabelEnv)
    (retTypes : List ParamType) (rmap : RefMap)
    (hwt : WellTypedState m env lenv retTypes rmap)
    (hss : StackSafe env.enumEnv m.stack m.frame.returnInfo m.heap retTypes)
    (sites : List Site)
    (hstmt : m.frame.stmt = .ret sites)
    (hstep : step (.running m) = .running m') :
    ∃ env' lenv' retTypes' rmap',
      env'.enumEnv = env.enumEnv ∧ WellTypedState m' env' lenv' retTypes' rmap' ∧
      StackSafe env.enumEnv m'.stack m'.frame.returnInfo m'.heap retTypes' := by
  -- 1. Simplify step; case-split on collectSiteValues
  simp only [step, hstmt] at hstep
  cases hcsv : collectSiteValues m.frame.siteStore sites with
  | none => simp [hcsv] at hstep
  | some vals =>
    simp only [hcsv] at hstep
    -- Case split on stack
    cases hstack : m.stack with
    | nil => simp [hstack] at hstep
    | cons callerFrame rest =>
      simp only [hstack] at hstep hss
      -- Case split on returnInfo
      cases hri : m.frame.returnInfo with
      | none => simp [hri] at hstep
      | some ri =>
        simp only [hri] at hstep hss
        -- Case split on bindReturnValues
        cases hbrv : bindReturnValues callerFrame.siteStore ri.resultSites vals with
        | none => simp [hbrv] at hstep
        | some newSiteStore =>
          simp only [hbrv, ExecState.running.injEq] at hstep
          subst hstep
          -- 2. Extract typing info from ret rule
          obtain ⟨htc_callee, _, _, _⟩ :=
            inv_ret (by rw [← hstmt]; exact hwt.stmt_typed)
          -- 3. Unfold StackSafe to get caller info
          unfold StackSafe at hss
          obtain ⟨cE, cL, cR, cM, hfields, hrest⟩ := hss
          have henum_eq : cE.enumEnv = env.enumEnv := hfields.1
          have henv_wf : TypeEnv.WellFormed cE := hfields.2.1
          obtain ⟨hstmt_caller, hblocks, hlenv_se, hlenv_wf, hlenv_vt,
            hlenv_vu, hlenv_fe, hlenv_lib, hcaller_has_ri,
            hfe_typed, hve_refs, hse_refs, hlru,
            hrmap_root, hno_paths_root, hroot_coh, hpfnm, hptnm, hsle,
            hiso_unmapped, hrru, hrtm, hvar_con, hsite_con, hrmap_live, hrmap_paths_f,
            hhlb, hvlb, hrmap_ht, hfe_sig, htc_caller⟩ := hfields.2.2
          -- 4. Construct extended rmap
          let rmap' := RefMap.extendWithReturns cM cE.siteEnv ri.resultSites vals
          -- 4b. Root stays unmapped in rmap' (needed early for rmap_paths proof)
          have hrmap_root' : rmap'.map .root = none :=
            RefMap.extendWithReturns_preserves_none cM cE.siteEnv ri.resultSites vals .root
              hrmap_root (fun s _ bt r bk hse => henv_wf.siteEnv_wf s (.ref bt r bk) hse)
          -- 5. Extract complex field proofs BEFORE the structure literal
          --    (to avoid the scoping gotcha: outer variables not accessible in by blocks inside exact { ... })
          -- Helper: output ref ≠ var ref (from live_refs_unique)
          have hne_output_var : ∀ (r_v : Aref), ∀ x bt bk ms,
              lookup cE.varEnv x = some (.validVar, .ref bt r_v bk, ms) →
              ∀ s ∈ ri.resultSites, ∀ bt' r' bk',
              lookup cE.siteEnv s = some (.ref bt' r' bk') → r' ≠ r_v := by
            intro r_v x bt bk ms hvar s hs bt' r' bk' hse hr'eq
            subst hr'eq; exact (hlru r').1 x bt bk ms s bt' bk' hvar hse
          -- Helper: mapped ref ≠ output ref (from result_refs_unmapped)
          have hne_mapped : ∀ r (p : Loc × List Field),
              cM.map r = some p →
              ∀ s ∈ ri.resultSites, ∀ bt r' bk,
              lookup cE.siteEnv s = some (.ref bt r' bk) → r' ≠ r := by
            intro r p hcm s hs bt r' bk hse hr'eq
            subst hr'eq; rw [hrru s bt r' bk hs hse] at hcm; exact absurd hcm (by simp)
          -- 5a. var_consistent for rmap'
          have hvar_con' : ∀ x isv τ ms,
              lookup cE.varEnv x = some (isv, τ, ms) →
              match isv with
              | .validVar => ∃ loc v,
                  lookup callerFrame.varStore x = some (some loc) ∧
                  m.heap.read loc = some v ∧ ValueMatchesType cE.enumEnv v τ rmap'
              | .invalidVar =>
                  lookup callerFrame.varStore x = some none ∨
                  ∃ loc, lookup callerFrame.varStore x = some (some loc) := by
            intro x isv τ ms hvar
            have hvc := hvar_con x isv τ ms hvar
            cases isv with
            | validVar =>
              obtain ⟨loc, v, hloc, hread, hmatch⟩ := hvc
              refine ⟨loc, v, hloc, hread, ?_⟩
              cases τ with
              | basic bt => exact hmatch
              | ref bt r bk =>
                obtain ⟨loc', path', hveq, hrmap_eq⟩ := hmatch
                exact ⟨loc', path', hveq, RefMap.extendWithReturns_preserves cM cE.siteEnv
                  ri.resultSites vals r (loc', path') hrmap_eq
                  (hne_output_var r x bt bk ms hvar)⟩
            | invalidVar => exact hvc
          -- 5b. rmap_live for rmap'
          have hrmap_live' : ∀ r loc path,
              r ∈ cE.pathEnv.refs →
              rmap'.map r = some (loc, path) → m.heap.readRef loc path ≠ none := by
            intro r loc path hr_tracked hrmap_eq
            have h_or := RefMap.extendWithReturns_values cM cE.siteEnv ri.resultSites vals
              r loc path hrmap_eq
            rcases h_or with hold | hnew
            · exact hrmap_live r loc path hr_tracked hold
            · exact returned_ref_is_live env.siteEnv m.frame.siteStore rmap m.heap
                sites retTypes vals loc path hcsv htc_callee hwt.site_consistent
                hwt.siteEnv_refs_in_pathEnv hwt.rmap_live hnew
          -- 5c. rmap_paths for rmap'
          have hrmap_paths' : ∀ r1 r2, r1 ∈ cE.pathEnv.refs → r2 ∈ cE.pathEnv.refs →
              ∀ p, interpret_regex (cE.pathEnv.paths (r1, r2)) p →
              PathReflectedInHeap rmap' m.heap r1 r2 p := by
            intro r1 r2 hr1 hr2 p hp
            by_cases heq : r1 = r2
            · -- Self-loop: p = []
              subst heq
              have hpeq : p = [] := hsle r1 p hp
              subst hpeq
              unfold PathReflectedInHeap
              cases hrm : rmap'.map r1 with
              | none => trivial
              | some pair =>
                intro _; constructor
                · simp [fieldPathOf]
                · exact hrmap_live' r1 pair.1 pair.2 hr1 hrm
            · -- r1 ≠ r2
              cases hm1 : cM.map r1 with
              | none =>
                by_cases hr1_root : r1 = .root
                · -- r1 = .root: rmap'.map .root = none → PathReflectedInHeap = True
                  subst hr1_root
                  unfold PathReflectedInHeap; rw [hrmap_root']; trivial
                · -- r1 ≠ .root: unmapped_isolated gives no paths to r1 from r2
                  have hiso := hiso_unmapped r1 hm1 hr1_root hr1
                  exact absurd hp ((hiso r2 (Ne.symm heq)).2 p)
              | some p1 =>
                cases hm2 : cM.map r2 with
                | none =>
                  by_cases hr2_root : r2 = .root
                  · -- r2 = .root: no_paths_to_root gives r1 = .root, contradicting r1 ≠ r2
                    subst hr2_root
                    have ⟨hr1_eq, _⟩ := hno_paths_root r1 p hp
                    exact absurd hr1_eq heq
                  · -- r2 ≠ .root: unmapped_isolated gives no paths from r1 to r2
                    have hiso := hiso_unmapped r2 hm2 hr2_root hr2
                    exact absurd hp ((hiso r1 heq).1 p)
                | some p2 =>
                  have hpih := hrmap_paths_f r1 r2 hr1 hr2 p hp
                  -- Annotate with rmap' so rw can find the pattern in the goal
                  have heq1 : rmap'.map r1 = some p1 :=
                    RefMap.extendWithReturns_preserves cM cE.siteEnv
                      ri.resultSites vals r1 p1 hm1 (hne_mapped r1 p1 hm1)
                  have heq2 : rmap'.map r2 = some p2 :=
                    RefMap.extendWithReturns_preserves cM cE.siteEnv
                      ri.resultSites vals r2 p2 hm2 (hne_mapped r2 p2 hm2)
                  simp only [PathReflectedInHeap] at hpih ⊢
                  rw [heq1, heq2]; rw [hm1, hm2] at hpih
                  exact hpih
          -- ReturnValsWellTyped for caller sites (needed by 5d and 5f)
          have hrvt_caller : ReturnValsWellTyped cE.enumEnv vals ri.resultSites cE.siteEnv m.heap := by
            rw [henum_eq]
            exact derive_returnValsWellTyped env.siteEnv cE.siteEnv sites ri.resultSites retTypes
              m.frame.siteStore m.heap rmap vals htc_callee htc_caller hcsv
              hwt.site_consistent
              (fun r bt loc path hrmap hcond =>
                hwt.rmap_has_type r bt loc path hrmap (Or.inr (by
                  obtain ⟨s, bk, hse⟩ := hcond
                  exact ⟨s, bk, hse⟩)))
          -- 5d. site_consistent for rmap' and newSiteStore
          have hsite_con' : ∀ s τ, lookup cE.siteEnv s = some τ →
              ∃ v, lookup newSiteStore s = some v ∧ ValueMatchesType cE.enumEnv v τ rmap' := by
            intro s τ hse
            by_cases hni : s ∈ ri.resultSites
            · exact returnVals_site_consistent cM callerFrame.siteStore cE.siteEnv
                ri.resultSites vals m.heap newSiteStore hbrv hrvt_caller
                (fun s₁ _ s₂ _ hne bt₁ bt₂ r bk₁ bk₂ hs₁ hs₂ =>
                  (hlru r).2.1 s₁ s₂ bt₁ bt₂ bk₁ bk₂ hne hs₁ hs₂)
                s hni τ hse
            · -- Non-result sites: preserved by bindReturnValues
              obtain ⟨v, hlookup, hvm⟩ := hsite_con s τ hse hni
              refine ⟨v, ?_, ?_⟩
              · rw [bindReturnValues_preserves callerFrame.siteStore ri.resultSites vals
                  newSiteStore s hbrv hni]
                exact hlookup
              · cases τ with
                | basic _ => exact hvm
                | ref bt r bk =>
                  obtain ⟨loc, path, hveq, hrmap_eq⟩ := hvm
                  have hne_site : ∀ s' ∈ ri.resultSites, ∀ bt' r' bk',
                      lookup cE.siteEnv s' = some (.ref bt' r' bk') → r' ≠ r := by
                    intro s' hs' bt' r' bk' hse' hr'eq
                    subst hr'eq
                    by_cases hsne : s = s'
                    · subst hsne; exact absurd hs' hni
                    · exact (hlru r').2.1 s s' bt bt' bk bk' hsne hse hse'
                  exact ⟨loc, path, hveq, RefMap.extendWithReturns_preserves cM cE.siteEnv
                    ri.resultSites vals r (loc, path) hrmap_eq hne_site⟩
          -- 5e. root_path_coherence for rmap'
          have hroot_coh' : ∀ v y rest, v ∈ cE.pathEnv.refs →
              interpret_regex (cE.pathEnv.paths (.root, v)) (.root_to_var y :: rest) →
              ∀ loc_v path_v, rmap'.map v = some (loc_v, path_v) →
              ∀ loc_y, lookup callerFrame.varStore y = some (some loc_y) →
              loc_v = loc_y → path_v = fieldPathOf rest := by
            intro v y rest hv_mem hpath loc_v path_v hrmap_v loc_y hvar_y hloc_eq
            -- Case split on whether v was already mapped in cM
            cases hcm_v : cM.map v with
            | some pair =>
              -- v is mapped in cM → v is NOT a result-site ref (by hrru contrapositive)
              have hne_v : ∀ s ∈ ri.resultSites, ∀ bt r' bk,
                  lookup cE.siteEnv s = some (.ref bt r' bk) → r' ≠ v := by
                intro s hs bt r' bk hse hr'eq
                have hcm_none := hrru s bt r' bk hs hse
                rw [hr'eq] at hcm_none; simp [hcm_none] at hcm_v
              -- extendWithReturns preserves v's mapping
              have hpres := RefMap.extendWithReturns_preserves cM cE.siteEnv
                ri.resultSites vals v pair hcm_v hne_v
              rw [hpres] at hrmap_v
              simp only [Option.some.injEq] at hrmap_v; subst hrmap_v
              exact hroot_coh v y rest hv_mem hpath loc_v path_v hcm_v loc_y hvar_y hloc_eq
            | none =>
              -- v is unmapped in cM
              by_cases hv_root : v = Aref.root
              · subst hv_root; rw [hrmap_root'] at hrmap_v; exact absurd hrmap_v (by simp)
              · -- v is unmapped non-root: unmapped_isolated gives no paths from .root to v
                exact absurd hpath
                  ((hiso_unmapped v hcm_v hv_root hv_mem Aref.root (Ne.symm hv_root)).1
                    (.root_to_var y :: rest))
          -- 5f. rmap_has_type for rmap'
          have hrmap_ht' : ∀ r bt loc path, rmap'.map r = some (loc, path) →
              ((∃ x bk ms, lookup cE.varEnv x = some (.validVar, .ref bt r bk, ms)) ∨
               (∃ s bk, lookup cE.siteEnv s = some (.ref bt r bk))) →
              ∃ v, m.heap.readRef loc path = some v ∧ HasType cE.enumEnv v bt := by
            intro r bt loc path hrmap_eq hcond
            rcases RefMap.extendWithReturns_values cM cE.siteEnv ri.resultSites vals
              r loc path hrmap_eq with hold | hnew
            · -- Old ref: use hrmap_ht
              apply hrmap_ht r bt loc path hold
              rcases hcond with ⟨x, bk, ms, hvar⟩ | ⟨s, bk, hse⟩
              · exact Or.inl ⟨x, bk, ms, hvar⟩
              · -- Need s ∉ ri.resultSites (because r is mapped in cM)
                by_cases hni : s ∈ ri.resultSites
                · exfalso; rw [hrru s bt r bk hni hse] at hold; exact absurd hold (by simp)
                · exact Or.inr ⟨s, bk, hse, hni⟩
            · -- New ref: extendWithReturns created this mapping
              rcases hcond with ⟨x, bk_v, ms, hvar⟩ | ⟨s_c, bk_c, hse_c⟩
              · -- varEnv case: no result site has ref r, so cM must map r
                have hne_r := hne_output_var r x bt bk_v ms hvar
                cases hcm : cM.map r with
                | none =>
                  exact absurd hrmap_eq (by
                    rw [show rmap'.map r = none from
                      RefMap.extendWithReturns_preserves_none cM cE.siteEnv
                        ri.resultSites vals r hcm hne_r]; simp)
                | some p =>
                  have hpres := RefMap.extendWithReturns_preserves cM cE.siteEnv
                    ri.resultSites vals r p hcm hne_r
                  rw [hpres] at hrmap_eq
                  simp only [Option.some.injEq] at hrmap_eq; subst hrmap_eq
                  exact hrmap_ht r bt loc path hcm (Or.inl ⟨x, bk_v, ms, hvar⟩)
              · -- siteEnv case
                by_cases hni_s : s_c ∈ ri.resultSites
                · -- s_c ∈ resultSites: cM.map r = none, use extendWithReturns_new_mapping_type
                  have hcm_none : cM.map r = none := hrru s_c bt r bk_c hni_s hse_c
                  obtain ⟨bt', bk'', s', hs', hse', v_h, hread, hhas⟩ :=
                    extendWithReturns_new_mapping_type cM cE.siteEnv ri.resultSites vals m.heap
                      r loc path hrmap_eq hcm_none hrvt_caller
                  -- bt' = bt: both sites have ref r, so must be same site by hlru
                  have hbt_eq : bt' = bt := by
                    by_cases hsne : s_c = s'
                    · subst hsne; rw [hse_c] at hse'
                      simp only [Option.some.injEq, MoveType.ref.injEq] at hse'; exact hse'.1.symm
                    · exact absurd ((hlru r).2.1 s_c s' bt bt' bk_c bk'' hsne hse_c hse') False.elim
                  subst hbt_eq; exact ⟨v_h, hread, hhas⟩
                · -- s_c ∉ resultSites: no result site has ref r, so cM maps r
                  have hne_r : ∀ s' ∈ ri.resultSites, ∀ bt' r' bk',
                      lookup cE.siteEnv s' = some (.ref bt' r' bk') → r' ≠ r := by
                    intro s' hs' bt' r' bk' hse' hr'eq; rw [hr'eq] at hse'
                    exact (hlru r).2.1 s_c s' bt bt' bk_c bk' (fun h => hni_s (h ▸ hs')) hse_c hse'
                  cases hcm : cM.map r with
                  | none =>
                    exact absurd hrmap_eq (by
                      rw [show rmap'.map r = none from
                        RefMap.extendWithReturns_preserves_none cM cE.siteEnv
                          ri.resultSites vals r hcm hne_r]; simp)
                  | some p =>
                    have hpres := RefMap.extendWithReturns_preserves cM cE.siteEnv
                      ri.resultSites vals r p hcm hne_r
                    rw [hpres] at hrmap_eq
                    simp only [Option.some.injEq] at hrmap_eq; subst hrmap_eq
                    exact hrmap_ht r bt loc path hcm (Or.inr ⟨s_c, bk_c, hse_c, hni_s⟩)
          -- 6. Assemble WellTypedState
          refine ⟨cE, cL, cR, rmap', henum_eq, ?_, hrest⟩
          exact {
            env_wf := henv_wf
            enumEnv_consistent := by rw [hwt.enumEnv_consistent, henum_eq]
            enum_qualified_nodup := by rw [henum_eq]; exact hwt.enum_qualified_nodup
            enum_names_nodup := by rw [henum_eq]; exact hwt.enum_names_nodup
            enum_variant_nodup := by rw [henum_eq]; intro ename ed he; exact hwt.enum_variant_nodup ename ed he
            enum_fields_nodup := by rw [henum_eq]; intro ename ed vn vd he hvn; exact hwt.enum_fields_nodup ename ed vn vd he hvn
            defaultValues_typed := by
              rw [henum_eq]; intro ename ed vn vd f bt he hv hf
              exact hwt.defaultValues_typed ename ed vn vd f bt he hv hf
            stmt_typed := hstmt_caller
            var_consistent := hvar_con'
            site_consistent := hsite_con'
            rmap_live := hrmap_live'
            rmap_paths := hrmap_paths'
            blocks_typed := hblocks
            lenv_empty_siteEnv := hlenv_se
            lenv_wf := hlenv_wf
            lenv_var_tracked := hlenv_vt
            lenv_var_unique := hlenv_vu
            lenv_funEnv_eq := hlenv_fe
            funEnv_typed := hfe_typed
            heap_loc_bound := hhlb
            varEnv_refs_in_pathEnv := hve_refs
            siteEnv_refs_in_pathEnv := hse_refs
            live_refs_unique := hlru
            rmap_root_none := hrmap_root'
            no_paths_to_root := hno_paths_root
            root_path_coherence := hroot_coh'
            paths_from_non_member_empty := hpfnm
            paths_to_non_member_empty := hptnm
            self_loop_only_empty := hsle
            rmap_has_type := hrmap_ht'
            funEnv_sig_consistent := hfe_sig
            refs_tracked_mapped := by
              intro ref href
              rcases hrtm ref href with hroot | hcm | ⟨s_r, bt_r, bk_r, hs_r, hse_r⟩
              · exact Or.inl hroot
              · right
                intro h_none
                cases hcm_val : cM.map ref with
                | none => exact hcm hcm_val
                | some p =>
                  have hmapped := RefMap.extendWithReturns_preserves cM cE.siteEnv
                    ri.resultSites vals ref p hcm_val (hne_mapped ref p hcm_val)
                  rw [hmapped] at h_none; simp at h_none
              · right
                exact RefMap.extendWithReturns_maps_result_ref cM cE.siteEnv
                  ri.resultSites vals m.heap ref hrvt_caller s_r bt_r bk_r hs_r hse_r
            lenv_labels_in_blocks := hlenv_lib
            has_return_info := hcaller_has_ri
            varStore_locs_bound := hvlb
          }

-- ============================================================
-- Part 8a3a: call_args_compatible helper
-- ============================================================

/-- For a function call, each argument value matches its corresponding parameter type.
    This connects the caller's type information (types_conform + site_consistent) with
    the callee's parameter types. -/
private lemma call_args_compatible
    {enumEnv : EnumEnv}
    (fdefParams : List (Var × MoveType))
    (argSites : List Site) (argVals : List Value)
    (se : SiteEnv) (ss : SiteStore) (heap : Heap) (rmap : RefMap)
    (htc : types_conform se argSites (fdefParams.map (fun (_, τ) => τ.toParamType)))
    (hcsv : collectSiteValues ss argSites = some argVals)
    (hsc : ∀ s τ, lookup se s = some τ →
        ∃ v, lookup ss s = some v ∧ ValueMatchesType enumEnv v τ rmap)
    (hrht : ∀ r bt loc path, rmap.map r = some (loc, path) →
        (∃ s bk, lookup se s = some (.ref bt r bk)) →
        ∃ v, heap.readRef loc path = some v ∧ HasType enumEnv v bt) :
    ∀ x τ v, ((x, τ), v) ∈ fdefParams.zip argVals →
      match τ with
      | .basic bt => HasType enumEnv v bt
      | .ref bt _r _bk => ∃ loc path, v = .ref loc path ∧
          (∃ val, heap.readRef loc path = some val ∧ HasType enumEnv val bt) := by
  induction fdefParams generalizing argSites argVals with
  | nil =>
    simp only [List.map] at htc
    cases argSites with
    | nil => simp [collectSiteValues] at hcsv; subst hcsv; intro x τ v h; simp at h
    | cons => simp [types_conform] at htc
  | cons p ps ih =>
    obtain ⟨x_h, τ_h⟩ := p
    simp only [List.map] at htc
    cases argSites with
    | nil => simp [types_conform] at htc
    | cons s sites' =>
      -- Decompose collectSiteValues
      simp only [collectSiteValues, Bind.bind, Option.bind] at hcsv
      cases hss_s : lookup ss s with
      | none => simp [hss_s] at hcsv
      | some v_h =>
        simp only [hss_s] at hcsv
        cases hcsv_rest : collectSiteValues ss sites' with
        | none => simp [hcsv_rest] at hcsv
        | some vs_t =>
          simp only [hcsv_rest, pure, Option.some.injEq] at hcsv
          subst hcsv
          -- Decompose types_conform
          simp only [types_conform] at htc
          cases hse_s : lookup se s with
          | none => simp [hse_s] at htc
          | some siteType =>
            simp only [hse_s] at htc
            -- Get site_consistent for s
            obtain ⟨v_sc, hv_sc_lookup, hv_sc_match⟩ := hsc s siteType hse_s
            rw [hss_s] at hv_sc_lookup; cases hv_sc_lookup -- v_sc = v_h
            -- Extract tail types_conform (before introducing membership)
            have htc_tail : types_conform se sites' (ps.map (fun (_, τ) => τ.toParamType)) := by
              have h := htc
              cases τ_h with
              | basic bt_h =>
                simp only [MoveType.toParamType] at h
                cases siteType with
                | basic _ => exact h.2
                | ref _ _ _ => exact h.elim
              | ref bt_h r_h bk_h =>
                cases bk_h <;> simp only [MoveType.toParamType] at h <;> cases siteType
                all_goals (first | exact h.elim | exact h.2.2)
            -- Now handle membership in the zip
            intro x τ v hmem
            simp only [List.zip_cons_cons, List.mem_cons, Prod.mk.injEq] at hmem
            rcases hmem with ⟨⟨rfl, rfl⟩, rfl⟩ | hmem_tail
            · -- Head element: after rfl, τ_h eliminated (becomes τ), v_h eliminated (becomes v)
              -- hv_sc_match : ValueMatchesType v siteType rmap
              -- htc : match (τ.toParamType, siteType) with ...
              cases τ with
              | basic bt =>
                simp only [MoveType.toParamType] at htc
                cases siteType with
                | basic bt' => exact (htc.1 ▸ hv_sc_match)
                | ref _ _ _ => exact htc.elim
              | ref bt r bk =>
                cases bk <;> simp only [MoveType.toParamType] at htc <;> cases siteType
                all_goals (try exact htc.elim)
                all_goals (
                  obtain ⟨rfl, _, _⟩ := htc
                  obtain ⟨loc, path, hveq, hrmap_r'⟩ := hv_sc_match
                  exact ⟨loc, path, hveq,
                    hrht _ bt loc path hrmap_r' ⟨s, _, hse_s⟩⟩)
            · -- Tail element: use IH
              exact ih sites' vs_t htc_tail hcsv_rest x τ v hmem_tail

-- ============================================================
-- Part 8a3b: preservation_call
-- ============================================================

private theorem preservation_call (m m' : Machine) (env : TypeEnv) (lenv : LabelEnv)
    (retTypes : List ParamType) (rmap : RefMap)
    (hwt : WellTypedState m env lenv retTypes rmap)
    (hss : StackSafe env.enumEnv m.stack m.frame.returnInfo m.heap retTypes)
    (results : List Site) (fname : Id) (argSites : List Site) (cont : Stmt)
    (hstmt : m.frame.stmt = .call results fname argSites cont)
    (hstep : step (.running m) = .running m') :
    ∃ env' lenv' retTypes' rmap',
      env'.enumEnv = env.enumEnv ∧ WellTypedState m' env' lenv' retTypes' rmap' ∧
      StackSafe env.enumEnv m'.stack m'.frame.returnInfo m'.heap retTypes' := by
  -- 1. Extract typing premises from typecheck_stmt.call
  have hstmt_typed : typecheck_stmt lenv env (.call results fname argSites cont) retTypes := by
    rw [← hstmt]; exact hwt.stmt_typed
  obtain ⟨params, rets, outRefs, popEnv, hsig, htypes_conf, hfresh_sites,
    hnodup_sites, hfresh_refs, hnodup_refs, hpop, hiso, hcont_cc⟩ := inv_call hstmt_typed

  -- 2. Get runtime function definition from funEnv_sig_consistent
  obtain ⟨fdef, hfdef_lookup, hfdef_params, hfdef_rets⟩ :=
    hwt.funEnv_sig_consistent fname ⟨params, rets⟩ hsig

  -- 3. Get FunTypeSafe from funEnv_typed
  have hfts := hwt.funEnv_typed fname fdef hfdef_lookup
  obtain ⟨callee_lenv, htyped_fun, hlenv_wf_callee, hlenv_es_callee, hlenv_vt_callee,
    hlenv_vu_callee, hlenv_sig_callee, hlenv_complete_callee, hlenv_lib_callee, hlenv_fe_callee,
    hlenv_pfnm_callee, hlenv_ptnm_callee, hlenv_sle_callee,
    hparams_nodup, hparam_refs_distinct, hparam_refs_not_root, hentry_varEnv_exact,
    hlenv_enumEnv_callee⟩ := hfts

  -- 4. Simplify step: case-split on collectSiteValues, allocArgs, blocks.head?
  simp only [step, hstmt] at hstep
  -- funEnv lookup succeeds
  rw [show AssocMap.lookup m.frame.funEnv fname = some fdef from hfdef_lookup] at hstep
  -- collectSiteValues
  cases hcsv : collectSiteValues m.frame.siteStore argSites with
  | none => simp [hcsv] at hstep
  | some argVals =>
    simp only [hcsv] at hstep
    -- allocArgs
    cases hallocArgs : allocArgs m.heap fdef.params argVals with
    | none => simp [hallocArgs] at hstep
    | some allocPair =>
      obtain ⟨heap', paramVarStore⟩ := allocPair
      simp only [hallocArgs] at hstep
      -- blocks.head?
      cases hhead : fdef.blocks.head? with
      | none => simp [hhead] at hstep
      | some entryBlock =>
        simp only [hhead, ExecState.running.injEq] at hstep
        subst hstep

        -- 5. Extract callee entry block info from FunTypeSafe
        obtain ⟨initEnv, hvarEnv_init, hsiteEnv_init, hpathEnv_init, henumEnv_init,
          hblocks_ne, hentry_equiv, hblocks_typed⟩ := htyped_fun
        obtain ⟨entryLabel, entryBody⟩ := entryBlock
        have hentry_in : ⟨entryLabel, entryBody⟩ ∈ fdef.blocks := by
          cases hbl : fdef.blocks with
          | nil => simp [hbl] at hhead
          | cons h t => rw [hbl] at hhead; simp only [List.head?, Option.some.injEq] at hhead;
                        rw [← hhead]; exact .head t
        obtain ⟨blockEnv, hlookup_callee⟩ := hlenv_complete_callee ⟨entryLabel, entryBody⟩ hentry_in
        have hequiv := hentry_equiv entryLabel entryBody blockEnv hhead hlookup_callee
        have htyped_entry := hblocks_typed ⟨entryLabel, entryBody⟩ hentry_in blockEnv hlookup_callee
        have hblockEnv_wf := hlenv_wf_callee entryLabel blockEnv hlookup_callee
        have hvarEnv_exact := hentry_varEnv_exact ⟨entryLabel, entryBody⟩ blockEnv hhead hlookup_callee
        -- Extract equiv components
        unfold TypeEnv.equiv at hequiv
        obtain ⟨_, hvar_compat, hrefs_equiv, hpaths_equiv, _henumEnv_equiv⟩ := hequiv
        have hrefs_eq : blockEnv.pathEnv.refs = (init_fun_pathEnv fdef).refs := by
          rw [hpathEnv_init] at hrefs_equiv; exact hrefs_equiv
        have hsiteEnv_empty : ∀ s, lookup blockEnv.siteEnv s = none :=
          hlenv_es_callee entryLabel blockEnv hlookup_callee

        -- 6. Construct callee rmap (same pattern as initState_safe)
        let paramRefEntries := (fdef.params.zip argVals).filterMap (fun ((_, τ), v) =>
          match τ, v with
          | .ref _ r _, .ref loc path => some (r, (loc, path))
          | _, _ => none)
        let calleeRmap : RefMap := { map := fun r => List.lookup r paramRefEntries }

        -- === Helpers for callee WellTypedState ===
        -- Args compatible (from call_args_compatible)
        have hargs_compat : ∀ x τ v, ((x, τ), v) ∈ fdef.params.zip argVals →
            match τ with
            | .basic bt => HasType env.enumEnv v bt
            | .ref bt _r _bk => ∃ loc path, v = .ref loc path ∧
                (∃ val, m.heap.readRef loc path = some val ∧ HasType env.enumEnv val bt) :=
          call_args_compatible fdef.params argSites argVals
            env.siteEnv m.frame.siteStore m.heap rmap
            (hfdef_params ▸ htypes_conf) hcsv hwt.site_consistent
            (fun r bt loc path hrm hse => hwt.rmap_has_type r bt loc path hrm (Or.inr hse))
        -- Helper: from blockEnv valid var lookup, get init type and param membership
        have hvar_init_exact : ∀ x τ ms, lookup blockEnv.varEnv x = some (.validVar, τ, ms) →
            lookup (init_fun_varEnv fdef) x = some (.validVar, τ, ms) ∧ (x, τ) ∈ fdef.params := by
          intro x τ ms hlookup_var
          have := hvarEnv_exact x
          rw [hlookup_var] at this
          exact ⟨this.symm, init_fun_varEnv_valid_in_params fdef x τ ms this.symm⟩
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
        -- rmap.map r → membership in params.zip argVals
        have hrmap_mem : ∀ r loc path, calleeRmap.map r = some (loc, path) →
            ∃ x bt bk, ((x, .ref bt r bk), .ref loc path) ∈ fdef.params.zip argVals := by
          intro r loc path hrmap_eq
          have hmem_entries : (r, (loc, path)) ∈ paramRefEntries := list_lookup_mem hrmap_eq
          simp only [paramRefEntries, List.mem_filterMap] at hmem_entries
          obtain ⟨⟨⟨x, τ⟩, v⟩, hmem_zip, hfm⟩ := hmem_entries
          revert hfm; cases τ with
          | basic _ => simp
          | ref bt r' bk =>
            cases v with
            | int _ => simp
            | bool _ => simp
            | unit => simp
            | record _ => simp
            | vec _ => simp
            | variant _ _ _ => simp
            | ref loc' path' =>
              intro hfm
              simp only [Option.some.injEq, Prod.mk.injEq] at hfm
              obtain ⟨rfl, rfl, rfl⟩ := hfm
              exact ⟨x, bt, bk, hmem_zip⟩
        -- ref param with arg → calleeRmap maps it
        have hrmap_of_param : ∀ x bt r bk loc path,
            ((x, .ref bt r bk), .ref loc path) ∈ fdef.params.zip argVals →
            calleeRmap.map r = some (loc, path) := by
          intro x bt r bk loc path hmem_zip
          show List.lookup r paramRefEntries = some (loc, path)
          have hmem_pre : (r, (loc, path)) ∈ paramRefEntries := by
            simp only [paramRefEntries, List.mem_filterMap]
            exact ⟨((x, .ref bt r bk), .ref loc path), hmem_zip, by simp⟩
          exact list_lookup_of_mem_nodup hmem_pre (by
            have hmf : paramRefEntries.map Prod.fst =
              (fdef.params.zip argVals).filterMap (fun ((_, τ), v) =>
                match τ, v with | .ref _ r' _, .ref _ _ => some r' | _, _ => none) := by
              simp only [paramRefEntries, List.map_filterMap]; congr 1
              ext ⟨⟨_, τ⟩, v⟩; cases τ with | basic _ => simp | ref _ _ _ => cases v <;> simp
            rw [hmf]; exact (paramRefKeys_sublist fdef.params argVals).nodup hparam_refs_distinct)
        -- Length and zip helpers
        have hlen_eq : fdef.params.length = argVals.length :=
          allocArgs_length_eq m.heap fdef.params argVals heap' paramVarStore hallocArgs
        have hmem_zip_of_param : ∀ x τ, (x, τ) ∈ fdef.params → ∃ v, ((x, τ), v) ∈ fdef.params.zip argVals :=
          fun x τ h => exists_mem_zip_right hlen_eq h
        -- Root membership
        have hroot_in_init : Aref.root ∈ (init_fun_pathEnv fdef).refs := by
          simp only [init_fun_pathEnv]; exact List.Mem.head _
        have hroot_in_block : Aref.root ∈ blockEnv.pathEnv.refs := hrefs_eq ▸ hroot_in_init
        -- heap' preserves readRef for calleeRmap-mapped locations
        have hreadRef_preserved : ∀ r loc path, calleeRmap.map r = some (loc, path) →
            heap'.readRef loc path = m.heap.readRef loc path := by
          intro r loc path hrmap_eq
          obtain ⟨x, bt, bk, hmem_zip⟩ := hrmap_mem r loc path hrmap_eq
          have hcompat := hargs_compat x (.ref bt r bk) (.ref loc path) hmem_zip
          dsimp only at hcompat
          obtain ⟨_, _, hveq, _, hreadref, _⟩ := hcompat
          cases hveq
          have hread_ne : m.heap.read loc ≠ none := by
            intro h; unfold Heap.readRef at hreadref; simp [h] at hreadref
          have hpreserve := allocArgs_preserves_old_read m.heap fdef.params argVals
            heap' paramVarStore hallocArgs loc (hwt.heap_loc_bound loc hread_ne)
          unfold Heap.readRef; rw [hpreserve]

        -- 7. Provide the two witnesses: callee WellTypedState + StackSafe
        refine ⟨blockEnv, callee_lenv, fdef.returnType, calleeRmap, ?_, ?_, ?_⟩
        · -- blockEnv.enumEnv = env.enumEnv
          exact hlenv_enumEnv_callee entryLabel blockEnv hlookup_callee
        · -- Callee WellTypedState
          exact {
            env_wf := hblockEnv_wf
            enumEnv_consistent := by
              rw [hwt.enumEnv_consistent]
              exact (hlenv_enumEnv_callee entryLabel blockEnv hlookup_callee).symm
            enum_qualified_nodup := by
              intro ename enumDef hlookup_ee
              have hee : blockEnv.enumEnv = env.enumEnv := by
                rw [hlenv_enumEnv_callee entryLabel blockEnv hlookup_callee,
                    ← hwt.enumEnv_consistent]
              rw [hee] at hlookup_ee
              exact hwt.enum_qualified_nodup ename enumDef hlookup_ee
            enum_names_nodup := by
              have hee : blockEnv.enumEnv = env.enumEnv := by
                rw [hlenv_enumEnv_callee entryLabel blockEnv hlookup_callee,
                    ← hwt.enumEnv_consistent]
              rw [hee]; exact hwt.enum_names_nodup
            enum_variant_nodup := by
              have hee : blockEnv.enumEnv = env.enumEnv := by
                rw [hlenv_enumEnv_callee entryLabel blockEnv hlookup_callee,
                    ← hwt.enumEnv_consistent]
              rw [hee]; intro ename ed he; exact hwt.enum_variant_nodup ename ed he
            enum_fields_nodup := by
              have hee : blockEnv.enumEnv = env.enumEnv := by
                rw [hlenv_enumEnv_callee entryLabel blockEnv hlookup_callee,
                    ← hwt.enumEnv_consistent]
              rw [hee]; intro ename ed vn vd he hvn; exact hwt.enum_fields_nodup ename ed vn vd he hvn
            defaultValues_typed := by
              have hee : blockEnv.enumEnv = env.enumEnv := by
                rw [hlenv_enumEnv_callee entryLabel blockEnv hlookup_callee,
                    ← hwt.enumEnv_consistent]
              rw [hee]; intro ename ed vn vd f bt he hv hf
              exact hwt.defaultValues_typed ename ed vn vd f bt he hv hf
            stmt_typed := htyped_entry
            var_consistent := by
              intro x isv τ ms hlookup_var
              have hlookup_init' : lookup (init_fun_varEnv fdef) x = some (isv, τ, ms) := by
                rw [← hvarEnv_exact x]; exact hlookup_var
              cases isv with
              | validVar =>
                have hparam := init_fun_varEnv_valid_in_params fdef x τ ms hlookup_init'
                have hnot_local := init_fun_varEnv_valid_not_local fdef x τ ms hlookup_init'
                have ⟨arg_v, hmem_zip⟩ := hmem_zip_of_param x τ hparam
                have ⟨alloc_loc, hstore, hread⟩ :=
                  allocArgs_param_stores_arg m.heap fdef.params argVals heap' paramVarStore
                    hwt.heap_loc_bound hallocArgs hparams_nodup x τ arg_v hmem_zip
                have hlookup_vs : lookup (addLocals paramVarStore fdef.locals) x = some (some alloc_loc) := by
                  rw [addLocals_preserves_lookup paramVarStore fdef.locals x hnot_local]; exact hstore
                cases τ with
                | basic bt =>
                  have hht := hargs_compat x (.basic bt) arg_v hmem_zip
                  have henum : blockEnv.enumEnv = env.enumEnv :=
                    hlenv_enumEnv_callee entryLabel blockEnv hlookup_callee
                  exact ⟨alloc_loc, arg_v, hlookup_vs, hread, henum ▸ hht⟩
                | ref bt r bk =>
                  have hcompat := hargs_compat x (.ref bt r bk) arg_v hmem_zip
                  dsimp only at hcompat
                  obtain ⟨loc, path, hveq, _val, _hreadref, _hht⟩ := hcompat
                  subst hveq
                  have hrmap_r := hrmap_of_param x bt r bk loc path hmem_zip
                  exact ⟨alloc_loc, .ref loc path, hlookup_vs, hread, loc, path, rfl, hrmap_r⟩
              | invalidVar =>
                have hlocal := init_fun_varEnv_invalid_is_local fdef x τ ms hlookup_init'
                exact Or.inl (addLocals_local_some_none paramVarStore fdef.locals x hlocal)
            site_consistent := by
              intro s τ hlookup_s; rw [hsiteEnv_empty s] at hlookup_s; cases hlookup_s
            rmap_live := by
              intro r loc path _hr_tracked hrmap_eq
              obtain ⟨x, bt, bk, hmem_zip⟩ := hrmap_mem r loc path hrmap_eq
              have hcompat := hargs_compat x (.ref bt r bk) (.ref loc path) hmem_zip
              dsimp only at hcompat
              obtain ⟨_, _, hveq, val, hreadref, _⟩ := hcompat
              cases hveq
              rw [hreadRef_preserved r loc path hrmap_eq, hreadref]
              exact fun h => nomatch h
            rmap_paths := by
              intro r1 r2 hr1 hr2 p hp
              have hpaths_init := hpaths_equiv r1 r2 hr1 hr2
              rw [hpathEnv_init] at hpaths_init
              by_cases heq : r1 = r2
              · subst heq
                have hself : blockEnv.pathEnv.paths (r1, r1) = Regex.ε := by
                  rw [hpaths_init]; simp [init_fun_pathEnv]
                rw [hself] at hp
                have hp_nil := hlenv_sle_callee entryLabel blockEnv hlookup_callee r1 p (by rw [hself]; exact hp)
                subst hp_nil
                unfold PathReflectedInHeap
                cases hrm : calleeRmap.map r1 with
                | none => exact True.intro
                | some pair =>
                  obtain ⟨loc, path⟩ := pair
                  intro _
                  obtain ⟨x, bt, bk, hmz⟩ := hrmap_mem r1 loc path hrm
                  have hcompat := hargs_compat x (.ref bt r1 bk) (.ref loc path) hmz
                  dsimp only at hcompat
                  obtain ⟨_, _, hveq, val, hrf, _⟩ := hcompat
                  cases hveq
                  refine ⟨(List.append_nil path).symm, ?_⟩
                  rw [hreadRef_preserved r1 loc path hrm, hrf]
                  exact fun h => nomatch h
              · have hempty : blockEnv.pathEnv.paths (r1, r2) = Regex.empty := by
                  rw [hpaths_init]; simp [init_fun_pathEnv, heq]
                rw [hempty] at hp; exact absurd hp id
            blocks_typed := fun b hmem benv hlookup_b => hblocks_typed b hmem benv hlookup_b
            lenv_empty_siteEnv := hlenv_es_callee
            lenv_wf := hlenv_wf_callee
            lenv_var_tracked := hlenv_vt_callee
            lenv_var_unique := hlenv_vu_callee
            lenv_funEnv_eq := fun L envL h => hlenv_fe_callee L envL entryLabel blockEnv h hlookup_callee
            funEnv_typed := by
              rw [hlenv_enumEnv_callee entryLabel blockEnv hlookup_callee]
              exact hwt.funEnv_typed
            heap_loc_bound :=
              allocArgs_heap_loc_bound' m.heap fdef.params argVals heap' paramVarStore
                hallocArgs hwt.heap_loc_bound
            varEnv_refs_in_pathEnv := by
              intro x bt r bk ms hlookup_var
              have ⟨_, hparam⟩ := hvar_init_exact x (.ref bt r bk) ms hlookup_var
              exact hrefs_eq ▸ (by
                simp only [init_fun_pathEnv]; apply List.mem_cons_of_mem
                simp only [List.mem_filterMap]
                exact ⟨(x, .ref bt r bk), hparam, by simp⟩)
            siteEnv_refs_in_pathEnv := by
              intro s bt r bk hlookup_s; rw [hsiteEnv_empty s] at hlookup_s; cases hlookup_s
            live_refs_unique := by
              intro r; refine ⟨?_, ?_, ?_⟩
              · intro x bt bk ms s bt' bk' _ hlookup_s
                rw [hsiteEnv_empty s] at hlookup_s; cases hlookup_s
              · intro s s' bt bt' bk bk' _ hlookup_s _
                rw [hsiteEnv_empty s] at hlookup_s; cases hlookup_s
              · intro x y bt bt' bk bk' ms ms' hne hlookup_x hlookup_y
                have ⟨_, hpx⟩ := hvar_init_exact x (.ref bt r bk) ms hlookup_x
                have ⟨_, hpy⟩ := hvar_init_exact y (.ref bt' r bk') ms' hlookup_y
                exact absurd (nodup_filterMap_params_same_ref fdef.params hparams_nodup
                  hparam_refs_distinct hpx hpy) hne
            rmap_root_none := by
              show calleeRmap.map Aref.root = none
              by_contra h
              have ⟨pair, hpair⟩ := Option.ne_none_iff_exists'.mp h
              obtain ⟨rloc, rpath⟩ := pair
              obtain ⟨x, bt, bk, hmem_zip⟩ := hrmap_mem Aref.root rloc rpath hpair
              exact hparam_refs_not_root x bt Aref.root bk (List.of_mem_zip hmem_zip).1 rfl
            no_paths_to_root := by
              intro u p hp
              by_cases hu : u = Aref.root
              · constructor
                · exact hu
                · have hpaths : blockEnv.pathEnv.paths (.root, .root) = Regex.ε := by
                    have h := hpaths_equiv .root .root hroot_in_block hroot_in_block
                    rw [hpathEnv_init] at h; simp [init_fun_pathEnv] at h; exact h
                  rw [hu, hpaths] at hp; exact hp
              · have hpaths_empty : blockEnv.pathEnv.paths (u, .root) = Regex.empty := by
                  by_cases hu_in : u ∈ blockEnv.pathEnv.refs
                  · have h := hpaths_equiv u .root hu_in hroot_in_block
                    rw [hpathEnv_init] at h
                    simp only [init_fun_pathEnv, hu, ↓reduceIte] at h; exact h
                  · exact hblockEnv_wf.pathEnv_wf.from_untracked_to_root_empty u hu_in hu
                rw [hpaths_empty] at hp; exact hp.elim
            root_path_coherence := by
              intro v y rest hv_in hp loc_v path_v hrmap_v loc_y hlookup_y
              by_cases hv : v = Aref.root
              · subst hv
                have hpaths : blockEnv.pathEnv.paths (.root, .root) = Regex.ε := by
                  have h := hpaths_equiv .root .root hroot_in_block hroot_in_block
                  rw [hpathEnv_init] at h; simp [init_fun_pathEnv] at h; exact h
                rw [hpaths] at hp
                have := hlenv_sle_callee entryLabel blockEnv hlookup_callee .root
                  (.root_to_var y :: rest) (by rw [hpaths]; exact hp)
                exact absurd this (by simp)
              · have hpaths_empty : blockEnv.pathEnv.paths (.root, v) = Regex.empty := by
                  by_cases hv_in' : v ∈ blockEnv.pathEnv.refs
                  · have h := hpaths_equiv .root v hroot_in_block hv_in'
                    rw [hpathEnv_init] at h
                    have hroot_ne_v : Aref.root ≠ v := fun heq => hv heq.symm
                    simp only [init_fun_pathEnv, show ¬(Aref.root = v) from hroot_ne_v, ite_false] at h
                    exact h
                  · exact hblockEnv_wf.pathEnv_wf.refs_complete v hv_in'
                rw [hpaths_empty] at hp; exact hp.elim
            paths_from_non_member_empty :=
              hlenv_pfnm_callee entryLabel blockEnv hlookup_callee
            paths_to_non_member_empty :=
              hlenv_ptnm_callee entryLabel blockEnv hlookup_callee
            self_loop_only_empty :=
              hlenv_sle_callee entryLabel blockEnv hlookup_callee
            rmap_has_type := by
              intro r bt loc path hrmap_eq hor
              rcases hor with ⟨x, bk, ms, hlookup_x⟩ | ⟨s, bk, hlookup_s⟩
              · have ⟨_, hparam⟩ := hvar_init_exact x (.ref bt r bk) ms hlookup_x
                have ⟨arg_v, hmem_zip⟩ := hmem_zip_of_param x (.ref bt r bk) hparam
                have hcompat := hargs_compat x (.ref bt r bk) arg_v hmem_zip
                dsimp only at hcompat
                obtain ⟨loc', path', hveq, val, hreadref, hht⟩ := hcompat
                subst hveq
                have hrmap_r := hrmap_of_param x bt r bk loc' path' hmem_zip
                rw [hrmap_eq] at hrmap_r; cases hrmap_r
                rw [hreadRef_preserved r loc path hrmap_eq]
                have henum : blockEnv.enumEnv = env.enumEnv :=
                  hlenv_enumEnv_callee entryLabel blockEnv hlookup_callee
                exact ⟨val, hreadref, henum ▸ hht⟩
              · rw [hsiteEnv_empty s] at hlookup_s; cases hlookup_s
            funEnv_sig_consistent := by
              intro fn sig hlookup_fe
              exact hlenv_sig_callee entryLabel blockEnv hlookup_callee fn sig hlookup_fe
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
                  have hcompat := hargs_compat x (.ref bt r' bk) v hmem_zip
                  dsimp only at hcompat
                  obtain ⟨loc, path, hveq, _⟩ := hcompat
                  subst hveq
                  have hrmap := hrmap_of_param x bt r' bk loc path hmem_zip
                  rw [hrmap]; simp
            lenv_labels_in_blocks := hlenv_lib_callee
            has_return_info := fun _ => rfl
            varStore_locs_bound := by
              intro y loc_y hvar
              by_cases hlocal : y ∈ fdef.locals.map (·.name)
              · rw [addLocals_local_some_none paramVarStore fdef.locals y hlocal] at hvar
                cases hvar
              · rw [addLocals_preserves_lookup paramVarStore fdef.locals y hlocal] at hvar
                exact allocArgs_varStore_locs_bound m.heap fdef.params argVals heap'
                  paramVarStore hallocArgs y loc_y hvar
          }
        · -- StackSafe for the new stack
          -- Define restricted rmap: agrees with rmap on env.pathEnv.refs, none elsewhere
          let callerRmap : RefMap := { map := fun r =>
            if r ∈ env.pathEnv.refs then rmap.map r else none }

          -- Key popEnv properties
          have hpopVarEnv : popEnv.varEnv = env.varEnv :=
            populate_call_outputs_varEnv env popEnv results rets outRefs hpop
          have hpopFunEnv : popEnv.funEnv = env.funEnv :=
            populate_call_outputs_funEnv env popEnv results rets outRefs hpop
          have hpopEnumEnv : popEnv.enumEnv = env.enumEnv :=
            populate_call_outputs_enumEnv env popEnv results rets outRefs hpop
          have hpopRefsMono : ∀ r ∈ env.pathEnv.refs, r ∈ popEnv.pathEnv.refs :=
            populate_call_outputs_refs_mono env popEnv results rets outRefs hpop
          have hpopSiteTracked : ∀ s bt r bk, lookup popEnv.siteEnv s = some (.ref bt r bk) →
              r ∈ popEnv.pathEnv.refs :=
            populate_call_outputs_site_tracked env popEnv results rets outRefs
              (fun s bt r bk h => hwt.siteEnv_refs_in_pathEnv s bt r bk h) hpop
          have hpopVarTracked : ∀ x bt r bk ms,
              lookup popEnv.varEnv x = some (.validVar, .ref bt r bk, ms) →
              r ∈ popEnv.pathEnv.refs :=
            populate_call_outputs_var_tracked env popEnv results rets outRefs
              (fun x bt r bk ms h => hwt.varEnv_refs_in_pathEnv x bt r bk ms h) hpop
          have hpopSle : ∀ u p, interpret_regex (popEnv.pathEnv.paths (u, u)) p → p = [] :=
            populate_call_outputs_self_loop_only_empty env popEnv results rets outRefs
              hwt.self_loop_only_empty hpop
          have hpopPfnm : ∀ u v p, u ∉ popEnv.pathEnv.refs → u ≠ .root → u ≠ v →
              ¬interpret_regex (popEnv.pathEnv.paths (u, v)) p :=
            populate_call_outputs_paths_from_nm env popEnv results rets outRefs
              hwt.paths_from_non_member_empty hpop
          have hpopPtnm : ∀ u v p, v ∉ popEnv.pathEnv.refs → v ≠ .root → u ≠ v →
              ¬interpret_regex (popEnv.pathEnv.paths (u, v)) p :=
            populate_call_outputs_paths_to_nm env popEnv results rets outRefs
              hwt.paths_to_non_member_empty hpop
          have houtRef_not_root : ∀ r ∈ outRefs, r ≠ Aref.root := by
            intro r hr hroot
            have hfr := hfresh_refs r hr
            have := hwt.env_wf.pathEnv_wf.root_in_refs
            rw [← hroot] at this
            exact hfr.1 this
          have hpopWf : TypeEnv.WellFormed popEnv :=
            populate_call_outputs_wf env popEnv results rets outRefs
              hwt.env_wf houtRef_not_root hpop
          have hpopUnique : RefsUnique popEnv.varEnv popEnv.siteEnv :=
            populate_call_outputs_RefsUnique env popEnv results rets outRefs
              hwt.live_refs_unique hfresh_refs hnodup_refs hpop

          -- callerRmap helpers
          have hcrmap_agree : ∀ r, r ∈ env.pathEnv.refs → callerRmap.map r = rmap.map r := by
            intro r hr; show (if r ∈ env.pathEnv.refs then rmap.map r else none) = rmap.map r
            simp [hr]
          have hcrmap_none : ∀ r, r ∉ env.pathEnv.refs → callerRmap.map r = none := by
            intro r hr; show (if r ∈ env.pathEnv.refs then rmap.map r else none) = none
            simp [hr]
          have hcrmap_root_none : callerRmap.map Aref.root = none := by
            rw [hcrmap_agree .root hwt.env_wf.pathEnv_wf.root_in_refs]
            exact hwt.rmap_root_none

          -- Tail StackSafe
          have htail : StackSafe env.enumEnv m.stack m.frame.returnInfo heap' retTypes :=
            stackSafe_allocArgs env.enumEnv m.stack m.frame.returnInfo m.heap fdef.params argVals
              heap' paramVarStore hss hwt.heap_loc_bound hallocArgs

          -- outRefs not in env.pathEnv.refs
          have houtRef_not_in_refs : ∀ r ∈ outRefs, r ∉ env.pathEnv.refs :=
            fun r hr => (hfresh_refs r hr).1

          -- heap' preserves old reads
          have hheap_preserve : ∀ loc, m.heap.read loc ≠ none →
              heap'.read loc = m.heap.read loc :=
            fun loc hne => allocArgs_preserves_old_read m.heap fdef.params argVals
              heap' paramVarStore hallocArgs loc (hwt.heap_loc_bound loc hne)

          -- Fresh result sites have no siteEnv entries in env
          have hfresh_sites_none : ∀ s ∈ results, lookup env.siteEnv s = none := by
            intro s hs
            have hfs := hfresh_sites
            simp only [all_fresh_sites, List.all_eq_true] at hfs
            exact notIn_implies_lookup_none env.siteEnv s (hfs s hs)

          -- result_refs_unmapped: callerRmap.map r = none for output refs
          have hresult_unmapped : ∀ s bt r bk, s ∈ results →
              lookup popEnv.siteEnv s = some (.ref bt r bk) → callerRmap.map r = none := by
            intro s bt r bk hs hse
            rcases populate_call_outputs_siteEnv_ref_origin env popEnv results rets outRefs hpop
              s bt r bk hse with h_old | h_out
            · -- r came from env.siteEnv at s — but s is a fresh result site
              rw [hfresh_sites_none s hs] at h_old; cases h_old
            · -- r ∈ outRefs → r ∉ env.pathEnv.refs → callerRmap.map r = none
              exact hcrmap_none r (houtRef_not_in_refs r h_out)

          -- refs_tracked_or_result
          have hrefs_tracked_or_result : ∀ r, r ∈ popEnv.pathEnv.refs →
              r = .root ∨ callerRmap.map r ≠ none ∨
              (∃ s bt bk, s ∈ results ∧ lookup popEnv.siteEnv s = some (.ref bt r bk)) := by
            intro r hr
            rcases populate_call_outputs_refs_bounded env popEnv results rets outRefs hpop r hr
              with hr_old | hr_out
            · -- r ∈ env.pathEnv.refs
              rcases hwt.refs_tracked_mapped r hr_old with rfl | hne
              · exact Or.inl rfl
              · right; left; rw [hcrmap_agree r hr_old]; exact hne
            · -- r ∈ outRefs → has a result site entry
              right; right
              exact populate_call_outputs_outRef_has_site env popEnv results rets outRefs
                hnodup_sites hpop r hr_out

          -- var_consistent
          have hvar_con : ∀ x isv τ ms, lookup popEnv.varEnv x = some (isv, τ, ms) →
              match isv with
              | .validVar => ∃ loc v, lookup m.frame.varStore x = some (some loc) ∧
                             heap'.read loc = some v ∧ ValueMatchesType env.enumEnv v τ callerRmap
              | .invalidVar => lookup m.frame.varStore x = some none ∨
                              ∃ loc, lookup m.frame.varStore x = some (some loc) := by
            intro x isv τ ms hlookup
            rw [hpopVarEnv] at hlookup
            have hvc := hwt.var_consistent x isv τ ms hlookup
            cases isv with
            | validVar =>
              obtain ⟨loc, v, hstore, hread, hvmt⟩ := hvc
              refine ⟨loc, v, hstore, ?_, ?_⟩
              · rw [hheap_preserve loc (by rw [hread]; exact fun h => nomatch h)]; exact hread
              · -- ValueMatchesType: callerRmap agrees with rmap on tracked refs
                cases τ with
                | basic bt => exact hvmt
                | ref bt r' bk =>
                  obtain ⟨loc', path', hveq, hrmap_r'⟩ := hvmt
                  refine ⟨loc', path', hveq, ?_⟩
                  rw [hcrmap_agree r' (hwt.varEnv_refs_in_pathEnv x bt r' bk ms hlookup)]
                  exact hrmap_r'
            | invalidVar => exact hvc

          -- site_consistent (restricted to non-result sites)
          have hsite_con : ∀ s τ, lookup popEnv.siteEnv s = some τ → s ∉ results →
              ∃ v, lookup m.frame.siteStore s = some v ∧ ValueMatchesType env.enumEnv v τ callerRmap := by
            intro s τ hlook hs_not_result
            -- s ∉ results → siteEnv entry is unchanged from env
            have hlook_env : lookup env.siteEnv s = some τ := by
              rcases populate_call_outputs_siteEnv_ref_origin env popEnv results rets outRefs hpop
                s with h_ref_origin
              -- Actually we need a more general fact: for non-result sites, siteEnv is unchanged
              rw [populate_call_outputs_siteEnv_non_member env popEnv results rets outRefs hpop
                s hs_not_result] at hlook
              exact hlook
            obtain ⟨v, hstore, hvmt⟩ := hwt.site_consistent s τ hlook_env
            refine ⟨v, hstore, ?_⟩
            cases τ with
            | basic bt => exact hvmt
            | ref bt r' bk =>
              obtain ⟨loc', path', hveq, hrmap_r'⟩ := hvmt
              refine ⟨loc', path', hveq, ?_⟩
              rw [hcrmap_agree r' (hwt.siteEnv_refs_in_pathEnv s bt r' bk hlook_env)]
              exact hrmap_r'

          -- rmap_live
          have hrmap_live : ∀ r loc path, r ∈ popEnv.pathEnv.refs → callerRmap.map r = some (loc, path) →
              heap'.readRef loc path ≠ none := by
            intro r loc path _hr_pop hcrmap
            have hr_in : r ∈ env.pathEnv.refs := by
              by_contra h; rw [hcrmap_none r h] at hcrmap; cases hcrmap
            rw [hcrmap_agree r hr_in] at hcrmap
            have hlive := hwt.rmap_live r loc path hr_in hcrmap
            -- readRef only reads loc then follows path through value
            unfold Heap.readRef at hlive ⊢
            simp only [bind, Option.bind] at hlive ⊢
            have hread_ne : m.heap.read loc ≠ none := by
              intro h; simp [h] at hlive
            rw [hheap_preserve loc hread_ne]; exact hlive

          -- rmap_has_type (restricted to non-result siteEnv)
          have hrmap_ht : ∀ r bt loc path, callerRmap.map r = some (loc, path) →
              ((∃ x bk ms, lookup popEnv.varEnv x = some (.validVar, .ref bt r bk, ms)) ∨
               (∃ s bk, lookup popEnv.siteEnv s = some (.ref bt r bk) ∧ s ∉ results)) →
              ∃ v, heap'.readRef loc path = some v ∧ HasType env.enumEnv v bt := by
            intro r bt loc path hcrmap hwitness
            have hr_in : r ∈ env.pathEnv.refs := by
              by_contra h; rw [hcrmap_none r h] at hcrmap; cases hcrmap
            rw [hcrmap_agree r hr_in] at hcrmap
            -- Transfer witness to env's varEnv/siteEnv
            have hwitness_env : (∃ x bk ms, lookup env.varEnv x =
                some (.validVar, .ref bt r bk, ms)) ∨
                (∃ s bk, lookup env.siteEnv s = some (.ref bt r bk)) := by
              rcases hwitness with ⟨x, bk, ms, hv⟩ | ⟨s, bk, hs, hs_nr⟩
              · left; rw [hpopVarEnv] at hv; exact ⟨x, bk, ms, hv⟩
              · right
                rw [populate_call_outputs_siteEnv_non_member env popEnv results rets outRefs
                  hpop s hs_nr] at hs
                exact ⟨s, bk, hs⟩
            have := hwt.rmap_has_type r bt loc path hcrmap hwitness_env
            obtain ⟨v, hreadref, hht⟩ := this
            refine ⟨v, ?_, hht⟩
            -- readRef preservation through allocArgs
            unfold Heap.readRef at hreadref ⊢
            simp only [bind, Option.bind] at hreadref ⊢
            have hread_ne : m.heap.read loc ≠ none := by
              intro h; simp [h] at hreadref
            rw [hheap_preserve loc hread_ne]; exact hreadref

          -- Helper: outRef isolation in popEnv
          have houtRef_isolated := populate_call_outputs_outRef_isolated env popEnv
            results rets outRefs (fun r hr => (hfresh_refs r hr).1) houtRef_not_root
            hnodup_refs hwt.paths_from_non_member_empty hwt.paths_to_non_member_empty hpop
          have hroot_not_out : Aref.root ∉ outRefs :=
            fun h => (houtRef_not_root .root h) rfl

          -- Helper: paths preserved between non-outRef refs
          have hpaths_preserved := populate_call_outputs_paths_preserved env popEnv
            results rets outRefs (fun r hr => (hfresh_refs r hr).1) hnodup_refs hpop

          -- Helper: readRef preserved from m.heap to heap'
          have hreadRef_preserved_gen : ∀ loc path, m.heap.read loc ≠ none →
              heap'.readRef loc path = m.heap.readRef loc path := by
            intro loc path hne
            unfold Heap.readRef; rw [hheap_preserve loc hne]

          -- Define popEnvDel: popEnv with arg sites consumed
          let popEnvDel := {popEnv with siteEnv := AssocMap.deleteAll popEnv.siteEnv argSites}
          have hpopDelWf : popEnvDel.WellFormed :=
            ⟨hpopWf.pathEnv_wf, SiteEnv.deleteAll_refs_not_root _ _ hpopWf.siteEnv_wf, hpopWf.varEnv_wf⟩

          -- stmt_typed: weaken from ccDelEnv to popEnvDel
          have hstmt_typed_pop : typecheck_stmt lenv popEnvDel cont retTypes := by
            have hiso_output : ∀ s ∈ results, ∀ bt r bk,
                lookup popEnv.siteEnv s = some (.ref bt r bk) →
                ∀ w, w ≠ r → (∀ p, ¬⟦popEnv.pathEnv.paths (w, r)⟧ p) ∧
                               (∀ p, ¬⟦popEnv.pathEnv.paths (r, w)⟧ p) := by
              intro s hs bt r bk hse w hw
              have hr_out : r ∈ outRefs := by
                rcases populate_call_outputs_siteEnv_ref_origin env popEnv results rets
                  outRefs hpop s bt r bk hse with h_old | h_out
                · rw [hfresh_sites_none s hs] at h_old; cases h_old
                · exact h_out
              exact houtRef_isolated r hr_out w hw
            -- subsumption: cc(popEnv) subsumes popEnv → ccDelEnv subsumes popEnvDel
            have hsub_cc := call_connect_subsumes_self popEnv results argSites
              hpopSiteTracked hpopSle hiso_output
            have hsub_del : TypeEnv.subsumes
                (let env'' := call_connect_inputs_outputs popEnv results argSites
                 {env'' with siteEnv := AssocMap.deleteAll env''.siteEnv argSites})
                popEnvDel := by
              obtain ⟨σ, hid, hve, hse, hrefs, hinj, hnonroot, hpaths⟩ := hsub_cc
              exact ⟨σ, hid, hve, SiteEnvSubstEquiv_deleteAll σ _ _ argSites hse,
                     hrefs, hinj, hnonroot, hpaths⟩
            -- WF for ccDelEnv
            have hwf_ccDel : (let env'' := call_connect_inputs_outputs popEnv results argSites
                {env'' with siteEnv := AssocMap.deleteAll env''.siteEnv argSites}).WellFormed := by
              have hwf_cc := call_connect_inputs_outputs_wf popEnv results argSites hpopWf
              exact ⟨hwf_cc.pathEnv_wf, SiteEnv.deleteAll_refs_not_root _ _ hwf_cc.siteEnv_wf, hwf_cc.varEnv_wf⟩
            -- site_tracked for ccDelEnv
            have hst_ccDel : ∀ s bt r bk,
                lookup (let env'' := call_connect_inputs_outputs popEnv results argSites
                  {env'' with siteEnv := AssocMap.deleteAll env''.siteEnv argSites}).siteEnv s =
                  some (.ref bt r bk) →
                r ∈ (let env'' := call_connect_inputs_outputs popEnv results argSites
                  {env'' with siteEnv := AssocMap.deleteAll env''.siteEnv argSites}).pathEnv.refs := by
              intro s bt r bk hlook
              have hlook_orig := lookup_deleteAll_some
                (call_connect_inputs_outputs popEnv results argSites).siteEnv argSites s _ hlook
              rw [call_connect_siteEnv] at hlook_orig
              exact call_connect_refs_mono popEnv results argSites r
                (hpopSiteTracked s bt r bk hlook_orig)
            -- var_tracked for ccDelEnv
            have hvt_ccDel : ∀ x bt r bk ms,
                lookup (let env'' := call_connect_inputs_outputs popEnv results argSites
                  {env'' with siteEnv := AssocMap.deleteAll env''.siteEnv argSites}).varEnv x =
                  some (.validVar, .ref bt r bk, ms) →
                r ∈ (let env'' := call_connect_inputs_outputs popEnv results argSites
                  {env'' with siteEnv := AssocMap.deleteAll env''.siteEnv argSites}).pathEnv.refs := by
              intro x bt r bk ms hlook
              rw [call_connect_varEnv] at hlook
              exact call_connect_refs_mono popEnv results argSites r
                (hpopVarTracked x bt r bk ms hlook)
            -- RefsUnique for ccDelEnv
            have huniq_ccDel : RefsUnique
                (call_connect_inputs_outputs popEnv results argSites).varEnv
                (AssocMap.deleteAll (call_connect_inputs_outputs popEnv results argSites).siteEnv argSites) := by
              rw [call_connect_varEnv, call_connect_siteEnv]
              exact RefsUnique_deleteAll _ _ _ hpopUnique
            exact typecheck_stmt_weaken lenv _ popEnvDel cont retTypes hcont_cc
              hsub_del
              (by simp only [call_connect_funEnv]; rfl)
              hwf_ccDel
              hpopDelWf
              hst_ccDel
              hvt_ccDel
              huniq_ccDel
              (by exact hpopPtnm)
              (by exact hpopPfnm)
              (by exact hpopSle)

          -- no_paths_to_root
          have hno_paths_to_root_pop : ∀ u p,
              interpret_regex (popEnv.pathEnv.paths (u, .root)) p →
              u = .root ∧ p = [] := by
            intro u p hp
            by_cases hu_out : u ∈ outRefs
            · exact absurd hp ((houtRef_isolated u hu_out .root
                (houtRef_not_root u hu_out).symm).2 p)
            · rw [hpaths_preserved u .root hu_out hroot_not_out] at hp
              exact hwt.no_paths_to_root u p hp

          -- root_path_coherence
          have hroot_coherence_pop : ∀ v y rest_pe, v ∈ popEnv.pathEnv.refs →
              interpret_regex (popEnv.pathEnv.paths (.root, v))
                (.root_to_var y :: rest_pe) →
              ∀ loc_v path_v, callerRmap.map v = some (loc_v, path_v) →
              ∀ loc_y, lookup m.frame.varStore y = some (some loc_y) →
              loc_v = loc_y → path_v = fieldPathOf rest_pe := by
            intro v y rest_pe _hv_in hp loc_v path_v hrmap_v loc_y hlookup_y hloc_eq
            have hv_env : v ∈ env.pathEnv.refs := by
              by_contra h; rw [hcrmap_none v h] at hrmap_v; cases hrmap_v
            have hv_not_out : v ∉ outRefs := fun h => (houtRef_not_in_refs v h) hv_env
            rw [hpaths_preserved .root v hroot_not_out hv_not_out] at hp
            rw [hcrmap_agree v hv_env] at hrmap_v
            exact hwt.root_path_coherence v y rest_pe hv_env hp loc_v path_v hrmap_v
              loc_y hlookup_y hloc_eq

          -- unmapped_isolated
          have hunmapped_isolated_pop : ∀ r, callerRmap.map r = none → r ≠ .root →
              r ∈ popEnv.pathEnv.refs →
              ∀ u, u ≠ r →
                (∀ p, ¬interpret_regex (popEnv.pathEnv.paths (u, r)) p) ∧
                (∀ p, ¬interpret_regex (popEnv.pathEnv.paths (r, u)) p) := by
            intro r hr_none hr_ne_root hr_in u hu
            have hr_not_env : r ∉ env.pathEnv.refs := by
              intro hr_env
              rcases hwt.refs_tracked_mapped r hr_env with rfl | hne
              · exact hr_ne_root rfl
              · rw [hcrmap_agree r hr_env] at hr_none; exact hne hr_none
            have hr_out : r ∈ outRefs := by
              rcases populate_call_outputs_refs_bounded env popEnv results rets outRefs
                hpop r hr_in with h | h
              · exact absurd h hr_not_env
              · exact h
            exact houtRef_isolated r hr_out u hu

          -- rmap_paths
          have hrmap_paths_pop : ∀ r1 r2, r1 ∈ popEnv.pathEnv.refs →
              r2 ∈ popEnv.pathEnv.refs →
              ∀ p, interpret_regex (popEnv.pathEnv.paths (r1, r2)) p →
              PathReflectedInHeap callerRmap heap' r1 r2 p := by
            intro r1 r2 hr1 hr2 p hp
            by_cases hr1_env : r1 ∈ env.pathEnv.refs <;>
              by_cases hr2_env : r2 ∈ env.pathEnv.refs
            · -- Both in env.pathEnv.refs
              have hr1_not_out : r1 ∉ outRefs :=
                fun h => (houtRef_not_in_refs r1 h) hr1_env
              have hr2_not_out : r2 ∉ outRefs :=
                fun h => (houtRef_not_in_refs r2 h) hr2_env
              rw [hpaths_preserved r1 r2 hr1_not_out hr2_not_out] at hp
              have hrp := hwt.rmap_paths r1 r2 hr1_env hr2_env p hp
              unfold PathReflectedInHeap at hrp ⊢
              rw [hcrmap_agree r1 hr1_env, hcrmap_agree r2 hr2_env]
              cases hrm1 : rmap.map r1 with
              | none => trivial
              | some p1 =>
                cases hrm2 : rmap.map r2 with
                | none => simp
                | some p2 =>
                  simp only [hrm1, hrm2] at hrp ⊢
                  obtain ⟨loc1, path1⟩ := p1
                  obtain ⟨loc2, path2⟩ := p2
                  simp only at hrp ⊢
                  intro hloc_eq
                  obtain ⟨hpath_eq, hreadRef_m⟩ := hrp hloc_eq
                  have hloc2_ne := readRef_implies_read m.heap loc2 path2 hreadRef_m
                  exact ⟨hpath_eq,
                    by rw [hreadRef_preserved_gen loc2 path2 hloc2_ne]; exact hreadRef_m⟩
            · -- r1 ∈ env, r2 ∉ env → callerRmap.map r2 = none → True
              unfold PathReflectedInHeap
              rw [hcrmap_none r2 hr2_env]
              cases callerRmap.map r1 <;> trivial
            · -- r1 ∉ env → callerRmap.map r1 = none → True
              unfold PathReflectedInHeap
              rw [hcrmap_none r1 hr1_env]
              trivial
            · -- Both not in env → both unmapped → True
              unfold PathReflectedInHeap
              rw [hcrmap_none r1 hr1_env]
              trivial

          -- types_conform
          have htypes_conform_pop : types_conform popEnv.siteEnv results fdef.returnType :=
            hfdef_rets ▸ populate_call_outputs_types_conform env popEnv results rets outRefs
              hnodup_sites hpop

          -- Disjointness: result sites are not in argSites
          have hresults_disj : ∀ s ∈ results, s ∉ argSites := by
            intro s hs hmem
            obtain ⟨τ, hlook⟩ := types_conform_site_has_type env.siteEnv argSites params s
              htypes_conf hmem
            rw [hfresh_sites_none s hs] at hlook; cases hlook

          -- types_conform for popEnvDel
          have htypes_conform_del : types_conform popEnvDel.siteEnv results fdef.returnType :=
            types_conform_ext htypes_conform_pop
              (fun s hs => (lookup_deleteAll_not_mem popEnv.siteEnv argSites s
                (hresults_disj s hs)).symm)

          -- Provide StackSafe witnesses
          exact ⟨popEnvDel, lenv, retTypes, callerRmap,
            ⟨hpopEnumEnv,
             hpopDelWf,
             hstmt_typed_pop,
             hwt.blocks_typed,
             hwt.lenv_empty_siteEnv,
             hwt.lenv_wf,
             hwt.lenv_var_tracked,
             hwt.lenv_var_unique,
             by intro L envL h; rw [hpopFunEnv]; exact hwt.lenv_funEnv_eq L envL h,
             hwt.lenv_labels_in_blocks,
             hwt.has_return_info,
             by show ∀ _ _, _ → FunTypeSafe _ _ popEnvDel.enumEnv
                simp only [show popEnvDel.enumEnv = env.enumEnv from hpopEnumEnv]
                exact hwt.funEnv_typed,
             by intro x bt r bk ms h; rw [hpopVarEnv] at h
                exact hpopRefsMono r (hwt.varEnv_refs_in_pathEnv x bt r bk ms h),
             by intro s bt r bk h
                exact hpopSiteTracked s bt r bk
                  (lookup_deleteAll_some popEnv.siteEnv argSites s _ h),
             RefsUnique_deleteAll _ _ _ hpopUnique,
             hcrmap_root_none,
             hno_paths_to_root_pop,
             hroot_coherence_pop,
             hpopPfnm,
             hpopPtnm,
             hpopSle,
             hunmapped_isolated_pop,
             by intro s bt r bk hs h
                exact hresult_unmapped s bt r bk hs
                  (lookup_deleteAll_some popEnv.siteEnv argSites s _ h),
             by intro r hr
                rcases hrefs_tracked_or_result r hr with rfl | hne | ⟨s, bt, bk, hs, hlook⟩
                · exact Or.inl rfl
                · exact Or.inr (Or.inl hne)
                · right; right
                  exact ⟨s, bt, bk, hs,
                    by rw [lookup_deleteAll_not_mem popEnv.siteEnv argSites s
                         (hresults_disj s hs)]; exact hlook⟩,
             by intro x isv τ ms hv; rw [← hpopEnumEnv] at hvar_con; exact hvar_con x isv τ ms hv,
             by intro s τ h hs_nr
                rw [← hpopEnumEnv] at hsite_con
                exact hsite_con s τ
                  (lookup_deleteAll_some popEnv.siteEnv argSites s _ h) hs_nr,
             hrmap_live,
             hrmap_paths_pop,
             allocArgs_heap_loc_bound' m.heap fdef.params argVals heap' paramVarStore
               hallocArgs hwt.heap_loc_bound,
             by intro y loc_y hvar
                have hlt := hwt.varStore_locs_bound y loc_y hvar
                exact Nat.lt_of_lt_of_le hlt (allocArgs_nextLoc_le m.heap fdef.params
                  argVals heap' paramVarStore hallocArgs),
             by intro r bt loc path hcrmap hwitness
                rw [← hpopEnumEnv] at hrmap_ht
                apply hrmap_ht r bt loc path hcrmap
                rcases hwitness with ⟨x, bk, ms, hv⟩ | ⟨s, bk, hs, hs_nr⟩
                · exact Or.inl ⟨x, bk, ms, hv⟩
                · exact Or.inr ⟨s, bk,
                    lookup_deleteAll_some popEnv.siteEnv argSites s _ hs, hs_nr⟩,
             by intro fn sig h; rw [hpopFunEnv] at h
                exact hwt.funEnv_sig_consistent fn sig h,
             htypes_conform_del⟩,
            htail⟩

-- ============================================================
-- Part 8a-vec: Vector preservation helpers
-- ============================================================

-- Helper: if all elements have readSite values, filterMap has same length
private theorem filterMap_readSite_length {m : Machine} {elems : List Site}
    (h : ∀ a, a ∈ elems → ∃ v, readSite m a = some v) :
    (elems.filterMap (readSite m)).length = elems.length := by
  induction elems with
  | nil => rfl
  | cons a rest ih =>
    obtain ⟨v, hv⟩ := h a (by simp)
    simp only [List.filterMap_cons, hv, List.length_cons]
    have := ih (fun b hb => h b (by simp [hb]))
    omega

private theorem preservation_vecPack (m m' : Machine) (env : TypeEnv) (lenv : LabelEnv)
    (retTypes : List ParamType) (rmap : RefMap)
    (hwt : WellTypedState m env lenv retTypes rmap)
    (hss : StackSafe env.enumEnv m.stack m.frame.returnInfo m.heap retTypes)
    (s : Site) (T : BasicMoveType) (elems : List Site) (cont : Stmt)
    (hstmt : m.frame.stmt = .letBind s (.vecPack T elems) cont)
    (hstep : step (.running m) = .running m') :
    ∃ env' lenv' retTypes' rmap',
      env'.enumEnv = env.enumEnv ∧ WellTypedState m' env' lenv' retTypes' rmap' ∧
      StackSafe env.enumEnv m'.stack m'.frame.returnInfo m'.heap retTypes' := by
  obtain ⟨hnotIn, hforall, _, hcont⟩ := inv_vecPack (by rw [← hstmt]; exact hwt.stmt_typed)
  -- All elements are initialized
  have hvals : ∀ a, a ∈ elems → ∃ v, readSite m a = some v := by
    intro a ha
    obtain ⟨v, hv, _⟩ := hwt.site_consistent a _ (hforall a ha)
    exact ⟨v, hv⟩
  -- Simplify step
  simp only [step, hstmt] at hstep
  have hlen : (elems.filterMap (readSite m)).length = elems.length :=
    filterMap_readSite_length hvals
  simp only [hlen, beq_self_eq_true, ↓reduceIte, ExecState.running.injEq] at hstep
  subst hstep
  -- New env
  refine ⟨{env with siteEnv := insert (deleteAll env.siteEnv elems) s (.basic (.tvec T))},
          lenv, retTypes, rmap, rfl, ?_, hss⟩
  -- All filterMap values have type T
  have hht_vals : ∀ v, v ∈ elems.filterMap (readSite m) → HasType env.enumEnv v T := by
    intro v hv
    rw [List.mem_filterMap] at hv
    obtain ⟨a, ha_mem, ha_read⟩ := hv
    obtain ⟨v', hv', hht⟩ := hwt.site_consistent a (.basic T) (hforall a ha_mem)
    have : v = v' := Option.some.inj (ha_read.symm.trans hv')
    subst this; exact hht
  exact {
    env_wf := TypeEnv.deleteAll_insert_wf env elems s (.basic (.tvec T)) hwt.env_wf trivial
    enumEnv_consistent := hwt.enumEnv_consistent
    enum_qualified_nodup := hwt.enum_qualified_nodup
    enum_names_nodup := hwt.enum_names_nodup
    enum_variant_nodup := hwt.enum_variant_nodup
    enum_fields_nodup := hwt.enum_fields_nodup
    defaultValues_typed := hwt.defaultValues_typed
    stmt_typed := hcont
    var_consistent := hwt.var_consistent
    site_consistent := by
      intro s' τ' hl
      by_cases heq : s' = s
      · subst heq; simp only [lookup_insert_same, Option.some.injEq] at hl; subst hl
        exact ⟨.vec T (elems.filterMap (readSite m)),
               lookup_insert_same _ _ _,
               HasType.vec _ _ hht_vals⟩
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
    funEnv_sig_consistent := hwt.funEnv_sig_consistent
    refs_tracked_mapped := hwt.refs_tracked_mapped
    lenv_labels_in_blocks := hwt.lenv_labels_in_blocks
    has_return_info := hwt.has_return_info
    varStore_locs_bound := hwt.varStore_locs_bound
  }

-- Utility: garbage_collect = delete_ref_node (definitionally)
private theorem garbage_collect_eq_delete_ref_node (pe : PathEnv) (r : Aref) :
    garbage_collect pe r = delete_ref_node pe r := by
  unfold garbage_collect delete_ref_node
  simp

-- Utility: foldl insert lookup for sites not in the list
private theorem foldl_insert_lookup_not_in
    (siteStore : AssocMap Site Value)
    (pairs : List (Site × Value)) (a : Site)
    (hnotin : a ∉ pairs.map Prod.fst) :
    lookup (pairs.foldl (fun ss (sv : Site × Value) =>
      AssocMap.insert ss sv.1 sv.2) siteStore) a
    = lookup siteStore a := by
  induction pairs generalizing siteStore with
  | nil => rfl
  | cons hd tl ih =>
    obtain ⟨s, v⟩ := hd
    simp only [List.map, List.mem_cons, not_or] at hnotin
    simp only [List.foldl_cons]
    rw [ih _ hnotin.2]
    exact lookup_insert_ne siteStore s a v hnotin.1

-- Utility: foldl insert lookup for a site that appears in the list (with nodup)
private theorem foldl_insert_lookup_mem
    (siteStore : AssocMap Site Value)
    (pairs : List (Site × Value)) (a : Site) (v : Value)
    (hnodup : List.Nodup (pairs.map Prod.fst))
    (hmem : (a, v) ∈ pairs) :
    lookup (pairs.foldl (fun ss (sv : Site × Value) =>
      AssocMap.insert ss sv.1 sv.2) siteStore) a
    = some v := by
  induction pairs generalizing siteStore with
  | nil => nomatch hmem
  | cons hd tl ih =>
    obtain ⟨s, w⟩ := hd
    simp only [List.map, List.nodup_cons] at hnodup
    obtain ⟨hnotin_tl, hnodup_tl⟩ := hnodup
    simp only [List.foldl_cons]
    simp only [List.mem_cons, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | hmem_tl
    · -- head is (a, v)
      have : a ∉ tl.map Prod.fst := hnotin_tl
      rw [foldl_insert_lookup_not_in _ _ _ this]
      exact lookup_insert_same siteStore a v
    · exact ih _ hnodup_tl hmem_tl

-- Utility: addVecSites lookup for sites not in the list
private theorem addVecSites_lookup_not_in (T : BasicMoveType) (se : AssocMap Site MoveType)
    (results : List Site) (a : Site) (hnotin : a ∉ results) :
    lookup (addVecSites T se results) a = lookup se a := by
  induction results generalizing se with
  | nil => rfl
  | cons s rest ih =>
    simp only [List.mem_cons, not_or] at hnotin
    simp only [addVecSites]
    rw [ih _ hnotin.2]
    exact lookup_insert_ne se s a _ hnotin.1

-- Utility: addVecSites lookup for a site in the list (with nodup)
private theorem addVecSites_lookup_mem (T : BasicMoveType) (se : AssocMap Site MoveType)
    (results : List Site) (a : Site) (hnodup : List.Nodup results) (hmem : a ∈ results) :
    lookup (addVecSites T se results) a = some (.basic T) := by
  induction results generalizing se with
  | nil => nomatch hmem
  | cons s rest ih =>
    simp only [addVecSites]
    simp only [List.nodup_cons] at hnodup
    simp only [List.mem_cons] at hmem
    rcases hmem with rfl | hmem_rest
    · rw [addVecSites_lookup_not_in _ _ _ _ hnodup.1]
      exact lookup_insert_same se a _
    · exact ih _ hnodup.2 hmem_rest

-- Utility: zip map fst
private theorem zip_map_fst_eq {results : List Site} {elems : List Value}
    (hlen : results.length = elems.length) :
    (results.zip elems).map Prod.fst = results := by
  induction results generalizing elems with
  | nil => simp
  | cons r rest ih =>
    cases elems with
    | nil => simp at hlen
    | cons v vs =>
      simp only [List.zip_cons_cons, List.map_cons, List.cons.injEq, true_and]
      exact ih (by simp at hlen; exact hlen)

private theorem preservation_vecUnpack (m m' : Machine) (env : TypeEnv) (lenv : LabelEnv)
    (retTypes : List ParamType) (rmap : RefMap)
    (hwt : WellTypedState m env lenv retTypes rmap)
    (hss : StackSafe env.enumEnv m.stack m.frame.returnInfo m.heap retTypes)
    (T : BasicMoveType) (results : List Site) (src : Site) (cont : Stmt)
    (hstmt : m.frame.stmt = .vecUnpack T results src cont)
    (hstep : step (.running m) = .running m') :
    ∃ env' lenv' retTypes' rmap',
      env'.enumEnv = env.enumEnv ∧ WellTypedState m' env' lenv' retTypes' rmap' ∧
      StackSafe env.enumEnv m'.stack m'.frame.returnInfo m'.heap retTypes' := by
  obtain ⟨hlookup_src, hfresh, hnodup, hcont⟩ := inv_vecUnpack (by rw [← hstmt]; exact hwt.stmt_typed)
  -- Get vector value from site_consistent
  obtain ⟨vsrc, hvsrc, hmatch_src⟩ := hwt.site_consistent src _ hlookup_src
  simp only [ValueMatchesType] at hmatch_src
  obtain ⟨elems, hvec_eq⟩ := HasType.vec_elems hmatch_src
  subst hvec_eq
  -- All elements have type T
  have helem_typed : ∀ v, v ∈ elems → HasType env.enumEnv v T := by
    cases hmatch_src with | vec _ _ h => exact h
  -- Simplify step
  have hrs : readSite m src = some (.vec T elems) := by unfold readSite; exact hvsrc
  simp only [step, hstmt, hrs] at hstep
  -- Handle length check
  by_cases hlen : elems.length == results.length <;> simp only [hlen, ↓reduceIte] at hstep
  · -- Length matches
    simp only [ExecState.running.injEq] at hstep; subst hstep
    have hlen_eq : results.length = elems.length := by
      simp only [beq_iff_eq] at hlen; omega
    refine ⟨{env with siteEnv := addVecSites T (delete env.siteEnv src) results},
            lenv, retTypes, rmap, rfl, ?_, hss⟩
    exact {
      env_wf := by
        constructor
        · exact hwt.env_wf.pathEnv_wf
        · exact addVecSites_refs_not_root T _ results
            (SiteEnv.delete_refs_not_root env.siteEnv src hwt.env_wf.siteEnv_wf)
        · exact hwt.env_wf.varEnv_wf
      enumEnv_consistent := hwt.enumEnv_consistent
      enum_qualified_nodup := hwt.enum_qualified_nodup
      enum_names_nodup := hwt.enum_names_nodup
      enum_variant_nodup := hwt.enum_variant_nodup
      enum_fields_nodup := hwt.enum_fields_nodup
      defaultValues_typed := hwt.defaultValues_typed
      stmt_typed := hcont
      var_consistent := hwt.var_consistent
      site_consistent := by
        intro s' τ' hlookup_s'
        by_cases hs'_in : s' ∈ results
        · -- s' is a result site → type is .basic T
          rw [addVecSites_lookup_mem T _ results s' hnodup hs'_in] at hlookup_s'
          cases hlookup_s'
          -- Need value from foldl and HasType proof
          have hzip_nodup : List.Nodup ((results.zip elems).map Prod.fst) := by
            rw [zip_map_fst_eq hlen_eq]; exact hnodup
          -- s' ∈ results → ∃ v, (s', v) ∈ results.zip elems
          obtain ⟨v_s', hmem_zip⟩ := exists_mem_zip_right hlen_eq hs'_in
          have hlookup_ss := foldl_insert_lookup_mem m.frame.siteStore _ s' v_s'
            hzip_nodup hmem_zip
          have hv_mem : v_s' ∈ elems := (List.of_mem_zip hmem_zip).2
          exact ⟨v_s', hlookup_ss, helem_typed _ hv_mem⟩
        · -- s' not in results → use old site_consistent
          rw [addVecSites_lookup_not_in T _ results s' hs'_in] at hlookup_s'
          have hne_src : s' ≠ src := by
            intro h; subst h; rw [lookup_delete_same] at hlookup_s'; cases hlookup_s'
          rw [lookup_delete_ne _ src s' hne_src] at hlookup_s'
          obtain ⟨v, hv, hmatch⟩ := hwt.site_consistent s' τ' hlookup_s'
          have hlookup_ss := foldl_insert_lookup_not_in m.frame.siteStore
            (results.zip elems) s' (by rw [zip_map_fst_eq hlen_eq]; exact hs'_in)
          exact ⟨v, hlookup_ss ▸ hv, hmatch⟩
      rmap_live := hwt.rmap_live
      rmap_paths := hwt.rmap_paths
      varEnv_refs_in_pathEnv := hwt.varEnv_refs_in_pathEnv
      siteEnv_refs_in_pathEnv := by
        intro s' bt r bk hlookup_s'
        by_cases hs'_in : s' ∈ results
        · rw [addVecSites_lookup_mem T _ results s' hnodup hs'_in] at hlookup_s'
          cases hlookup_s'
        · rw [addVecSites_lookup_not_in T _ results s' hs'_in] at hlookup_s'
          have hne_src : s' ≠ src := by
            intro h; subst h; rw [lookup_delete_same] at hlookup_s'; cases hlookup_s'
          rw [lookup_delete_ne _ src s' hne_src] at hlookup_s'
          exact hwt.siteEnv_refs_in_pathEnv s' bt r bk hlookup_s'
      live_refs_unique := by
        intro r
        refine ⟨?_, ?_, ?_⟩
        · intro x bt bk ms s' bt' bk' hvar hlookup_s'
          by_cases hs'_in : s' ∈ results
          · rw [addVecSites_lookup_mem T _ results s' hnodup hs'_in] at hlookup_s'
            cases hlookup_s'
          · rw [addVecSites_lookup_not_in T _ results s' hs'_in] at hlookup_s'
            have hne_src : s' ≠ src := by
              intro h; subst h; rw [lookup_delete_same] at hlookup_s'; cases hlookup_s'
            rw [lookup_delete_ne _ src s' hne_src] at hlookup_s'
            exact (hwt.live_refs_unique r).1 x bt bk ms s' bt' bk' hvar hlookup_s'
        · intro s1 s2 bt1 bt2 bk1 bk2 hne12 hs1 hs2
          have get_old : ∀ s bt' bk', lookup (addVecSites T (delete env.siteEnv src) results) s
              = some (.ref bt' r bk') → lookup env.siteEnv s = some (.ref bt' r bk') := by
            intro s bt' bk' hs
            by_cases hs_in : s ∈ results
            · rw [addVecSites_lookup_mem T _ results s hnodup hs_in] at hs; cases hs
            · rw [addVecSites_lookup_not_in T _ results s hs_in] at hs
              have hne_src : s ≠ src := by
                intro h; subst h; rw [lookup_delete_same] at hs; cases hs
              rw [lookup_delete_ne _ src s hne_src] at hs; exact hs
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
        · by_cases hs'_in : s' ∈ results
          · rw [addVecSites_lookup_mem T _ results s' hnodup hs'_in] at hsite; cases hsite
          · rw [addVecSites_lookup_not_in T _ results s' hs'_in] at hsite
            have hne_src : s' ≠ src := by
              intro h; subst h; rw [lookup_delete_same] at hsite; cases hsite
            rw [lookup_delete_ne _ src s' hne_src] at hsite
            exact Or.inr ⟨s', bk, hsite⟩
      funEnv_sig_consistent := hwt.funEnv_sig_consistent
      refs_tracked_mapped := hwt.refs_tracked_mapped
      lenv_labels_in_blocks := hwt.lenv_labels_in_blocks
      has_return_info := hwt.has_return_info
      varStore_locs_bound := hwt.varStore_locs_bound
    }
  · -- Length mismatch → contradiction
    simp [Bool.false_eq_true] at hstep

private theorem preservation_vecLen (m m' : Machine) (env : TypeEnv) (lenv : LabelEnv)
    (retTypes : List ParamType) (rmap : RefMap)
    (hwt : WellTypedState m env lenv retTypes rmap)
    (hss : StackSafe env.enumEnv m.stack m.frame.returnInfo m.heap retTypes)
    (s : Site) (src : Site) (cont : Stmt)
    (hstmt : m.frame.stmt = .letBind s (.vecLen src) cont)
    (hstep : step (.running m) = .running m') :
    ∃ env' lenv' retTypes' rmap',
      env'.enumEnv = env.enumEnv ∧ WellTypedState m' env' lenv' retTypes' rmap' ∧
      StackSafe env.enumEnv m'.stack m'.frame.returnInfo m'.heap retTypes' := by
  obtain ⟨T, r, isBor, hlookup_src, hnotIn, hcont⟩ := inv_vecLen (by rw [← hstmt]; exact hwt.stmt_typed)
  -- Get ref value from site_consistent
  obtain ⟨vsrc, hvsrc, hmatch_src⟩ := hwt.site_consistent src _ hlookup_src
  simp only [ValueMatchesType] at hmatch_src
  obtain ⟨loc, path, hveq, hrmap⟩ := hmatch_src
  subst hveq
  -- Get the vector from heap via rmap_has_type
  obtain ⟨heap_val, hread_heap, hht_heap⟩ := hwt.rmap_has_type r (.tvec T) loc path hrmap
    (Or.inr ⟨src, isBor, hlookup_src⟩)
  obtain ⟨elems, rfl⟩ := HasType.vec_elems hht_heap
  -- Simplify step
  have hrs : readSite m src = some (.ref loc path) := by unfold readSite; exact hvsrc
  have hread : m.heap.readRef loc path = some (.vec T elems) := hread_heap
  simp only [step, hstmt, hrs, hread, ExecState.running.injEq] at hstep
  subst hstep
  -- r is not root
  have hr_not_root : r ≠ .root := hwt.env_wf.siteEnv_wf src _ hlookup_src
  -- New env
  refine ⟨{env with siteEnv := insert (delete env.siteEnv src) s (.basic .u64),
                     pathEnv := delete_ref_node env.pathEnv r},
          lenv, retTypes, rmap, rfl, ?_, hss⟩
  exact {
    env_wf := ⟨delete_ref_node_wellformed env.pathEnv r hwt.env_wf.pathEnv_wf hr_not_root,
               SiteEnv.insert_refs_not_root (delete env.siteEnv src) s (.basic .u64)
                 (SiteEnv.delete_refs_not_root env.siteEnv src hwt.env_wf.siteEnv_wf) trivial,
               hwt.env_wf.varEnv_wf⟩
    enumEnv_consistent := hwt.enumEnv_consistent
    enum_qualified_nodup := hwt.enum_qualified_nodup
    enum_names_nodup := hwt.enum_names_nodup
    enum_variant_nodup := hwt.enum_variant_nodup
    enum_fields_nodup := hwt.enum_fields_nodup
    defaultValues_typed := hwt.defaultValues_typed
    stmt_typed := hcont
    var_consistent := hwt.var_consistent
    site_consistent := by
      intro s' τ' hl
      by_cases heq : s' = s
      · subst heq; simp only [lookup_insert_same, Option.some.injEq] at hl; subst hl
        exact ⟨.int elems.length, lookup_insert_same _ _ _, HasType.int _⟩
      · rw [lookup_insert_ne _ s s' _ heq] at hl
        have hne_src : s' ≠ src := by
          intro h; subst h; rw [lookup_delete_same] at hl; simp at hl
        rw [lookup_delete_ne _ src s' hne_src] at hl
        obtain ⟨v, hv, hm⟩ := hwt.site_consistent s' τ' hl
        exact ⟨v, by rw [lookup_insert_ne _ s s' _ heq]; exact hv, hm⟩
    rmap_live := by
      intro r' loc' path' hr' hrmap'
      have hr'_old : r' ∈ env.pathEnv.refs := by
        have hr'' : r' ∈ (delete_ref_node env.pathEnv r).refs := hr'
        simp only [delete_ref_node_refs, List.mem_filter, decide_eq_true_eq] at hr''; exact hr''.1
      exact hwt.rmap_live r' loc' path' hr'_old hrmap'
    rmap_paths := rmap_paths_delete_ref_node env m rmap r hwt.rmap_paths
    varEnv_refs_in_pathEnv :=
      varEnv_refs_in_pathEnv_delete_ref_node hwt r src (.tvec T) isBor hlookup_src
    siteEnv_refs_in_pathEnv := by
      intro s' bt r' bk hl
      by_cases heqs : s' = s
      · subst heqs; rw [lookup_insert_same] at hl; simp at hl
      · rw [lookup_insert_ne _ s s' _ heqs] at hl
        exact siteEnv_refs_in_pathEnv_delete_ref_node hwt r src (.tvec T) isBor hlookup_src s' bt r' bk hl
    live_refs_unique := by
      intro r'
      refine ⟨fun x' bt bk ms' s' bt' bk' hvar' hs' => ?_,
              fun s1 s2 bt1 bt2 bk1 bk2 hne hs1 hs2 => ?_,
              fun x1 x2 bt1 bt2 bk1 bk2 ms1 ms2 hne hx1 hx2 =>
                (hwt.live_refs_unique r').2.2 x1 x2 bt1 bt2 bk1 bk2 ms1 ms2 hne hx1 hx2⟩
      · by_cases heqs : s' = s
        · subst heqs; rw [lookup_insert_same] at hs'; simp at hs'
        · rw [lookup_insert_ne _ s s' _ heqs] at hs'
          exact (live_refs_unique_delete_site hwt src r').1 x' bt bk ms' s' bt' bk' hvar' hs'
      · by_cases heq1 : s1 = s
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
      intro r' bt loc' path' hrmap' hcond
      apply hwt.rmap_has_type r' bt loc' path' hrmap'
      rcases hcond with ⟨x, bk, ms, hvar⟩ | ⟨s', bk, hsite⟩
      · exact Or.inl ⟨x, bk, ms, hvar⟩
      · by_cases heqs : s' = s
        · subst heqs; simp [lookup_insert_same] at hsite
        · rw [lookup_insert_ne _ s s' _ heqs] at hsite
          have hne_src : s' ≠ src := by
            intro h; subst h; rw [lookup_delete_same] at hsite; simp at hsite
          rw [lookup_delete_ne _ src s' hne_src] at hsite
          exact Or.inr ⟨s', bk, hsite⟩
    funEnv_sig_consistent := hwt.funEnv_sig_consistent
    refs_tracked_mapped := by
      intro ref href
      simp only [delete_ref_node_refs, List.mem_filter, decide_eq_true_eq] at href
      exact hwt.refs_tracked_mapped ref href.1
    lenv_labels_in_blocks := hwt.lenv_labels_in_blocks
    has_return_info := hwt.has_return_info
    varStore_locs_bound := hwt.varStore_locs_bound
  }

-- For vecPopBack, vecPushBack, vecSwap: convert garbage_collect to delete_ref_node and reuse lemmas
private theorem preservation_vecPopBack (m m' : Machine) (env : TypeEnv) (lenv : LabelEnv)
    (retTypes : List ParamType) (rmap : RefMap)
    (hwt : WellTypedState m env lenv retTypes rmap)
    (hss : StackSafe env.enumEnv m.stack m.frame.returnInfo m.heap retTypes)
    (s : Site) (src : Site) (cont : Stmt)
    (hstmt : m.frame.stmt = .letBind s (.vecPopBack src) cont)
    (hstep : step (.running m) = .running m') :
    ∃ env' lenv' retTypes' rmap',
      env'.enumEnv = env.enumEnv ∧ WellTypedState m' env' lenv' retTypes' rmap' ∧
      StackSafe env.enumEnv m'.stack m'.frame.returnInfo m'.heap retTypes' := by
  obtain ⟨T, r, hlookup_src, houtbound, hnotIn, hcont⟩ :=
    inv_vecPopBack (by rw [← hstmt]; exact hwt.stmt_typed)
  -- Get ref value from site_consistent
  obtain ⟨vsrc, hvsrc, hmatch_src⟩ := hwt.site_consistent src _ hlookup_src
  simp only [ValueMatchesType] at hmatch_src
  obtain ⟨loc, path, hveq, hrmap⟩ := hmatch_src
  subst hveq
  -- r not root
  have hr_not_root : r ≠ .root := hwt.env_wf.siteEnv_wf src _ hlookup_src
  -- Get vector from heap
  obtain ⟨heap_val, hread_heap, hht_heap⟩ := hwt.rmap_has_type r (.tvec T) loc path hrmap
    (Or.inr ⟨src, .siteBorrowMut, hlookup_src⟩)
  obtain ⟨elems, rfl⟩ := HasType.vec_elems hht_heap
  -- Simplify step
  have hrs : readSite m src = some (.ref loc path) := by unfold readSite; exact hvsrc
  simp only [step, hstmt, hrs] at hstep
  simp only [hread_heap] at hstep
  -- Split on getLast?
  cases hgl : elems.getLast? with
  | none =>
    -- Empty vector → vectorError → contradiction
    simp [hgl] at hstep
  | some lastVal =>
    -- writeRef must succeed (rmap_live)
    have hread_ne_none : m.heap.readRef loc path ≠ none := by rw [hread_heap]; exact Option.some_ne_none _
    obtain ⟨heap', hwrite⟩ :=
      readRef_ne_none_implies_writeRef_ne_none m.heap loc path (.vec T elems.dropLast) hread_ne_none
    simp only [hgl] at hstep
    simp only [hwrite, ExecState.running.injEq] at hstep
    subst hstep
    -- garbage_collect = delete_ref_node
    rw [garbage_collect_eq_delete_ref_node] at hcont
    -- The popped element has type T
    have hlast_mem : lastVal ∈ elems := by
      have hne : elems ≠ [] := by intro h; subst h; simp at hgl
      have := List.getLast?_eq_some_getLast hne
      rw [hgl] at this; cases this
      exact List.getLast_mem hne
    have hht_last : HasType env.enumEnv lastVal T := by
      cases hht_heap with | vec _ _ h => exact h _ hlast_mem
    -- HasType for the remaining vector
    have hht_remaining : HasType env.enumEnv (.vec T elems.dropLast) (.tvec T) := by
      cases hht_heap with | vec _ _ h =>
        exact HasType.vec elems.dropLast T (fun v hv => h v (List.dropLast_subset elems hv))
    have hcheck_empty := check_outbound_only_empty env.pathEnv r houtbound
    -- New env
    refine ⟨{env with siteEnv := insert (delete env.siteEnv src) s (.basic T),
                       pathEnv := delete_ref_node env.pathEnv r},
            lenv, retTypes, rmap, rfl, ?_,
            stackSafe_heap_writeRef env.enumEnv m.stack m.frame.returnInfo m.heap heap' loc path
              (.vec T elems.dropLast) (.vec T elems) (.tvec T) hss hwrite hread_heap
              hht_heap hht_remaining
              (fun suffix hne_s hread => by cases suffix with | nil => exact absurd rfl hne_s | cons f rest => simp [readPath] at hread)
              (fun suffix hne_s => by cases suffix with | nil => exact absurd rfl hne_s | cons f rest => simp [typeAtPathV])⟩
    exact {
      env_wf := ⟨delete_ref_node_wellformed env.pathEnv r hwt.env_wf.pathEnv_wf hr_not_root,
                 SiteEnv.insert_refs_not_root (delete env.siteEnv src) s (.basic T)
                   (SiteEnv.delete_refs_not_root env.siteEnv src hwt.env_wf.siteEnv_wf) trivial,
                 hwt.env_wf.varEnv_wf⟩
      enumEnv_consistent := hwt.enumEnv_consistent
      enum_qualified_nodup := hwt.enum_qualified_nodup
      enum_names_nodup := hwt.enum_names_nodup
      enum_variant_nodup := hwt.enum_variant_nodup
      enum_fields_nodup := hwt.enum_fields_nodup
      defaultValues_typed := hwt.defaultValues_typed
      stmt_typed := hcont
      var_consistent := by
        intro x isv τ ms hvar
        have hvc := hwt.var_consistent x isv τ ms hvar
        cases isv with
        | validVar =>
          dsimp only at hvc ⊢
          obtain ⟨loc_x, v_x, hvarStore, hread_x, hmatch_x⟩ := hvc
          by_cases hloc : loc = loc_x
          · subst hloc
            have ⟨newRootVal, hwp, hread_new⟩ :
                ∃ nv, writePath v_x path (.vec T elems.dropLast) = some nv ∧ heap'.read loc = some nv := by
              simp only [Heap.writeRef, bind, Option.bind, hread_x] at hwrite
              cases hwp' : writePath v_x path (.vec T elems.dropLast) with
              | none => simp [hwp'] at hwrite
              | some nv =>
                simp [hwp'] at hwrite
                exact ⟨nv, rfl, by rw [← hwrite]; simp [Heap.write, Heap.read, lookup_insert_same]⟩
            refine ⟨loc, newRootVal, hvarStore, hread_new, ?_⟩
            cases τ with
            | basic bt_x =>
              dsimp only [ValueMatchesType] at hmatch_x ⊢
              exact writePath_preserves_HasType_generalV v_x path (.vec T elems.dropLast) newRootVal bt_x
                hmatch_x hwp (by
                  intro bt_leaf htapV
                  have hread_leaf : readPath v_x path = some (.vec T elems) := by
                    simp only [Heap.readRef, bind, Option.bind, hread_x] at hread_heap
                    exact hread_heap
                  obtain ⟨u, hread_u, hht_u⟩ :=
                    HasType_typeAtPathV v_x bt_x path bt_leaf hmatch_x htapV
                  rw [hread_leaf] at hread_u
                  simp only [Option.some.injEq] at hread_u; subst hread_u
                  exact HasType_transfer hht_u hht_heap hht_remaining)
            | ref bt_ref r_ref bk_ref =>
              exfalso
              dsimp only [ValueMatchesType] at hmatch_x
              obtain ⟨loc', path', hveq, _⟩ := hmatch_x
              rw [hveq] at hwp hread_x
              cases path with
              | cons f rest => simp [writePath] at hwp
              | nil =>
                simp only [Heap.readRef, bind, Option.bind, hread_x, readPath,
                            Option.some.injEq] at hread_heap
                rw [← hread_heap] at hht_heap
                exact HasType_not_ref loc' path' T.tvec hht_heap
          · -- Different location: heap value unchanged
            have hread_diff : heap'.read loc_x = m.heap.read loc_x := by
              simp only [Heap.writeRef, bind, Option.bind] at hwrite
              cases hbase : m.heap.read loc with
              | none => simp [hbase] at hwrite
              | some baseVal =>
                simp [hbase] at hwrite
                cases hwp' : writePath baseVal path (.vec T elems.dropLast) with
                | none => simp [hwp'] at hwrite
                | some newVal =>
                  simp [hwp'] at hwrite; rw [← hwrite]
                  exact heap_write_preserves_read m.heap loc loc_x newVal hloc
            exact ⟨loc_x, v_x, hvarStore, hread_diff.trans hread_x, hmatch_x⟩
        | invalidVar =>
          dsimp only at hvc ⊢
          rcases hvc with hvc_none | ⟨loc_x, hvc_some⟩
          · exact Or.inl hvc_none
          · exact Or.inr ⟨loc_x, hvc_some⟩
      site_consistent := by
        intro s' τ' hl
        by_cases heq : s' = s
        · subst heq; simp only [lookup_insert_same, Option.some.injEq] at hl; subst hl
          exact ⟨lastVal, lookup_insert_same _ _ _, hht_last⟩
        · rw [lookup_insert_ne _ s s' _ heq] at hl
          have hne_src : s' ≠ src := by
            intro h; subst h; rw [lookup_delete_same] at hl; simp at hl
          rw [lookup_delete_ne _ src s' hne_src] at hl
          obtain ⟨v, hv, hm⟩ := hwt.site_consistent s' τ' hl
          exact ⟨v, by rw [lookup_insert_ne _ s s' _ heq]; exact hv, hm⟩
      rmap_live := by
        intro r' loc' path' hr'_tracked hrmap'
        have hr'_old : r' ∈ env.pathEnv.refs := by
          have hr'' : r' ∈ (delete_ref_node env.pathEnv r).refs := hr'_tracked
          simp only [delete_ref_node_refs, List.mem_filter, decide_eq_true_eq] at hr''; exact hr''.1
        have hlive := hwt.rmap_live r' loc' path' hr'_old hrmap'
        by_cases hloc : loc = loc'
        · subst hloc
          exact heap_writeRef_preserves_readRef_same_loc m.heap loc path path' (.vec T elems.dropLast) heap'
            hwrite hlive (by
              intro suffix hsuffix
              cases suffix with
              | nil => simp [readPath]
              | cons sf srest =>
                have hleaf_suffix : readPath (.vec T elems) (sf :: srest) ≠ none := by
                  simp only [Heap.readRef, bind, Option.bind] at hlive hread_heap
                  cases hbase : m.heap.read loc with
                  | none => simp [hbase] at hread_heap
                  | some baseVal =>
                    simp only [hbase] at hlive hread_heap
                    rw [← hsuffix, readPath_append] at hlive
                    simp only [hread_heap, Option.bind] at hlive
                    exact hlive
                simp [readPath] at hleaf_suffix)
        · rwa [heap_writeRef_preserves_readRef_diff_loc m.heap loc loc' path path' (.vec T elems.dropLast) heap'
                 hloc hwrite]
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
              exact heap_writeRef_preserves_readRef_same_loc m.heap loc path path2
                (.vec T elems.dropLast) heap' hwrite hne (by
                  intro suffix hsuffix
                  cases suffix with
                  | nil => simp [readPath]
                  | cons sf srest =>
                    have hleaf_suffix : readPath (.vec T elems) (sf :: srest) ≠ none := by
                      simp only [Heap.readRef, bind, Option.bind] at hne hread_heap
                      cases hbase : m.heap.read loc with
                      | none => simp [hbase] at hread_heap
                      | some baseVal =>
                        simp only [hbase] at hne hread_heap
                        rw [← hsuffix, readPath_append] at hne
                        simp only [hread_heap, Option.bind] at hne
                        exact hne
                    simp [readPath] at hleaf_suffix)
            · rwa [heap_writeRef_preserves_readRef_diff_loc m.heap loc loc2 path path2
                     (.vec T elems.dropLast) heap' hloc2 hwrite]
      varEnv_refs_in_pathEnv :=
        varEnv_refs_in_pathEnv_delete_ref_node hwt r src (.tvec T) .siteBorrowMut hlookup_src
      siteEnv_refs_in_pathEnv := by
        intro s' bt r' bk hl
        by_cases heqs : s' = s
        · subst heqs; rw [lookup_insert_same] at hl; simp at hl
        · rw [lookup_insert_ne _ s s' _ heqs] at hl
          exact siteEnv_refs_in_pathEnv_delete_ref_node hwt r src (.tvec T) .siteBorrowMut hlookup_src s' bt r' bk hl
      live_refs_unique := by
        intro r'
        refine ⟨fun x' bt bk ms' s' bt' bk' hvar' hs' => ?_,
                fun s1 s2 bt1 bt2 bk1 bk2 hne hs1 hs2 => ?_,
                fun x1 x2 bt1 bt2 bk1 bk2 ms1 ms2 hne hx1 hx2 =>
                  (hwt.live_refs_unique r').2.2 x1 x2 bt1 bt2 bk1 bk2 ms1 ms2 hne hx1 hx2⟩
        · by_cases heqs : s' = s
          · subst heqs; rw [lookup_insert_same] at hs'; simp at hs'
          · rw [lookup_insert_ne _ s s' _ heqs] at hs'
            exact (live_refs_unique_delete_site hwt src r').1 x' bt bk ms' s' bt' bk' hvar' hs'
        · by_cases heq1 : s1 = s
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
      heap_loc_bound := heap_loc_bound_after_writeRef m.heap loc path (.vec T elems.dropLast) heap'
        hwt.heap_loc_bound hwrite
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
                      (∃ s' bk, lookup env.siteEnv s' = some (.ref bt r' bk)) := by
          rcases hcond with ⟨x, bk, ms, hvar⟩ | ⟨s', bk, hsite⟩
          · exact Or.inl ⟨x, bk, ms, hvar⟩
          · by_cases heqs : s' = s
            · subst heqs; rw [lookup_insert_same] at hsite; simp at hsite
            · rw [lookup_insert_ne _ s s' _ heqs] at hsite
              have hne_src : s' ≠ src := by
                intro h; subst h; rw [lookup_delete_same] at hsite; simp at hsite
              rw [lookup_delete_ne _ src s' hne_src] at hsite
              exact Or.inr ⟨s', bk, hsite⟩
        obtain ⟨v_old, hread_old, hht_old⟩ := hwt.rmap_has_type r' bt loc' path' hrmap' hcond'
        by_cases hloc' : loc = loc'
        · subst hloc'
          simp only [Heap.readRef, bind, Option.bind] at hread_old hread_heap
          have hwr' := hwrite
          simp only [Heap.writeRef, bind, Option.bind] at hwr'
          cases hbase : m.heap.read loc with
          | none => simp [hbase] at hread_heap
          | some baseVal =>
            simp only [hbase] at hread_old hread_heap hwr'
            cases hwp2 : writePath baseVal path (.vec T elems.dropLast) with
            | none => simp [hwp2] at hwr'
            | some newRoot =>
              simp [hwp2] at hwr'
              obtain ⟨vnew, hread_vnew, hht_vnew⟩ := writePath_preserves_readPath_HasType
                baseVal path path' (.vec T elems.dropLast) newRoot (.vec T elems) v_old T.tvec bt
                hwp2 hread_old hht_old hread_heap hht_heap hht_remaining
                (fun suffix hne => by cases suffix with | nil => exact absurd rfl hne | cons => rfl)
              refine ⟨vnew, ?_, hht_vnew⟩
              rw [← hwr']
              simp only [Heap.readRef, bind, Option.bind, Heap.write, Heap.read,
                          lookup_insert_same, hread_vnew]
        · have hread' : heap'.readRef loc' path' = some v_old := by
            rw [heap_writeRef_preserves_readRef_diff_loc m.heap loc loc' path path'
              (.vec T elems.dropLast) heap' hloc' hwrite]
            exact hread_old
          exact ⟨v_old, hread', hht_old⟩
      funEnv_sig_consistent := hwt.funEnv_sig_consistent
      refs_tracked_mapped := by
        intro ref href
        simp only [delete_ref_node_refs, List.mem_filter, decide_eq_true_eq] at href
        exact hwt.refs_tracked_mapped ref href.1
      lenv_labels_in_blocks := hwt.lenv_labels_in_blocks
      has_return_info := hwt.has_return_info
      varStore_locs_bound := by
        intro y loc_y hvar
        rw [writeRef_preserves_nextLoc m.heap loc path (.vec T elems.dropLast) heap' hwrite]
        exact hwt.varStore_locs_bound y loc_y hvar
    }

private theorem preservation_vecPushBack (m m' : Machine) (env : TypeEnv) (lenv : LabelEnv)
    (retTypes : List ParamType) (rmap : RefMap)
    (hwt : WellTypedState m env lenv retTypes rmap)
    (hss : StackSafe env.enumEnv m.stack m.frame.returnInfo m.heap retTypes)
    (refSite val : Site) (cont : Stmt)
    (hstmt : m.frame.stmt = .vecPushBack refSite val cont)
    (hstep : step (.running m) = .running m') :
    ∃ env' lenv' retTypes' rmap',
      env'.enumEnv = env.enumEnv ∧ WellTypedState m' env' lenv' retTypes' rmap' ∧
      StackSafe env.enumEnv m'.stack m'.frame.returnInfo m'.heap retTypes' := by
  obtain ⟨T, r, hlookup_ref, hlookup_val, houtbound, hcont⟩ :=
    inv_vecPushBack (by rw [← hstmt]; exact hwt.stmt_typed)
  -- Get ref value
  obtain ⟨vref, hvref, hmatch_ref⟩ := hwt.site_consistent refSite _ hlookup_ref
  simp only [ValueMatchesType] at hmatch_ref
  obtain ⟨loc, path, hveq, hrmap⟩ := hmatch_ref
  subst hveq
  -- Get val value
  obtain ⟨vval, hvval, hmatch_val⟩ := hwt.site_consistent val _ hlookup_val
  -- r not root
  have hr_not_root : r ≠ .root := hwt.env_wf.siteEnv_wf refSite _ hlookup_ref
  -- Get vector from heap
  obtain ⟨heap_val, hread_heap, hht_heap⟩ := hwt.rmap_has_type r (.tvec T) loc path hrmap
    (Or.inr ⟨refSite, .siteBorrowMut, hlookup_ref⟩)
  obtain ⟨elems, rfl⟩ := HasType.vec_elems hht_heap
  -- writeRef must succeed
  have hread_ne_none : m.heap.readRef loc path ≠ none := by rw [hread_heap]; exact Option.some_ne_none _
  obtain ⟨heap', hwrite⟩ :=
    readRef_ne_none_implies_writeRef_ne_none m.heap loc path (.vec T (elems ++ [vval])) hread_ne_none
  -- Simplify step
  have hrs_ref : readSite m refSite = some (.ref loc path) := by unfold readSite; exact hvref
  have hrs_val : readSite m val = some vval := by unfold readSite; exact hvval
  simp only [step, hstmt, hrs_ref, hrs_val, hread_heap] at hstep
  simp only [hwrite, ExecState.running.injEq] at hstep
  subst hstep
  -- garbage_collect = delete_ref_node
  rw [garbage_collect_eq_delete_ref_node] at hcont
  -- HasType for new vector
  have hmval : HasType env.enumEnv vval T := hmatch_val
  have hht_appended : HasType env.enumEnv (.vec T (elems ++ [vval])) (.tvec T) :=
    HasType.vec (elems ++ [vval]) T (fun v hv => by
      rw [List.mem_append, List.mem_singleton] at hv
      rcases hv with hv_old | rfl
      · cases hht_heap with | vec _ _ h => exact h v hv_old
      · exact hmval)
  have hcheck_empty := check_outbound_only_empty env.pathEnv r houtbound
  -- New env
  refine ⟨{env with siteEnv := delete (delete env.siteEnv val) refSite,
                     pathEnv := delete_ref_node env.pathEnv r},
          lenv, retTypes, rmap, rfl, ?_,
          stackSafe_heap_writeRef env.enumEnv m.stack m.frame.returnInfo m.heap heap' loc path
            (.vec T (elems ++ [vval])) (.vec T elems) (.tvec T) hss hwrite hread_heap
            hht_heap hht_appended
            (fun suffix hne_s hread => by cases suffix with | nil => exact absurd rfl hne_s | cons f rest => simp [readPath] at hread)
            (fun suffix hne_s => by cases suffix with | nil => exact absurd rfl hne_s | cons f rest => simp [typeAtPathV])⟩
  -- Helper: get original siteEnv from double-deleted
  have get_old_site : ∀ s' τ', lookup (delete (delete env.siteEnv val) refSite) s' = some τ' →
      lookup env.siteEnv s' = some τ' := by
    intro s' τ' hl
    have hne_ref : s' ≠ refSite := by intro h; subst h; rw [lookup_delete_same] at hl; cases hl
    have hne_val : s' ≠ val := by
      intro h; subst h; rw [lookup_delete_ne _ refSite s' hne_ref, lookup_delete_same] at hl; cases hl
    rw [lookup_delete_ne _ refSite s' hne_ref, lookup_delete_ne _ val s' hne_val] at hl; exact hl
  -- Helper: heap read at different loc
  have hread_diff : ∀ loc', loc' ≠ loc → heap'.read loc' = m.heap.read loc' := by
    intro loc' hne
    simp only [Heap.writeRef, bind, Option.bind] at hwrite
    cases hbase : m.heap.read loc with
    | none => simp [hbase] at hwrite
    | some baseVal =>
      simp [hbase] at hwrite
      cases hwp : writePath baseVal path (.vec T (elems ++ [vval])) with
      | none => simp [hwp] at hwrite
      | some newVal =>
        simp [hwp] at hwrite; rw [← hwrite]
        exact heap_write_preserves_read m.heap loc loc' newVal (Ne.symm hne)
  exact {
    env_wf := ⟨delete_ref_node_wellformed env.pathEnv r hwt.env_wf.pathEnv_wf hr_not_root,
               SiteEnv.delete_refs_not_root _ _
                 (SiteEnv.delete_refs_not_root _ _ hwt.env_wf.siteEnv_wf),
               hwt.env_wf.varEnv_wf⟩
    enumEnv_consistent := hwt.enumEnv_consistent
    enum_qualified_nodup := hwt.enum_qualified_nodup
    enum_names_nodup := hwt.enum_names_nodup
    enum_variant_nodup := hwt.enum_variant_nodup
    enum_fields_nodup := hwt.enum_fields_nodup
    defaultValues_typed := hwt.defaultValues_typed
    stmt_typed := hcont
    var_consistent := by
      intro x isv τ ms hvar
      have hvc := hwt.var_consistent x isv τ ms hvar
      cases isv with
      | validVar =>
        dsimp only at hvc ⊢
        obtain ⟨loc_x, v_x, hvarStore, hread_x, hmatch_x⟩ := hvc
        by_cases hloc : loc_x = loc
        · subst hloc
          have ⟨newRootVal, hwp, hread_new⟩ :
              ∃ nv, writePath v_x path (.vec T (elems ++ [vval])) = some nv ∧ heap'.read loc_x = some nv := by
            simp only [Heap.writeRef, bind, Option.bind, hread_x] at hwrite
            cases hwp' : writePath v_x path (.vec T (elems ++ [vval])) with
            | none => simp [hwp'] at hwrite
            | some nv =>
              simp [hwp'] at hwrite
              exact ⟨nv, rfl, by rw [← hwrite]; simp [Heap.write, Heap.read, lookup_insert_same]⟩
          refine ⟨loc_x, newRootVal, hvarStore, hread_new, ?_⟩
          cases τ with
          | basic bt_x =>
            dsimp only [ValueMatchesType] at hmatch_x ⊢
            exact writePath_preserves_HasType_generalV v_x path (.vec T (elems ++ [vval])) newRootVal bt_x
              hmatch_x hwp (by
                intro bt_leaf htapV
                have hread_leaf : readPath v_x path = some (.vec T elems) := by
                  simp only [Heap.readRef, bind, Option.bind, hread_x] at hread_heap; exact hread_heap
                obtain ⟨u, hread_u, hht_u⟩ := HasType_typeAtPathV v_x bt_x path bt_leaf hmatch_x htapV
                rw [hread_leaf] at hread_u
                simp only [Option.some.injEq] at hread_u; subst hread_u
                exact HasType_transfer hht_u hht_heap hht_appended)
          | ref bt_ref r_ref bk_ref =>
            exfalso
            dsimp only [ValueMatchesType] at hmatch_x
            obtain ⟨loc', path', hveq, _⟩ := hmatch_x
            rw [hveq] at hwp hread_x
            cases path with
            | cons f rest => simp [writePath] at hwp
            | nil =>
              simp only [Heap.readRef, bind, Option.bind, hread_x, readPath,
                          Option.some.injEq] at hread_heap
              rw [← hread_heap] at hht_heap
              exact HasType_not_ref loc' path' T.tvec hht_heap
        · exact ⟨loc_x, v_x, hvarStore, (hread_diff loc_x hloc).trans hread_x, hmatch_x⟩
      | invalidVar =>
        dsimp only at hvc ⊢
        rcases hvc with hvc_none | ⟨loc_x, hvc_some⟩
        · exact Or.inl hvc_none
        · exact Or.inr ⟨loc_x, hvc_some⟩
    site_consistent := by
      intro s' τ' hl
      exact hwt.site_consistent s' τ' (get_old_site s' τ' hl)
    rmap_live := by
      intro r' loc' path' hr'_tracked hrmap'
      have hr'_old : r' ∈ env.pathEnv.refs := by
        have hr'' : r' ∈ (delete_ref_node env.pathEnv r).refs := hr'_tracked
        simp only [delete_ref_node_refs, List.mem_filter, decide_eq_true_eq] at hr''; exact hr''.1
      have hlive := hwt.rmap_live r' loc' path' hr'_old hrmap'
      by_cases hloc : loc = loc'
      · subst hloc
        exact heap_writeRef_preserves_readRef_same_loc m.heap loc path path'
          (.vec T (elems ++ [vval])) heap' hwrite hlive (by
            intro suffix hsuffix
            cases suffix with
            | nil => simp [readPath]
            | cons sf srest =>
              have hleaf_suffix : readPath (.vec T elems) (sf :: srest) ≠ none := by
                simp only [Heap.readRef, bind, Option.bind] at hlive hread_heap
                cases hbase : m.heap.read loc with
                | none => simp [hbase] at hread_heap
                | some baseVal =>
                  simp only [hbase] at hlive hread_heap
                  rw [← hsuffix, readPath_append] at hlive
                  simp only [hread_heap, Option.bind] at hlive; exact hlive
              simp [readPath] at hleaf_suffix)
      · rwa [heap_writeRef_preserves_readRef_diff_loc m.heap loc loc' path path'
               (.vec T (elems ++ [vval])) heap' hloc hwrite]
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
            exact heap_writeRef_preserves_readRef_same_loc m.heap loc path path2
              (.vec T (elems ++ [vval])) heap' hwrite hne (by
                intro suffix hsuffix
                cases suffix with
                | nil => simp [readPath]
                | cons sf srest =>
                  have hleaf_suffix : readPath (.vec T elems) (sf :: srest) ≠ none := by
                    simp only [Heap.readRef, bind, Option.bind] at hne hread_heap
                    cases hbase : m.heap.read loc with
                    | none => simp [hbase] at hread_heap
                    | some baseVal =>
                      simp only [hbase] at hne hread_heap
                      rw [← hsuffix, readPath_append] at hne
                      simp only [hread_heap, Option.bind] at hne; exact hne
                  simp [readPath] at hleaf_suffix)
          · rwa [heap_writeRef_preserves_readRef_diff_loc m.heap loc loc2 path path2
                   (.vec T (elems ++ [vval])) heap' hloc2 hwrite]
    varEnv_refs_in_pathEnv :=
      varEnv_refs_in_pathEnv_delete_ref_node hwt r refSite (.tvec T) .siteBorrowMut hlookup_ref
    siteEnv_refs_in_pathEnv := by
      intro s' bt r' bk hl
      have hl_orig := get_old_site s' (.ref bt r' bk) hl
      have hr'_in := hwt.siteEnv_refs_in_pathEnv s' bt r' bk hl_orig
      have hne_ref : s' ≠ refSite := by intro h; subst h; rw [lookup_delete_same] at hl; cases hl
      have hr'_ne : r' ≠ r := by
        intro heq; rw [heq] at hl_orig
        exact (hwt.live_refs_unique r).2.1 s' refSite bt (.tvec T) bk .siteBorrowMut
          hne_ref hl_orig hlookup_ref
      simp only [delete_ref_node_refs, List.mem_filter, decide_eq_true_eq]
      exact ⟨hr'_in, hr'_ne⟩
    live_refs_unique := by
      intro r'
      refine ⟨fun x bt bk ms s' bt' bk' hv hs =>
                (hwt.live_refs_unique r').1 x bt bk ms s' bt' bk' hv (get_old_site s' _ hs),
              fun s1 s2 bt1 bt2 bk1 bk2 hne hs1 hs2 =>
                (hwt.live_refs_unique r').2.1 s1 s2 bt1 bt2 bk1 bk2 hne
                  (get_old_site s1 _ hs1) (get_old_site s2 _ hs2),
              fun x y bt1 bt2 bk1 bk2 ms1 ms2 hne hx hy =>
                (hwt.live_refs_unique r').2.2 x y bt1 bt2 bk1 bk2 ms1 ms2 hne hx hy⟩
    blocks_typed := hwt.blocks_typed
    lenv_empty_siteEnv := hwt.lenv_empty_siteEnv
    lenv_wf := hwt.lenv_wf
    lenv_var_tracked := hwt.lenv_var_tracked
    lenv_var_unique := hwt.lenv_var_unique
    lenv_funEnv_eq := hwt.lenv_funEnv_eq
    funEnv_typed := hwt.funEnv_typed
    heap_loc_bound := heap_loc_bound_after_writeRef m.heap loc path (.vec T (elems ++ [vval])) heap'
      hwt.heap_loc_bound hwrite
    rmap_root_none := hwt.rmap_root_none
    no_paths_to_root := no_paths_to_root_delete_ref_node' hwt r hr_not_root
    root_path_coherence := root_path_coherence_delete_ref_node' hwt r hr_not_root
    paths_from_non_member_empty := delete_ref_node_paths_from_non_member env.pathEnv r
      hwt.paths_from_non_member_empty
    paths_to_non_member_empty := delete_ref_node_paths_to_non_member env.pathEnv r
      hwt.paths_to_non_member_empty
    self_loop_only_empty := by
      intro u p hp
      simp only [delete_ref_node] at hp
      by_cases hu : u = r
      · subst hu; rw [if_pos ⟨rfl, rfl⟩] at hp; exact hp
      · simp only [hu, false_or, ↓reduceIte] at hp; exact hwt.self_loop_only_empty u p hp
    rmap_has_type := by
      intro r' bt loc' path' hrmap' hcond
      have hcond' : (∃ x bk ms, lookup env.varEnv x = some (.validVar, .ref bt r' bk, ms)) ∨
                    (∃ s' bk, lookup env.siteEnv s' = some (.ref bt r' bk)) := by
        rcases hcond with ⟨x, bk, ms, hvar⟩ | ⟨s', bk, hsite⟩
        · exact Or.inl ⟨x, bk, ms, hvar⟩
        · exact Or.inr ⟨s', bk, get_old_site s' _ hsite⟩
      obtain ⟨v_old, hread_old, hht_old⟩ := hwt.rmap_has_type r' bt loc' path' hrmap' hcond'
      by_cases hloc' : loc = loc'
      · subst hloc'
        simp only [Heap.readRef, bind, Option.bind] at hread_old hread_heap
        have hwr' := hwrite
        simp only [Heap.writeRef, bind, Option.bind] at hwr'
        cases hbase : m.heap.read loc with
        | none => simp [hbase] at hread_heap
        | some baseVal =>
          simp only [hbase] at hread_old hread_heap hwr'
          cases hwp2 : writePath baseVal path (.vec T (elems ++ [vval])) with
          | none => simp [hwp2] at hwr'
          | some newRoot =>
            simp [hwp2] at hwr'
            obtain ⟨vnew, hread_vnew, hht_vnew⟩ := writePath_preserves_readPath_HasType
              baseVal path path' (.vec T (elems ++ [vval])) newRoot (.vec T elems) v_old T.tvec bt
              hwp2 hread_old hht_old hread_heap hht_heap hht_appended
                (fun suffix hne => by cases suffix with | nil => exact absurd rfl hne | cons => rfl)
            refine ⟨vnew, ?_, hht_vnew⟩
            rw [← hwr']
            simp only [Heap.readRef, bind, Option.bind, Heap.write, Heap.read,
                        lookup_insert_same, hread_vnew]
      · have hread' : heap'.readRef loc' path' = some v_old := by
          rw [heap_writeRef_preserves_readRef_diff_loc m.heap loc loc' path path'
            (.vec T (elems ++ [vval])) heap' hloc' hwrite]
          exact hread_old
        exact ⟨v_old, hread', hht_old⟩
    funEnv_sig_consistent := hwt.funEnv_sig_consistent
    refs_tracked_mapped := by
      intro ref href
      simp only [delete_ref_node_refs, List.mem_filter, decide_eq_true_eq] at href
      exact hwt.refs_tracked_mapped ref href.1
    lenv_labels_in_blocks := hwt.lenv_labels_in_blocks
    has_return_info := hwt.has_return_info
    varStore_locs_bound := by
      intro y loc_y hvar
      rw [writeRef_preserves_nextLoc m.heap loc path (.vec T (elems ++ [vval])) heap' hwrite]
      exact hwt.varStore_locs_bound y loc_y hvar
  }

private theorem preservation_vecSwap (m m' : Machine) (env : TypeEnv) (lenv : LabelEnv)
    (retTypes : List ParamType) (rmap : RefMap)
    (hwt : WellTypedState m env lenv retTypes rmap)
    (hss : StackSafe env.enumEnv m.stack m.frame.returnInfo m.heap retTypes)
    (refSite idx1Site idx2Site : Site) (cont : Stmt)
    (hstmt : m.frame.stmt = .vecSwap refSite idx1Site idx2Site cont)
    (hstep : step (.running m) = .running m') :
    ∃ env' lenv' retTypes' rmap',
      env'.enumEnv = env.enumEnv ∧ WellTypedState m' env' lenv' retTypes' rmap' ∧
      StackSafe env.enumEnv m'.stack m'.frame.returnInfo m'.heap retTypes' := by
  -- 1. Invert typing
  obtain ⟨T, r, hlookup_ref, hlookup_idx1, hlookup_idx2, houtbound, hcont⟩ :=
    inv_vecSwap (by rw [← hstmt]; exact hwt.stmt_typed)
  -- 2. Get concrete values from site_consistent
  obtain ⟨vref, hvref, hmatch_ref⟩ := hwt.site_consistent refSite _ hlookup_ref
  simp only [ValueMatchesType] at hmatch_ref
  obtain ⟨loc, path, hveq, hrmap⟩ := hmatch_ref
  subst hveq
  obtain ⟨vidx1, hvidx1, hmatch_idx1⟩ := hwt.site_consistent idx1Site _ hlookup_idx1
  obtain ⟨vidx2, hvidx2, hmatch_idx2⟩ := hwt.site_consistent idx2Site _ hlookup_idx2
  -- 3. r not root
  have hr_not_root : r ≠ .root := hwt.env_wf.siteEnv_wf refSite _ hlookup_ref
  -- 4. Get vector from heap via rmap_has_type
  obtain ⟨heap_val, hread_heap, hht_heap⟩ := hwt.rmap_has_type r (.tvec T) loc path hrmap
    (Or.inr ⟨refSite, .siteBorrowMut, hlookup_ref⟩)
  obtain ⟨elems, rfl⟩ := HasType.vec_elems hht_heap
  -- hread_heap : m.heap.readRef loc path = some (.vec T elems)
  -- hht_heap : HasType (.vec T elems) (.tvec T)
  -- 5. Get int values for indices
  simp only [ValueMatchesType] at hmatch_idx1 hmatch_idx2
  obtain ⟨i, rfl⟩ : ∃ i, vidx1 = .int i := by cases hmatch_idx1 with | int n => exact ⟨n, rfl⟩
  obtain ⟨j, rfl⟩ : ∃ j, vidx2 = .int j := by cases hmatch_idx2 with | int n => exact ⟨n, rfl⟩
  -- 6. Simplify step
  have hrs_ref : readSite m refSite = some (.ref loc path) := by unfold readSite; exact hvref
  have hrs_idx1 : readSite m idx1Site = some (.int i) := by unfold readSite; exact hvidx1
  have hrs_idx2 : readSite m idx2Site = some (.int j) := by unfold readSite; exact hvidx2
  simp only [step, hstmt, hrs_ref, hrs_idx1, hrs_idx2, hread_heap] at hstep
  -- 7. Handle index bounds checks
  split at hstep
  · -- i < elems.length
    split at hstep
    · -- j < elems.length
      rename_i hi hj
      -- The new value to write
      let newVec := Value.vec T ((elems.set i (elems[j])).set j (elems[i]))
      -- writeRef must succeed (readRef succeeded, so writeRef does too)
      have hread_ne_none : m.heap.readRef loc path ≠ none := by
        rw [hread_heap]; exact Option.some_ne_none _
      obtain ⟨heap', hwrite⟩ :=
        readRef_ne_none_implies_writeRef_ne_none m.heap loc path newVec hread_ne_none
      simp only [newVec, hwrite, ExecState.running.injEq] at hstep
      subst hstep
      -- garbage_collect = delete_ref_node
      rw [garbage_collect_eq_delete_ref_node] at hcont
      -- Key facts
      have hcheck_empty := check_outbound_only_empty env.pathEnv r houtbound
      -- The old value at loc/path (v_leaf) has HasType (.tvec T)
      -- Here v_leaf = .vec T elems, so hv_leaf_read = hread_heap, hv_leaf_ht = hht_heap
      -- The new value also has HasType (.tvec T)
      have hmval : HasType env.enumEnv newVec (.tvec T) := by
        apply HasType.vec
        intro v hv_mem
        -- v is a member of (elems.set i (elems[j])).set j (elems[i])
        -- Every element is either from the original list or is elems[i] or elems[j]
        have helem_typed : ∀ w, w ∈ elems → HasType env.enumEnv w T := by
          cases hht_heap with | vec _ _ h => exact h
        -- Use getElem-based reasoning: every element at index k of the result list
        -- is either elems[i], elems[j], or elems[k] for some k
        rw [List.mem_iff_getElem] at hv_mem
        obtain ⟨k, hk, rfl⟩ := hv_mem
        simp only [List.length_set] at hk
        simp only [List.getElem_set]
        split
        · -- k = j: we get elems[i]
          exact helem_typed _ (List.getElem_mem hi)
        · -- k ≠ j: we get (elems.set i elems[j])[k]
          split
          · -- k = i: we get elems[j]
            exact helem_typed _ (List.getElem_mem hj)
          · -- k ≠ i: we get elems[k]
            exact helem_typed _ (List.getElem_mem hk)
      -- Helper: heap'.read at different locations is unchanged
      have hread_diff : ∀ loc', loc' ≠ loc → heap'.read loc' = m.heap.read loc' := by
        intro loc' hne
        simp only [Heap.writeRef, bind, Option.bind] at hwrite
        cases hbase : m.heap.read loc with
        | none => simp [hbase] at hwrite
        | some baseVal =>
          simp [hbase] at hwrite
          cases hwp : writePath baseVal path newVec with
          | none => simp [hwp] at hwrite
          | some newVal =>
            simp [hwp] at hwrite; rw [← hwrite]
            exact heap_write_preserves_read m.heap loc loc' newVal (Ne.symm hne)
      -- 8. Construct WellTypedState for m'
      refine ⟨{env with siteEnv := delete (delete (delete env.siteEnv idx2Site) idx1Site) refSite,
                         pathEnv := delete_ref_node env.pathEnv r},
              lenv, retTypes, rmap, rfl, ?_,
              stackSafe_heap_writeRef env.enumEnv m.stack m.frame.returnInfo m.heap heap' loc path
                newVec (.vec T elems) (.tvec T) hss hwrite hread_heap
                hht_heap hmval
                (fun suffix hne_s hread => by cases suffix with | nil => exact absurd rfl hne_s | cons f rest => simp [readPath] at hread)
                (fun suffix hne_s => by cases suffix with | nil => exact absurd rfl hne_s | cons f rest => simp [typeAtPathV])⟩
      exact {
        env_wf := ⟨delete_ref_node_wellformed env.pathEnv r hwt.env_wf.pathEnv_wf hr_not_root,
                   SiteEnv.delete_refs_not_root _ _
                     (SiteEnv.delete_refs_not_root _ _
                       (SiteEnv.delete_refs_not_root _ _ hwt.env_wf.siteEnv_wf)),
                   hwt.env_wf.varEnv_wf⟩
        enumEnv_consistent := hwt.enumEnv_consistent
        enum_qualified_nodup := hwt.enum_qualified_nodup
        enum_names_nodup := hwt.enum_names_nodup
        enum_variant_nodup := hwt.enum_variant_nodup
        enum_fields_nodup := hwt.enum_fields_nodup
        defaultValues_typed := hwt.defaultValues_typed
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
              subst hloc
              -- Extract writePath and new root value from writeRef
              have ⟨newRootVal, hwp, hread_new⟩ :
                  ∃ nv, writePath v_x path newVec = some nv ∧ heap'.read loc = some nv := by
                simp only [Heap.writeRef, bind, Option.bind, hread_x] at hwrite
                cases hwp' : writePath v_x path newVec with
                | none => simp [hwp'] at hwrite
                | some nv =>
                  simp [hwp'] at hwrite
                  exact ⟨nv, rfl, by rw [← hwrite]; simp [Heap.write, Heap.read, lookup_insert_same]⟩
              refine ⟨loc, newRootVal, hvarStore, hread_new, ?_⟩
              -- ValueMatchesType newRootVal τ_x rmap
              cases τ_x with
              | basic bt_x =>
                dsimp only [ValueMatchesType] at hmatch_x ⊢
                exact writePath_preserves_HasType_generalV v_x path newVec newRootVal bt_x
                  hmatch_x hwp (by
                    intro bt_leaf htapV
                    have hread_leaf : readPath v_x path = some (.vec T elems) := by
                      simp only [Heap.readRef, bind, Option.bind, hread_x] at hread_heap
                      exact hread_heap
                    obtain ⟨u, hread_u, hht_u⟩ :=
                      HasType_typeAtPathV v_x bt_x path bt_leaf hmatch_x htapV
                    rw [hread_leaf] at hread_u
                    simp only [Option.some.injEq] at hread_u; subst hread_u
                    exact HasType_transfer hht_u hht_heap hmval)
              | ref bt_ref r_ref bk_ref =>
                -- Variable x has ref type at same location as write target — impossible
                exfalso
                dsimp only [ValueMatchesType] at hmatch_x
                obtain ⟨loc', path', hveq, _⟩ := hmatch_x
                rw [hveq] at hwp hread_x
                cases path with
                | cons f rest => simp [writePath] at hwp
                | nil =>
                  simp only [Heap.readRef, bind, Option.bind, hread_x, readPath,
                              Option.some.injEq] at hread_heap
                  rw [← hread_heap] at hht_heap
                  exact HasType_not_ref loc' path' (.tvec T) hht_heap
            · -- Different location: heap value unchanged
              exact ⟨loc_x, v_x, hvarStore, (hread_diff loc_x (Ne.symm hloc)).trans hread_x, hmatch_x⟩
          | invalidVar =>
            dsimp only at hvc ⊢
            rcases hvc with hvc_none | ⟨loc_x, hvc_some⟩
            · exact Or.inl hvc_none
            · exact Or.inr ⟨loc_x, hvc_some⟩
        site_consistent := by
          intro s' τ' hl
          -- All three sites are deleted; peel off to get original siteEnv lookup
          have hne_ref : s' ≠ refSite := by
            intro h; subst h; rw [lookup_delete_same] at hl; simp at hl
          rw [lookup_delete_ne _ refSite s' hne_ref] at hl
          have hne_idx1 : s' ≠ idx1Site := by
            intro h; subst h; rw [lookup_delete_same] at hl; simp at hl
          rw [lookup_delete_ne _ idx1Site s' hne_idx1] at hl
          have hne_idx2 : s' ≠ idx2Site := by
            intro h; subst h; rw [lookup_delete_same] at hl; simp at hl
          rw [lookup_delete_ne _ idx2Site s' hne_idx2] at hl
          exact hwt.site_consistent s' τ' hl
        rmap_live := by
          intro r' loc' path' hr'_tracked hrmap'
          have hr'_old : r' ∈ env.pathEnv.refs := by
            have hr'' : r' ∈ (delete_ref_node env.pathEnv r).refs := hr'_tracked
            simp only [delete_ref_node_refs, List.mem_filter, decide_eq_true_eq] at hr''; exact hr''.1
          have hlive := hwt.rmap_live r' loc' path' hr'_old hrmap'
          by_cases hloc : loc = loc'
          · subst hloc
            exact heap_writeRef_preserves_readRef_same_loc m.heap loc path path' newVec heap'
              hwrite hlive (by
                intro suffix hsuffix
                cases suffix with
                | nil => simp [readPath]
                | cons sf srest =>
                  -- Derive readPath (.vec T elems) (sf :: srest) ≠ none from old heap
                  have hleaf_suffix : readPath (.vec T elems) (sf :: srest) ≠ none := by
                    simp only [Heap.readRef, bind, Option.bind] at hlive hread_heap
                    cases hbase : m.heap.read loc with
                    | none => simp [hbase] at hread_heap
                    | some baseVal =>
                      simp only [hbase] at hlive hread_heap
                      rw [← hsuffix, readPath_append] at hlive
                      simp only [hread_heap, Option.bind] at hlive
                      exact hlive
                  -- readPath on vec with non-empty path is always none
                  simp [readPath] at hleaf_suffix)
          · rwa [heap_writeRef_preserves_readRef_diff_loc m.heap loc loc' path path' newVec heap'
                   hloc hwrite]
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
                exact heap_writeRef_preserves_readRef_same_loc m.heap loc path path2 newVec heap'
                  hwrite hne (by
                    intro suffix hsuffix
                    cases suffix with
                    | nil => simp [readPath]
                    | cons sf srest =>
                      have hleaf_suffix : readPath (.vec T elems) (sf :: srest) ≠ none := by
                        simp only [Heap.readRef, bind, Option.bind] at hne hread_heap
                        cases hbase : m.heap.read loc with
                        | none => simp [hbase] at hread_heap
                        | some baseVal =>
                          simp only [hbase] at hne hread_heap
                          rw [← hsuffix, readPath_append] at hne
                          simp only [hread_heap, Option.bind] at hne
                          exact hne
                      simp [readPath] at hleaf_suffix)
              · rwa [heap_writeRef_preserves_readRef_diff_loc m.heap loc loc2 path path2 newVec heap'
                       hloc2 hwrite]
        varEnv_refs_in_pathEnv :=
          varEnv_refs_in_pathEnv_delete_ref_node hwt r refSite (.tvec T) .siteBorrowMut hlookup_ref
        siteEnv_refs_in_pathEnv := by
          intro s' bt r' bk hl
          -- Peel off the 3 deletes to reach the original siteEnv
          have hne_ref : s' ≠ refSite := by
            intro h; subst h; rw [lookup_delete_same] at hl; simp at hl
          rw [lookup_delete_ne _ refSite s' hne_ref] at hl
          have hne_idx1 : s' ≠ idx1Site := by
            intro h; subst h; rw [lookup_delete_same] at hl; simp at hl
          rw [lookup_delete_ne _ idx1Site s' hne_idx1] at hl
          have hne_idx2 : s' ≠ idx2Site := by
            intro h; subst h; rw [lookup_delete_same] at hl; simp at hl
          rw [lookup_delete_ne _ idx2Site s' hne_idx2] at hl
          have hr'_in := hwt.siteEnv_refs_in_pathEnv s' bt r' bk hl
          have hr'_ne : r' ≠ r := by
            intro heq; rw [heq] at hl
            exact (hwt.live_refs_unique r).2.1 s' refSite bt (.tvec T) bk .siteBorrowMut
              hne_ref hl hlookup_ref
          simp only [delete_ref_node_refs, List.mem_filter, decide_eq_true_eq]
          exact ⟨hr'_in, hr'_ne⟩
        live_refs_unique := by
          intro r'
          -- Helper to peel off 3 deletes
          have get_old : ∀ s bt' bk',
              lookup (delete (delete (delete env.siteEnv idx2Site) idx1Site) refSite) s
              = some (.ref bt' r' bk') → lookup env.siteEnv s = some (.ref bt' r' bk') := by
            intro s bt' bk' hs
            have hne_ref : s ≠ refSite := by
              intro h; subst h; simp [lookup_delete_same] at hs
            have hne_idx1 : s ≠ idx1Site := by
              intro h; subst h
              rw [lookup_delete_ne _ refSite s hne_ref, lookup_delete_same] at hs; cases hs
            have hne_idx2 : s ≠ idx2Site := by
              intro h; subst h
              rw [lookup_delete_ne _ refSite s hne_ref,
                  lookup_delete_ne _ idx1Site s hne_idx1, lookup_delete_same] at hs; cases hs
            rw [lookup_delete_ne _ refSite s hne_ref,
                lookup_delete_ne _ idx1Site s hne_idx1,
                lookup_delete_ne _ idx2Site s hne_idx2] at hs; exact hs
          refine ⟨fun x bt bk ms s' bt' bk' hv hs =>
                    (hwt.live_refs_unique r').1 x bt bk ms s' bt' bk' hv (get_old s' bt' bk' hs),
                  fun s1 s2 bt1 bt2 bk1 bk2 hne hs1 hs2 =>
                    (hwt.live_refs_unique r').2.1 s1 s2 bt1 bt2 bk1 bk2 hne
                      (get_old s1 bt1 bk1 hs1) (get_old s2 bt2 bk2 hs2),
                  fun x y bt1 bt2 bk1 bk2 ms1 ms2 hne hx hy =>
                    (hwt.live_refs_unique r').2.2 x y bt1 bt2 bk1 bk2 ms1 ms2 hne hx hy⟩
        blocks_typed := hwt.blocks_typed
        lenv_empty_siteEnv := hwt.lenv_empty_siteEnv
        lenv_wf := hwt.lenv_wf
        lenv_var_tracked := hwt.lenv_var_tracked
        lenv_var_unique := hwt.lenv_var_unique
        lenv_funEnv_eq := hwt.lenv_funEnv_eq
        funEnv_typed := hwt.funEnv_typed
        heap_loc_bound :=
          heap_loc_bound_after_writeRef m.heap loc path newVec heap' hwt.heap_loc_bound hwrite
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
          · simp only [hu, false_or, ↓reduceIte] at hp; exact hwt.self_loop_only_empty u p hp
        rmap_has_type := by
          intro r' bt loc' path' hrmap' hcond
          have hcond' : (∃ x bk ms, lookup env.varEnv x = some (.validVar, .ref bt r' bk, ms)) ∨
                        (∃ s bk, lookup env.siteEnv s = some (.ref bt r' bk)) := by
            rcases hcond with ⟨x, bk, ms, hvar⟩ | ⟨s', bk, hsite⟩
            · exact Or.inl ⟨x, bk, ms, hvar⟩
            · -- Peel off deletes
              have hne_ref : s' ≠ refSite := by
                intro h; subst h; rw [lookup_delete_same] at hsite; simp at hsite
              rw [lookup_delete_ne _ refSite s' hne_ref] at hsite
              have hne_idx1 : s' ≠ idx1Site := by
                intro h; subst h; rw [lookup_delete_same] at hsite; simp at hsite
              rw [lookup_delete_ne _ idx1Site s' hne_idx1] at hsite
              have hne_idx2 : s' ≠ idx2Site := by
                intro h; subst h; rw [lookup_delete_same] at hsite; simp at hsite
              rw [lookup_delete_ne _ idx2Site s' hne_idx2] at hsite
              exact Or.inr ⟨s', bk, hsite⟩
          obtain ⟨v_old, hread_old, hht_old⟩ := hwt.rmap_has_type r' bt loc' path' hrmap' hcond'
          by_cases hloc' : loc = loc'
          · subst hloc'
            -- Same location: use writePath_preserves_readPath_HasType
            simp only [Heap.readRef, bind, Option.bind] at hread_old hread_heap
            have hwrite' := hwrite
            simp only [Heap.writeRef, bind, Option.bind] at hwrite'
            cases hbase : m.heap.read loc with
            | none => simp [hbase] at hread_heap
            | some baseVal =>
              simp only [hbase] at hread_old hread_heap hwrite'
              cases hwp2 : writePath baseVal path newVec with
              | none => simp [hwp2] at hwrite'
              | some newRoot =>
                simp [hwp2] at hwrite'
                obtain ⟨vnew, hread_vnew, hht_vnew⟩ := writePath_preserves_readPath_HasType
                  baseVal path path' newVec newRoot (.vec T elems) v_old (.tvec T) bt
                  hwp2 hread_old hht_old hread_heap hht_heap hmval
                    (fun suffix hne => by cases suffix with | nil => exact absurd rfl hne | cons => rfl)
                refine ⟨vnew, ?_, hht_vnew⟩
                rw [← hwrite']
                simp only [Heap.readRef, bind, Option.bind, Heap.write, Heap.read,
                            lookup_insert_same, hread_vnew]
          · have hread' : heap'.readRef loc' path' = some v_old := by
              rw [heap_writeRef_preserves_readRef_diff_loc m.heap loc loc' path path' newVec heap'
                    hloc' hwrite]
              exact hread_old
            exact ⟨v_old, hread', hht_old⟩
        funEnv_sig_consistent := hwt.funEnv_sig_consistent
        refs_tracked_mapped := by
          intro ref href
          simp only [delete_ref_node_refs, List.mem_filter, decide_eq_true_eq] at href
          exact hwt.refs_tracked_mapped ref href.1
        lenv_labels_in_blocks := hwt.lenv_labels_in_blocks
        has_return_info := hwt.has_return_info
        varStore_locs_bound := by
          intro y loc_y hvar
          rw [writeRef_preserves_nextLoc m.heap loc path newVec heap' hwrite]
          exact hwt.varStore_locs_bound y loc_y hvar
      }
    · simp at hstep  -- j out of bounds → contradiction
  · simp at hstep    -- i out of bounds → contradiction

private lemma lookup_delete_delete_first_none {K V : Type} [DecidableEq K]
    (m : AssocMap K V) (k1 k2 : K) : lookup (delete (delete m k1) k2) k1 = none := by
  by_cases heq : k1 = k2
  · rw [← heq, lookup_delete_same]
  · rw [lookup_delete_ne _ k2 k1 heq, lookup_delete_same]

-- vecImmBorrow and vecMutBorrow: these are similar to borrowField/borrowMutField
-- They create a new heap allocation and extend rmap with a fresh ref
-- For now, we use the borrowField machinery with .vecElem path instead of .field field
private theorem preservation_vecImmBorrow (m m' : Machine) (env : TypeEnv) (lenv : LabelEnv)
    (retTypes : List ParamType) (rmap : RefMap)
    (hwt : WellTypedState m env lenv retTypes rmap)
    (hss : StackSafe env.enumEnv m.stack m.frame.returnInfo m.heap retTypes)
    (s : Site) (src idx : Site) (cont : Stmt)
    (hstmt : m.frame.stmt = .letBind s (.vecImmBorrow src idx) cont)
    (hstep : step (.running m) = .running m') :
    ∃ env' lenv' retTypes' rmap',
      env'.enumEnv = env.enumEnv ∧ WellTypedState m' env' lenv' retTypes' rmap' ∧
      StackSafe env.enumEnv m'.stack m'.frame.returnInfo m'.heap retTypes' := by
  obtain ⟨T, s_ref, rf, isBor, hlookup_src, hlookup_idx, hnotIn, houtbound, hfresh, hcont⟩ :=
    inv_vecImmBorrow (by rw [← hstmt]; exact hwt.stmt_typed)
  -- Get values
  obtain ⟨vsrc, hvsrc, hmatch_src⟩ := hwt.site_consistent src _ hlookup_src
  simp only [ValueMatchesType] at hmatch_src
  obtain ⟨loc, path, hveq_src, hrmap_s⟩ := hmatch_src
  subst hveq_src
  obtain ⟨vidx, hvidx, hmatch_idx⟩ := hwt.site_consistent idx _ hlookup_idx
  simp only [ValueMatchesType] at hmatch_idx
  obtain ⟨i_val, rfl⟩ : ∃ n, vidx = .int n := by cases hmatch_idx with | int n => exact ⟨n, rfl⟩
  -- Get vector from heap
  obtain ⟨heap_val, hread_heap, hht_heap⟩ := hwt.rmap_has_type s_ref (.tvec T) loc path hrmap_s
    (Or.inr ⟨src, isBor, hlookup_src⟩)
  obtain ⟨elems, rfl⟩ := HasType.vec_elems hht_heap
  -- Simplify step
  have hrs_src : readSite m src = some (.ref loc path) := by unfold readSite; exact hvsrc
  have hrs_idx : readSite m idx = some (.int i_val) := by unfold readSite; exact hvidx
  simp only [step, hstmt, hrs_src, hrs_idx, hread_heap] at hstep
  -- Handle index bounds
  split at hstep
  · -- In bounds
    rename_i hi
    -- Name alloc components transparently (so heap'/elemLoc are definitionally projections)
    let elem : Value := elems[i_val]
    let heap' := (m.heap.alloc elem).1
    let elemLoc := (m.heap.alloc elem).2
    dsimp only [Heap.alloc] at hstep
    simp only [ExecState.running.injEq] at hstep
    subst hstep
    -- 1. Key definitions
    let rmap' : RefMap := { map := fun r => if r = rf then some (elemLoc, []) else rmap.map r }
    let pe' := update_with_extension rf s_ref [.vecElem] env.pathEnv
    let se' := insert (delete (delete env.siteEnv src) idx) s (.ref T rf .siteBorrowImm)
    -- 2. Freshness facts
    have hfresh_bool : freshRefInEnvBool rf env = true :=
      (freshRefInEnv_iff_freshRefInEnvBool rf env).mp hfresh
    have hfresh_pathEnv : freshRefBool rf env.pathEnv :=
      freshRefInEnvBool_implies_freshRefBool rf env hfresh_bool
    have hrf_not_root : rf ≠ Aref.root := freshRef_not_root hwt.env_wf.pathEnv_wf rf hfresh_pathEnv
    have hrf_fresh_pe : rf ∉ env.pathEnv.refs :=
      (freshRef_iff_freshRefBool rf env.pathEnv).mpr hfresh_pathEnv
    have hs_not_root : s_ref ≠ .root := hwt.env_wf.siteEnv_wf src (.ref (.tvec T) s_ref isBor) hlookup_src
    have hs_in_refs : s_ref ∈ env.pathEnv.refs := hwt.siteEnv_refs_in_pathEnv src (.tvec T) s_ref isBor hlookup_src
    have hrf_ne_s : rf ≠ s_ref := fun h => hrf_fresh_pe (h ▸ hs_in_refs)
    -- 3. Heap facts
    have hht_elem : HasType env.enumEnv elem T := by
      cases hht_heap with | vec _ _ h => exact h _ (List.getElem_mem hi)
    have helemLoc : elemLoc = m.heap.nextLoc := rfl
    have hread_new : heap'.read elemLoc = some elem := by
      rw [helemLoc]; exact heap_alloc_read_same m.heap elem
    have hreadRef_new : heap'.readRef elemLoc [] = some elem := by
      simp [Heap.readRef, readPath, hread_new]
    have hreadRef_old : ∀ l p, m.heap.read l ≠ none →
        heap'.readRef l p = m.heap.readRef l p :=
      fun l p hne => heap_alloc_preserves_readRef m.heap elem l p
        (Nat.ne_of_lt (hwt.heap_loc_bound l hne))
    -- 4. pe' refs
    have hrefs_eq : pe'.refs = rf :: env.pathEnv.refs := by
      simp only [pe', update_with_extension, hrf_fresh_pe, not_false_eq_true, ↓reduceIte]
    -- 5. rmap' helpers
    have hrmap'_rf : rmap'.map rf = some (elemLoc, []) := by simp [rmap']
    have hrmap'_ne : ∀ r, r ≠ rf → rmap'.map r = rmap.map r := by
      intro r hr; simp [rmap', hr]
    -- 6. StackSafe for new heap
    have hss' : StackSafe env.enumEnv m.stack m.frame.returnInfo heap' retTypes :=
      stackSafe_heap_alloc env.enumEnv m.stack m.frame.returnInfo m.heap elem hss hwt.heap_loc_bound
    -- 7. Construct WellTypedState
    refine ⟨{env with siteEnv := se', pathEnv := pe'}, lenv, retTypes, rmap', rfl, ?_, hss'⟩
    exact {
      env_wf := TypeEnv.delete_delete_insert_pathEnv_wf env src idx s (.ref T rf .siteBorrowImm) pe' hwt.env_wf
        (update_with_extension_wellformed rf s_ref [.vecElem] env.pathEnv hwt.env_wf.pathEnv_wf
          hrf_not_root) hrf_not_root
      enumEnv_consistent := hwt.enumEnv_consistent
      enum_qualified_nodup := hwt.enum_qualified_nodup
      enum_names_nodup := hwt.enum_names_nodup
      enum_variant_nodup := hwt.enum_variant_nodup
      enum_fields_nodup := hwt.enum_fields_nodup
      defaultValues_typed := hwt.defaultValues_typed
      stmt_typed := hcont
      var_consistent := by
        intro y isv τ ms hvy
        have hold := hwt.var_consistent y isv τ ms hvy
        cases isv with
        | invalidVar =>
          rcases hold with hl | ⟨l, hl⟩
          · exact Or.inl hl
          · exact Or.inr ⟨l, hl⟩
        | validVar =>
          obtain ⟨l, v, hl, hr, hm⟩ := hold
          have hloc_lt := hwt.heap_loc_bound l (by rw [hr]; exact fun h => nomatch h)
          have hne : l ≠ m.heap.nextLoc := Nat.ne_of_lt hloc_lt
          refine ⟨l, v, hl, (heap_alloc_read_ne m.heap elem l hne).trans hr, ?_⟩
          cases τ with
          | basic _ => exact hm
          | ref bt r_y bk =>
            obtain ⟨loc_v, path_v, hv_eq, hrmap_r⟩ := hm
            by_cases hrt : r_y = rf
            · exact absurd hrt.symm (freshRefInEnv_ne_varEnv_ref rf env y .validVar bt r_y bk ms hfresh hvy)
            · refine ⟨loc_v, path_v, hv_eq, ?_⟩
              show (if r_y = rf then _ else rmap.map r_y) = _
              rw [if_neg hrt]; exact hrmap_r
      site_consistent := by
        intro s' τ' hl
        by_cases heq : s' = s
        · subst heq; rw [lookup_insert_same] at hl; injection hl with hl; subst hl
          refine ⟨Value.ref elemLoc [], lookup_insert_same _ _ _, elemLoc, [], rfl, ?_⟩
          show (if rf = rf then some (elemLoc, []) else rmap.map rf) = some (elemLoc, [])
          rw [if_pos rfl]
        · rw [lookup_insert_ne _ s s' _ heq] at hl
          have hne_src : s' ≠ src := by
            intro h; subst h; rw [lookup_delete_delete_first_none] at hl; cases hl
          have hne_idx : s' ≠ idx := by
            intro h; subst h; rw [lookup_delete_same] at hl; cases hl
          rw [lookup_delete_ne _ idx s' hne_idx, lookup_delete_ne _ src s' hne_src] at hl
          obtain ⟨v', hv', hm⟩ := hwt.site_consistent s' τ' hl
          refine ⟨v', by rw [lookup_insert_ne _ s s' _ heq]; exact hv', ?_⟩
          cases τ' with
          | basic _ => exact hm
          | ref bt r_s bk' =>
            obtain ⟨loc_v, path_v, hv_eq', hrmap_r⟩ := hm
            by_cases hrt : r_s = rf
            · exact absurd hrt.symm (freshRefInEnv_ne_siteEnv_ref rf env s' bt r_s bk' hfresh (hrt ▸ hl))
            · refine ⟨loc_v, path_v, hv_eq', ?_⟩
              show (if r_s = rf then _ else rmap.map r_s) = _
              rw [if_neg hrt]; exact hrmap_r
      rmap_live := by
        intro r' l p hr'_tracked hrmap_r'
        rw [hrefs_eq] at hr'_tracked
        simp only [List.mem_cons] at hr'_tracked
        by_cases hrt : r' = rf
        · subst hrt; simp only [rmap', ite_true] at hrmap_r'
          obtain ⟨h1, h2⟩ := Prod.mk.inj (Option.some.inj hrmap_r')
          subst h1; subst h2; exact hreadRef_new ▸ fun h => nomatch h
        · simp only [rmap', if_neg hrt] at hrmap_r'
          have hr'_old : r' ∈ env.pathEnv.refs := hr'_tracked.resolve_left hrt
          have hlive := hwt.rmap_live r' l p hr'_old hrmap_r'
          exact hreadRef_old l p (readRef_implies_read m.heap l p hlive) ▸ hlive
      rmap_paths := by
        intro r1 r2 hr1 hr2 p hp
        rw [hrefs_eq] at hr1 hr2
        simp only [List.mem_cons] at hr1 hr2
        rcases hr1 with h1eq | hr1_mem <;> rcases hr2 with h2eq | hr2_mem
        · -- (rf, rf): self-loop ε
          rw [h1eq, h2eq] at hp ⊢
          unfold pe' update_with_extension at hp
          simp only [↓reduceIte] at hp; subst hp
          unfold PathReflectedInHeap; simp only [hrmap'_rf]
          intro _; exact ⟨by simp [fieldPathOf], hreadRef_new ▸ fun h => nomatch h⟩
        · -- (rf, r2): paths via der
          rw [h1eq] at hp ⊢
          have hr2_ne : r2 ≠ rf := fun h => hrf_fresh_pe (h ▸ hr2_mem)
          unfold pe' update_with_extension at hp
          simp only [hr2_ne, and_false, ite_false, ite_true] at hp
          simp only [der, List.foldl] at hp
          have hold := hwt.rmap_paths s_ref r2 hs_in_refs hr2_mem (.vecElem :: p) hp
          unfold PathReflectedInHeap at hold ⊢
          rw [hrmap'_rf, hrmap'_ne r2 hr2_ne]
          cases hrmap_r2 : rmap.map r2 with
          | none => simp
          | some lr2 =>
            obtain ⟨loc2, path2⟩ := lr2
            simp only [hrmap_s] at hold; simp only [hrmap_r2] at hold ⊢
            intro heq_loc
            exfalso
            have hloc2_live := hwt.rmap_live r2 loc2 path2 hr2_mem hrmap_r2
            have hloc2_lt := hwt.heap_loc_bound loc2 (readRef_implies_read m.heap loc2 path2 hloc2_live)
            rw [helemLoc] at heq_loc; grind
        · -- (r1, rf): paths via extend
          rw [h2eq] at hp ⊢
          have hr1_ne : r1 ≠ rf := fun h => hrf_fresh_pe (h ▸ hr1_mem)
          unfold pe' update_with_extension at hp
          simp only [hr1_ne, false_and, ite_false, ite_true] at hp
          simp only [extend, List.foldl, interpret_regex] at hp
          obtain ⟨s1, s2, heq_p, hinterp1, hs2_eq⟩ := hp
          subst hs2_eq
          unfold PathReflectedInHeap; rw [hrmap'_ne r1 hr1_ne, hrmap'_rf]
          cases hrmap_r1 : rmap.map r1 with
          | none => simp
          | some lr1 =>
            obtain ⟨loc1, path1⟩ := lr1
            intro heq_loc
            exfalso
            have hloc1_live := hwt.rmap_live r1 loc1 path1 hr1_mem hrmap_r1
            have hloc1_lt := hwt.heap_loc_bound loc1 (readRef_implies_read m.heap loc1 path1 hloc1_live)
            rw [helemLoc] at heq_loc; grind
        · -- (r1, r2): both old, paths unchanged
          have hr1_ne : r1 ≠ rf := fun h => hrf_fresh_pe (h ▸ hr1_mem)
          have hr2_ne : r2 ≠ rf := fun h => hrf_fresh_pe (h ▸ hr2_mem)
          unfold pe' update_with_extension at hp
          simp only [hr1_ne, hr2_ne, false_and, ite_false] at hp
          have hold := hwt.rmap_paths r1 r2 hr1_mem hr2_mem p hp
          unfold PathReflectedInHeap at hold ⊢
          rw [hrmap'_ne r1 hr1_ne, hrmap'_ne r2 hr2_ne]
          cases hrmap_r1 : rmap.map r1 with
          | none => simp
          | some lr1 =>
            obtain ⟨loc1, path1⟩ := lr1
            cases hrmap_r2 : rmap.map r2 with
            | none => simp
            | some lr2 =>
              obtain ⟨loc2, path2⟩ := lr2
              simp only [hrmap_r1, hrmap_r2] at hold ⊢
              intro heq_loc
              obtain ⟨hpath, hlive⟩ := hold heq_loc
              exact ⟨hpath, hreadRef_old loc2 path2 (readRef_implies_read m.heap loc2 path2 hlive) ▸ hlive⟩
      varEnv_refs_in_pathEnv := by
        intro x bt r_v bk_v ms hv
        show r_v ∈ pe'.refs
        rw [hrefs_eq]
        exact List.mem_cons_of_mem rf (hwt.varEnv_refs_in_pathEnv x bt r_v bk_v ms hv)
      siteEnv_refs_in_pathEnv := by
        intro s' bt_s r_s bk_s hl
        show r_s ∈ pe'.refs
        rw [hrefs_eq]
        by_cases heq : s' = s
        · subst heq; rw [lookup_insert_same] at hl
          simp only [Option.some.injEq, MoveType.ref.injEq] at hl
          rw [hl.2.1.symm]; exact .head _
        · rw [lookup_insert_ne _ s s' _ heq] at hl
          have hne_src : s' ≠ src := by intro h; subst h; rw [lookup_delete_delete_first_none] at hl; cases hl
          have hne_idx : s' ≠ idx := by intro h; subst h; rw [lookup_delete_same] at hl; cases hl
          rw [lookup_delete_ne _ idx s' hne_idx, lookup_delete_ne _ src s' hne_src] at hl
          exact List.mem_cons_of_mem rf (hwt.siteEnv_refs_in_pathEnv s' bt_s r_s bk_s hl)
      live_refs_unique := by
        intro r_u
        refine ⟨fun x bt_x bk_x ms s' bt_s bk_s hvar hs => ?_,
                fun s1 s2 bt1 bt2 bk1 bk2 hne hs1 hs2 => ?_,
                fun x y bt1 bt2 bk1 bk2 ms1 ms2 hne hx hy =>
                  (hwt.live_refs_unique r_u).2.2 x y bt1 bt2 bk1 bk2 ms1 ms2 hne hx hy⟩
        · -- var-site
          by_cases heqs : s' = s
          · subst heqs; rw [lookup_insert_same] at hs
            simp only [Option.some.injEq, MoveType.ref.injEq] at hs
            rw [← hs.2.1] at hvar
            exact absurd (hwt.varEnv_refs_in_pathEnv x bt_x rf bk_x ms hvar) hrf_fresh_pe
          · rw [lookup_insert_ne _ s s' _ heqs] at hs
            have hne_src : s' ≠ src := by intro h; subst h; rw [lookup_delete_delete_first_none] at hs; cases hs
            have hne_idx : s' ≠ idx := by intro h; subst h; rw [lookup_delete_same] at hs; cases hs
            rw [lookup_delete_ne _ idx s' hne_idx, lookup_delete_ne _ src s' hne_src] at hs
            exact (hwt.live_refs_unique r_u).1 x bt_x bk_x ms s' bt_s bk_s hvar hs
        · -- site-site
          by_cases heq1 : s1 = s
          · subst heq1; rw [lookup_insert_same] at hs1
            simp only [Option.some.injEq, MoveType.ref.injEq] at hs1
            rw [lookup_insert_ne _ s1 s2 _ hne.symm] at hs2
            have hne_src2 : s2 ≠ src := by intro h; subst h; rw [lookup_delete_delete_first_none] at hs2; cases hs2
            have hne_idx2 : s2 ≠ idx := by intro h; subst h; rw [lookup_delete_same] at hs2; cases hs2
            rw [lookup_delete_ne _ idx s2 hne_idx2, lookup_delete_ne _ src s2 hne_src2] at hs2
            rw [← hs1.2.1] at hs2
            exact absurd (hwt.siteEnv_refs_in_pathEnv s2 bt2 rf bk2 hs2) hrf_fresh_pe
          · by_cases heq2 : s2 = s
            · subst heq2; rw [lookup_insert_same] at hs2
              simp only [Option.some.injEq, MoveType.ref.injEq] at hs2
              rw [lookup_insert_ne _ s2 s1 _ hne] at hs1
              have hne_src1 : s1 ≠ src := by intro h; subst h; rw [lookup_delete_delete_first_none] at hs1; cases hs1
              have hne_idx1 : s1 ≠ idx := by intro h; subst h; rw [lookup_delete_same] at hs1; cases hs1
              rw [lookup_delete_ne _ idx s1 hne_idx1, lookup_delete_ne _ src s1 hne_src1] at hs1
              rw [← hs2.2.1] at hs1
              exact absurd (hwt.siteEnv_refs_in_pathEnv s1 bt1 rf bk1 hs1) hrf_fresh_pe
            · rw [lookup_insert_ne _ s s1 _ heq1] at hs1
              rw [lookup_insert_ne _ s s2 _ heq2] at hs2
              have hne_src1 : s1 ≠ src := by intro h; subst h; rw [lookup_delete_delete_first_none] at hs1; cases hs1
              have hne_src2 : s2 ≠ src := by intro h; subst h; rw [lookup_delete_delete_first_none] at hs2; cases hs2
              have hne_idx1 : s1 ≠ idx := by intro h; subst h; rw [lookup_delete_same] at hs1; cases hs1
              have hne_idx2 : s2 ≠ idx := by intro h; subst h; rw [lookup_delete_same] at hs2; cases hs2
              rw [lookup_delete_ne _ idx s1 hne_idx1, lookup_delete_ne _ src s1 hne_src1] at hs1
              rw [lookup_delete_ne _ idx s2 hne_idx2, lookup_delete_ne _ src s2 hne_src2] at hs2
              exact (hwt.live_refs_unique r_u).2.1 s1 s2 bt1 bt2 bk1 bk2 hne hs1 hs2
      blocks_typed := hwt.blocks_typed
      lenv_empty_siteEnv := hwt.lenv_empty_siteEnv
      lenv_wf := hwt.lenv_wf
      lenv_var_tracked := hwt.lenv_var_tracked
      lenv_var_unique := hwt.lenv_var_unique
      lenv_funEnv_eq := hwt.lenv_funEnv_eq
      funEnv_typed := hwt.funEnv_typed
      heap_loc_bound := heap_loc_bound_after_alloc m.heap elem hwt.heap_loc_bound
      rmap_root_none := by
        show (if Aref.root = rf then some (elemLoc, []) else rmap.map .root) = none
        rw [if_neg (Ne.symm hrf_not_root)]; exact hwt.rmap_root_none
      no_paths_to_root := by
        have hroot_ne_rf : ¬(Aref.root = rf) := Ne.symm hrf_not_root
        intro u p hp
        by_cases hu : u = rf
        · rw [hu] at hp
          unfold pe' update_with_extension at hp
          simp only [hroot_ne_rf, and_false, ite_false, ite_true] at hp
          simp only [der, List.foldl] at hp
          have ⟨hueq, _⟩ := hwt.no_paths_to_root s_ref _ hp
          exact absurd hueq hs_not_root
        · unfold pe' update_with_extension at hp
          simp only [hu, hroot_ne_rf, ite_false] at hp
          exact hwt.no_paths_to_root u p hp
      root_path_coherence := by
        have hroot_ne_rf : ¬(Aref.root = rf) := Ne.symm hrf_not_root
        intro v' y rest hv_mem hp loc_v path_v hrmap_v loc_y hloc heq_loc
        rw [hrefs_eq] at hv_mem
        simp only [List.mem_cons] at hv_mem
        rcases hv_mem with hv_eq | hv_in
        · -- v' = rf: rmap'(rf) = (elemLoc, []), elemLoc = heap.nextLoc
          -- But loc_y < heap.nextLoc by varStore_locs_bound, so elemLoc ≠ loc_y → contradiction
          rw [hv_eq] at hrmap_v
          simp only [rmap', ite_true] at hrmap_v
          obtain ⟨h1, h2⟩ := Prod.mk.inj (Option.some.inj hrmap_v)
          subst h1; subst h2
          exfalso
          have hloc_y_lt := hwt.varStore_locs_bound y loc_y hloc
          rw [helemLoc] at heq_loc; grind
        · -- v' ≠ rf: delegate to old
          have hv_ne : ¬(v' = rf) := fun h => by subst h; exact absurd hv_in hrf_fresh_pe
          unfold pe' update_with_extension at hp
          simp only [hroot_ne_rf, hv_ne, false_and, ite_false] at hp
          simp only [rmap', if_neg hv_ne] at hrmap_v
          exact hwt.root_path_coherence v' y rest hv_in hp loc_v path_v hrmap_v loc_y hloc heq_loc
      paths_from_non_member_empty :=
        update_with_extension_paths_from_non_member rf s_ref [.vecElem] env.pathEnv
          hwt.paths_from_non_member_empty (Or.inl hs_in_refs)
      paths_to_non_member_empty :=
        update_with_extension_paths_to_non_member rf s_ref [.vecElem] env.pathEnv
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
        · -- r_arg = rf
          simp only [rmap', hrt, ite_true] at hrmap_r
          obtain ⟨h1, h2⟩ := Prod.mk.inj (Option.some.inj hrmap_r)
          rw [← h1, ← h2]
          rcases hcond with ⟨x', bk', ms', hvar'⟩ | ⟨s', bk', hsite'⟩
          · rw [hrt] at hvar'
            exact absurd (hwt.varEnv_refs_in_pathEnv x' bt_r rf bk' ms' hvar') hrf_fresh_pe
          · by_cases heqs : s' = s
            · subst heqs; rw [lookup_insert_same] at hsite'
              simp only [Option.some.injEq, MoveType.ref.injEq] at hsite'
              rw [hrt] at hsite'; rw [← hsite'.1]
              exact ⟨elem, hreadRef_new, hht_elem⟩
            · rw [lookup_insert_ne _ s s' _ heqs] at hsite'
              have hne_src : s' ≠ src := by intro h; subst h; rw [lookup_delete_delete_first_none] at hsite'; cases hsite'
              have hne_idx : s' ≠ idx := by intro h; subst h; rw [lookup_delete_same] at hsite'; cases hsite'
              rw [lookup_delete_ne _ idx s' hne_idx, lookup_delete_ne _ src s' hne_src] at hsite'
              rw [hrt] at hsite'
              exact absurd (hwt.siteEnv_refs_in_pathEnv s' bt_r rf bk' hsite') hrf_fresh_pe
        · -- r_arg ≠ rf
          simp only [rmap', if_neg hrt] at hrmap_r
          have hold := hwt.rmap_has_type r_arg bt_r loc_r path_r hrmap_r
          rcases hcond with ⟨x', bk', ms', hvar'⟩ | ⟨s', bk', hsite'⟩
          · obtain ⟨val, hread, hht⟩ := hold (Or.inl ⟨x', bk', ms', hvar'⟩)
            have hlive_r : m.heap.readRef loc_r path_r ≠ none := by rw [hread]; exact fun h => nomatch h
            exact ⟨val, (hreadRef_old loc_r path_r (readRef_implies_read m.heap loc_r path_r hlive_r)).trans hread, hht⟩
          · by_cases heqs : s' = s
            · subst heqs; rw [lookup_insert_same] at hsite'
              simp only [Option.some.injEq, MoveType.ref.injEq] at hsite'
              exact absurd hsite'.2.1.symm hrt
            · rw [lookup_insert_ne _ s s' _ heqs] at hsite'
              have hne_src : s' ≠ src := by intro h; subst h; rw [lookup_delete_delete_first_none] at hsite'; cases hsite'
              have hne_idx : s' ≠ idx := by
                intro h; subst h; rw [lookup_delete_same] at hsite'; cases hsite'
              rw [lookup_delete_ne _ idx s' hne_idx, lookup_delete_ne _ src s' hne_src] at hsite'
              obtain ⟨val, hread, hht⟩ := hold (Or.inr ⟨s', bk', hsite'⟩)
              have hlive_r : m.heap.readRef loc_r path_r ≠ none := by rw [hread]; exact fun h => nomatch h
              exact ⟨val, (hreadRef_old loc_r path_r (readRef_implies_read m.heap loc_r path_r hlive_r)).trans hread, hht⟩
      funEnv_sig_consistent := hwt.funEnv_sig_consistent
      refs_tracked_mapped := by
        intro ref href
        rw [hrefs_eq] at href
        simp only [List.mem_cons] at href
        rcases href with heq | href_old
        · rw [heq]; right
          show (if rf = rf then some (elemLoc, []) else rmap.map rf) ≠ none
          simp
        · cases hwt.refs_tracked_mapped ref href_old with
          | inl h => exact Or.inl h
          | inr h =>
            right
            show (if ref = rf then some (elemLoc, []) else rmap.map ref) ≠ none
            have hne : ref ≠ rf := fun heq => hrf_fresh_pe (heq ▸ href_old)
            simp [hne]; exact h
      lenv_labels_in_blocks := hwt.lenv_labels_in_blocks
      has_return_info := hwt.has_return_info
      varStore_locs_bound := by
        intro y loc_y hvar
        have hlt := hwt.varStore_locs_bound y loc_y hvar
        exact lt_heap_alloc_nextLoc m.heap elem loc_y hlt
    }
  · -- Out of bounds → vectorError → contradiction
    simp at hstep

private theorem preservation_vecMutBorrow (m m' : Machine) (env : TypeEnv) (lenv : LabelEnv)
    (retTypes : List ParamType) (rmap : RefMap)
    (hwt : WellTypedState m env lenv retTypes rmap)
    (hss : StackSafe env.enumEnv m.stack m.frame.returnInfo m.heap retTypes)
    (s : Site) (src idx : Site) (cont : Stmt)
    (hstmt : m.frame.stmt = .letBind s (.vecMutBorrow src idx) cont)
    (hstep : step (.running m) = .running m') :
    ∃ env' lenv' retTypes' rmap',
      env'.enumEnv = env.enumEnv ∧ WellTypedState m' env' lenv' retTypes' rmap' ∧
      StackSafe env.enumEnv m'.stack m'.frame.returnInfo m'.heap retTypes' := by
  -- vecMutBorrow has identical runtime semantics to vecImmBorrow
  -- Only the typing differs (siteBorrowMut vs siteBorrowImm)
  obtain ⟨T, s_ref, rf, hlookup_src, hlookup_idx, hnotIn, houtbound, hfresh, hcont⟩ :=
    inv_vecMutBorrow (by rw [← hstmt]; exact hwt.stmt_typed)
  obtain ⟨vsrc, hvsrc, hmatch_src⟩ := hwt.site_consistent src _ hlookup_src
  simp only [ValueMatchesType] at hmatch_src
  obtain ⟨loc, path, hveq_src, hrmap_s⟩ := hmatch_src
  subst hveq_src
  obtain ⟨vidx, hvidx, hmatch_idx⟩ := hwt.site_consistent idx _ hlookup_idx
  simp only [ValueMatchesType] at hmatch_idx
  obtain ⟨i_val, rfl⟩ : ∃ n, vidx = .int n := by cases hmatch_idx with | int n => exact ⟨n, rfl⟩
  obtain ⟨heap_val, hread_heap, hht_heap⟩ := hwt.rmap_has_type s_ref (.tvec T) loc path hrmap_s
    (Or.inr ⟨src, .siteBorrowMut, hlookup_src⟩)
  obtain ⟨elems, rfl⟩ := HasType.vec_elems hht_heap
  have hrs_src : readSite m src = some (.ref loc path) := by unfold readSite; exact hvsrc
  have hrs_idx : readSite m idx = some (.int i_val) := by unfold readSite; exact hvidx
  simp only [step, hstmt, hrs_src, hrs_idx, hread_heap] at hstep
  split at hstep
  · rename_i hi
    -- Name alloc components transparently (so heap'/elemLoc are definitionally projections)
    let elem : Value := elems[i_val]
    let heap' := (m.heap.alloc elem).1
    let elemLoc := (m.heap.alloc elem).2
    dsimp only [Heap.alloc] at hstep
    simp only [ExecState.running.injEq] at hstep
    subst hstep
    let rmap' : RefMap := { map := fun r => if r = rf then some (elemLoc, []) else rmap.map r }
    let pe' := update_with_extension rf s_ref [.vecElem] env.pathEnv
    let se' := insert (delete (delete env.siteEnv src) idx) s (.ref T rf .siteBorrowMut)
    have hfresh_bool : freshRefInEnvBool rf env = true :=
      (freshRefInEnv_iff_freshRefInEnvBool rf env).mp hfresh
    have hfresh_pathEnv : freshRefBool rf env.pathEnv :=
      freshRefInEnvBool_implies_freshRefBool rf env hfresh_bool
    have hrf_not_root : rf ≠ Aref.root := freshRef_not_root hwt.env_wf.pathEnv_wf rf hfresh_pathEnv
    have hrf_fresh_pe : rf ∉ env.pathEnv.refs :=
      (freshRef_iff_freshRefBool rf env.pathEnv).mpr hfresh_pathEnv
    have hs_not_root : s_ref ≠ .root := hwt.env_wf.siteEnv_wf src (.ref (.tvec T) s_ref .siteBorrowMut) hlookup_src
    have hs_in_refs : s_ref ∈ env.pathEnv.refs := hwt.siteEnv_refs_in_pathEnv src (.tvec T) s_ref .siteBorrowMut hlookup_src
    have hrf_ne_s : rf ≠ s_ref := fun h => hrf_fresh_pe (h ▸ hs_in_refs)
    have hht_elem : HasType env.enumEnv elem T := by
      cases hht_heap with | vec _ _ h => exact h _ (List.getElem_mem hi)
    have helemLoc : elemLoc = m.heap.nextLoc := rfl
    have hread_new : heap'.read elemLoc = some elem := by
      rw [helemLoc]; exact heap_alloc_read_same m.heap elem
    have hreadRef_new : heap'.readRef elemLoc [] = some elem := by
      simp [Heap.readRef, readPath, hread_new]
    have hreadRef_old : ∀ l p, m.heap.read l ≠ none →
        heap'.readRef l p = m.heap.readRef l p :=
      fun l p hne => heap_alloc_preserves_readRef m.heap elem l p
        (Nat.ne_of_lt (hwt.heap_loc_bound l hne))
    have hrefs_eq : pe'.refs = rf :: env.pathEnv.refs := by
      simp only [pe', update_with_extension, hrf_fresh_pe, not_false_eq_true, ↓reduceIte]
    have hrmap'_rf : rmap'.map rf = some (elemLoc, []) := by simp [rmap']
    have hrmap'_ne : ∀ r, r ≠ rf → rmap'.map r = rmap.map r := by
      intro r hr; simp [rmap', hr]
    have hss' : StackSafe env.enumEnv m.stack m.frame.returnInfo heap' retTypes :=
      stackSafe_heap_alloc env.enumEnv m.stack m.frame.returnInfo m.heap elem hss hwt.heap_loc_bound
    refine ⟨{env with siteEnv := se', pathEnv := pe'}, lenv, retTypes, rmap', rfl, ?_, hss'⟩
    exact {
      env_wf := TypeEnv.delete_delete_insert_pathEnv_wf env src idx s (.ref T rf .siteBorrowMut) pe' hwt.env_wf
        (update_with_extension_wellformed rf s_ref [.vecElem] env.pathEnv hwt.env_wf.pathEnv_wf
          hrf_not_root) hrf_not_root
      enumEnv_consistent := hwt.enumEnv_consistent
      enum_qualified_nodup := hwt.enum_qualified_nodup
      enum_names_nodup := hwt.enum_names_nodup
      enum_variant_nodup := hwt.enum_variant_nodup
      enum_fields_nodup := hwt.enum_fields_nodup
      defaultValues_typed := hwt.defaultValues_typed
      stmt_typed := hcont
      var_consistent := by
        intro y isv τ ms hvy
        have hold := hwt.var_consistent y isv τ ms hvy
        cases isv with
        | invalidVar =>
          rcases hold with hl | ⟨l, hl⟩
          · exact Or.inl hl
          · exact Or.inr ⟨l, hl⟩
        | validVar =>
          obtain ⟨l, v, hl, hr, hm⟩ := hold
          have hloc_lt := hwt.heap_loc_bound l (by rw [hr]; exact fun h => nomatch h)
          have hne : l ≠ m.heap.nextLoc := Nat.ne_of_lt hloc_lt
          refine ⟨l, v, hl, (heap_alloc_read_ne m.heap elem l hne).trans hr, ?_⟩
          cases τ with
          | basic _ => exact hm
          | ref bt r_y bk =>
            obtain ⟨loc_v, path_v, hv_eq, hrmap_r⟩ := hm
            by_cases hrt : r_y = rf
            · exact absurd hrt.symm (freshRefInEnv_ne_varEnv_ref rf env y .validVar bt r_y bk ms hfresh hvy)
            · refine ⟨loc_v, path_v, hv_eq, ?_⟩
              show (if r_y = rf then _ else rmap.map r_y) = _
              rw [if_neg hrt]; exact hrmap_r
      site_consistent := by
        intro s' τ' hl
        by_cases heq : s' = s
        · subst heq; rw [lookup_insert_same] at hl; injection hl with hl; subst hl
          refine ⟨Value.ref elemLoc [], lookup_insert_same _ _ _, elemLoc, [], rfl, ?_⟩
          show (if rf = rf then some (elemLoc, []) else rmap.map rf) = some (elemLoc, [])
          rw [if_pos rfl]
        · rw [lookup_insert_ne _ s s' _ heq] at hl
          have hne_src : s' ≠ src := by
            intro h; subst h; rw [lookup_delete_delete_first_none] at hl; cases hl
          have hne_idx : s' ≠ idx := by
            intro h; subst h; rw [lookup_delete_same] at hl; cases hl
          rw [lookup_delete_ne _ idx s' hne_idx, lookup_delete_ne _ src s' hne_src] at hl
          obtain ⟨v', hv', hm⟩ := hwt.site_consistent s' τ' hl
          refine ⟨v', by rw [lookup_insert_ne _ s s' _ heq]; exact hv', ?_⟩
          cases τ' with
          | basic _ => exact hm
          | ref bt r_s bk' =>
            obtain ⟨loc_v, path_v, hv_eq', hrmap_r⟩ := hm
            by_cases hrt : r_s = rf
            · exact absurd hrt.symm (freshRefInEnv_ne_siteEnv_ref rf env s' bt r_s bk' hfresh (hrt ▸ hl))
            · refine ⟨loc_v, path_v, hv_eq', ?_⟩
              show (if r_s = rf then _ else rmap.map r_s) = _
              rw [if_neg hrt]; exact hrmap_r
      rmap_live := by
        intro r' l p hr'_tracked hrmap_r'
        rw [hrefs_eq] at hr'_tracked
        simp only [List.mem_cons] at hr'_tracked
        by_cases hrt : r' = rf
        · subst hrt; simp only [rmap', ite_true] at hrmap_r'
          obtain ⟨h1, h2⟩ := Prod.mk.inj (Option.some.inj hrmap_r')
          subst h1; subst h2; exact hreadRef_new ▸ fun h => nomatch h
        · simp only [rmap', if_neg hrt] at hrmap_r'
          have hr'_old : r' ∈ env.pathEnv.refs := hr'_tracked.resolve_left hrt
          have hlive := hwt.rmap_live r' l p hr'_old hrmap_r'
          exact hreadRef_old l p (readRef_implies_read m.heap l p hlive) ▸ hlive
      rmap_paths := by
        intro r1 r2 hr1 hr2 p hp
        rw [hrefs_eq] at hr1 hr2
        simp only [List.mem_cons] at hr1 hr2
        rcases hr1 with h1eq | hr1_mem <;> rcases hr2 with h2eq | hr2_mem
        · rw [h1eq, h2eq] at hp ⊢
          unfold pe' update_with_extension at hp
          simp only [↓reduceIte] at hp; subst hp
          unfold PathReflectedInHeap; simp only [hrmap'_rf]
          intro _; exact ⟨by simp [fieldPathOf], hreadRef_new ▸ fun h => nomatch h⟩
        · rw [h1eq] at hp ⊢
          have hr2_ne : r2 ≠ rf := fun h => hrf_fresh_pe (h ▸ hr2_mem)
          unfold pe' update_with_extension at hp
          simp only [hr2_ne, and_false, ite_false, ite_true] at hp
          simp only [der, List.foldl] at hp
          have hold := hwt.rmap_paths s_ref r2 hs_in_refs hr2_mem (.vecElem :: p) hp
          unfold PathReflectedInHeap at hold ⊢
          rw [hrmap'_rf, hrmap'_ne r2 hr2_ne]
          cases hrmap_r2 : rmap.map r2 with
          | none => simp
          | some lr2 =>
            obtain ⟨loc2, path2⟩ := lr2
            simp only [hrmap_s] at hold; simp only [hrmap_r2] at hold ⊢
            intro heq_loc
            exfalso
            have hloc2_live := hwt.rmap_live r2 loc2 path2 hr2_mem hrmap_r2
            have hloc2_lt := hwt.heap_loc_bound loc2 (readRef_implies_read m.heap loc2 path2 hloc2_live)
            rw [helemLoc] at heq_loc; grind
        · rw [h2eq] at hp ⊢
          have hr1_ne : r1 ≠ rf := fun h => hrf_fresh_pe (h ▸ hr1_mem)
          unfold pe' update_with_extension at hp
          simp only [hr1_ne, false_and, ite_false, ite_true] at hp
          simp only [extend, List.foldl, interpret_regex] at hp
          obtain ⟨s1, s2, heq_p, hinterp1, hs2_eq⟩ := hp
          subst hs2_eq
          unfold PathReflectedInHeap; rw [hrmap'_ne r1 hr1_ne, hrmap'_rf]
          cases hrmap_r1 : rmap.map r1 with
          | none => simp
          | some lr1 =>
            obtain ⟨loc1, path1⟩ := lr1
            intro heq_loc
            exfalso
            have hloc1_live := hwt.rmap_live r1 loc1 path1 hr1_mem hrmap_r1
            have hloc1_lt := hwt.heap_loc_bound loc1 (readRef_implies_read m.heap loc1 path1 hloc1_live)
            rw [helemLoc] at heq_loc; grind
        · have hr1_ne : r1 ≠ rf := fun h => hrf_fresh_pe (h ▸ hr1_mem)
          have hr2_ne : r2 ≠ rf := fun h => hrf_fresh_pe (h ▸ hr2_mem)
          unfold pe' update_with_extension at hp
          simp only [hr1_ne, hr2_ne, false_and, ite_false] at hp
          have hold := hwt.rmap_paths r1 r2 hr1_mem hr2_mem p hp
          unfold PathReflectedInHeap at hold ⊢
          rw [hrmap'_ne r1 hr1_ne, hrmap'_ne r2 hr2_ne]
          cases hrmap_r1 : rmap.map r1 with
          | none => simp
          | some lr1 =>
            obtain ⟨loc1, path1⟩ := lr1
            cases hrmap_r2 : rmap.map r2 with
            | none => simp
            | some lr2 =>
              obtain ⟨loc2, path2⟩ := lr2
              simp only [hrmap_r1, hrmap_r2] at hold ⊢
              intro heq_loc
              obtain ⟨hpath, hlive⟩ := hold heq_loc
              exact ⟨hpath, hreadRef_old loc2 path2 (readRef_implies_read m.heap loc2 path2 hlive) ▸ hlive⟩
      varEnv_refs_in_pathEnv := by
        intro x bt r_v bk_v ms hv
        show r_v ∈ pe'.refs
        rw [hrefs_eq]
        exact List.mem_cons_of_mem rf (hwt.varEnv_refs_in_pathEnv x bt r_v bk_v ms hv)
      siteEnv_refs_in_pathEnv := by
        intro s' bt_s r_s bk_s hl
        show r_s ∈ pe'.refs
        rw [hrefs_eq]
        by_cases heq : s' = s
        · subst heq; rw [lookup_insert_same] at hl
          simp only [Option.some.injEq, MoveType.ref.injEq] at hl
          rw [hl.2.1.symm]; exact .head _
        · rw [lookup_insert_ne _ s s' _ heq] at hl
          have hne_src : s' ≠ src := by intro h; subst h; rw [lookup_delete_delete_first_none] at hl; cases hl
          have hne_idx : s' ≠ idx := by intro h; subst h; rw [lookup_delete_same] at hl; cases hl
          rw [lookup_delete_ne _ idx s' hne_idx, lookup_delete_ne _ src s' hne_src] at hl
          exact List.mem_cons_of_mem rf (hwt.siteEnv_refs_in_pathEnv s' bt_s r_s bk_s hl)
      live_refs_unique := by
        intro r_u
        refine ⟨fun x bt_x bk_x ms s' bt_s bk_s hvar hs => ?_,
                fun s1 s2 bt1 bt2 bk1 bk2 hne hs1 hs2 => ?_,
                fun x y bt1 bt2 bk1 bk2 ms1 ms2 hne hx hy =>
                  (hwt.live_refs_unique r_u).2.2 x y bt1 bt2 bk1 bk2 ms1 ms2 hne hx hy⟩
        · by_cases heqs : s' = s
          · subst heqs; rw [lookup_insert_same] at hs
            simp only [Option.some.injEq, MoveType.ref.injEq] at hs
            rw [← hs.2.1] at hvar
            exact absurd (hwt.varEnv_refs_in_pathEnv x bt_x rf bk_x ms hvar) hrf_fresh_pe
          · rw [lookup_insert_ne _ s s' _ heqs] at hs
            have hne_src : s' ≠ src := by intro h; subst h; rw [lookup_delete_delete_first_none] at hs; cases hs
            have hne_idx : s' ≠ idx := by intro h; subst h; rw [lookup_delete_same] at hs; cases hs
            rw [lookup_delete_ne _ idx s' hne_idx, lookup_delete_ne _ src s' hne_src] at hs
            exact (hwt.live_refs_unique r_u).1 x bt_x bk_x ms s' bt_s bk_s hvar hs
        · by_cases heq1 : s1 = s
          · subst heq1; rw [lookup_insert_same] at hs1
            simp only [Option.some.injEq, MoveType.ref.injEq] at hs1
            rw [lookup_insert_ne _ s1 s2 _ hne.symm] at hs2
            have hne_src2 : s2 ≠ src := by intro h; subst h; rw [lookup_delete_delete_first_none] at hs2; cases hs2
            have hne_idx2 : s2 ≠ idx := by intro h; subst h; rw [lookup_delete_same] at hs2; cases hs2
            rw [lookup_delete_ne _ idx s2 hne_idx2, lookup_delete_ne _ src s2 hne_src2] at hs2
            rw [← hs1.2.1] at hs2
            exact absurd (hwt.siteEnv_refs_in_pathEnv s2 bt2 rf bk2 hs2) hrf_fresh_pe
          · by_cases heq2 : s2 = s
            · subst heq2; rw [lookup_insert_same] at hs2
              simp only [Option.some.injEq, MoveType.ref.injEq] at hs2
              rw [lookup_insert_ne _ s2 s1 _ hne] at hs1
              have hne_src1 : s1 ≠ src := by intro h; subst h; rw [lookup_delete_delete_first_none] at hs1; cases hs1
              have hne_idx1 : s1 ≠ idx := by intro h; subst h; rw [lookup_delete_same] at hs1; cases hs1
              rw [lookup_delete_ne _ idx s1 hne_idx1, lookup_delete_ne _ src s1 hne_src1] at hs1
              rw [← hs2.2.1] at hs1
              exact absurd (hwt.siteEnv_refs_in_pathEnv s1 bt1 rf bk1 hs1) hrf_fresh_pe
            · rw [lookup_insert_ne _ s s1 _ heq1] at hs1
              rw [lookup_insert_ne _ s s2 _ heq2] at hs2
              have hne_src1 : s1 ≠ src := by intro h; subst h; rw [lookup_delete_delete_first_none] at hs1; cases hs1
              have hne_src2 : s2 ≠ src := by intro h; subst h; rw [lookup_delete_delete_first_none] at hs2; cases hs2
              have hne_idx1 : s1 ≠ idx := by intro h; subst h; rw [lookup_delete_same] at hs1; cases hs1
              have hne_idx2 : s2 ≠ idx := by intro h; subst h; rw [lookup_delete_same] at hs2; cases hs2
              rw [lookup_delete_ne _ idx s1 hne_idx1, lookup_delete_ne _ src s1 hne_src1] at hs1
              rw [lookup_delete_ne _ idx s2 hne_idx2, lookup_delete_ne _ src s2 hne_src2] at hs2
              exact (hwt.live_refs_unique r_u).2.1 s1 s2 bt1 bt2 bk1 bk2 hne hs1 hs2
      blocks_typed := hwt.blocks_typed
      lenv_empty_siteEnv := hwt.lenv_empty_siteEnv
      lenv_wf := hwt.lenv_wf
      lenv_var_tracked := hwt.lenv_var_tracked
      lenv_var_unique := hwt.lenv_var_unique
      lenv_funEnv_eq := hwt.lenv_funEnv_eq
      funEnv_typed := hwt.funEnv_typed
      heap_loc_bound := heap_loc_bound_after_alloc m.heap elem hwt.heap_loc_bound
      rmap_root_none := by
        show (if Aref.root = rf then some (elemLoc, []) else rmap.map .root) = none
        rw [if_neg (Ne.symm hrf_not_root)]; exact hwt.rmap_root_none
      no_paths_to_root := by
        have hroot_ne_rf : ¬(Aref.root = rf) := Ne.symm hrf_not_root
        intro u p hp
        by_cases hu : u = rf
        · rw [hu] at hp
          unfold pe' update_with_extension at hp
          simp only [hroot_ne_rf, and_false, ite_false, ite_true] at hp
          simp only [der, List.foldl] at hp
          have ⟨hueq, _⟩ := hwt.no_paths_to_root s_ref _ hp
          exact absurd hueq hs_not_root
        · unfold pe' update_with_extension at hp
          simp only [hu, hroot_ne_rf, ite_false] at hp
          exact hwt.no_paths_to_root u p hp
      root_path_coherence := by
        have hroot_ne_rf : ¬(Aref.root = rf) := Ne.symm hrf_not_root
        intro v' y rest hv_mem hp loc_v path_v hrmap_v loc_y hloc heq_loc
        rw [hrefs_eq] at hv_mem
        simp only [List.mem_cons] at hv_mem
        rcases hv_mem with hv_eq | hv_in
        · rw [hv_eq] at hrmap_v
          simp only [rmap', ite_true] at hrmap_v
          obtain ⟨h1, h2⟩ := Prod.mk.inj (Option.some.inj hrmap_v)
          subst h1; subst h2
          exfalso
          have hloc_y_lt := hwt.varStore_locs_bound y loc_y hloc
          rw [helemLoc] at heq_loc; grind
        · have hv_ne : ¬(v' = rf) := fun h => by subst h; exact absurd hv_in hrf_fresh_pe
          unfold pe' update_with_extension at hp
          simp only [hroot_ne_rf, hv_ne, false_and, ite_false] at hp
          simp only [rmap', if_neg hv_ne] at hrmap_v
          exact hwt.root_path_coherence v' y rest hv_in hp loc_v path_v hrmap_v loc_y hloc heq_loc
      paths_from_non_member_empty :=
        update_with_extension_paths_from_non_member rf s_ref [.vecElem] env.pathEnv
          hwt.paths_from_non_member_empty (Or.inl hs_in_refs)
      paths_to_non_member_empty :=
        update_with_extension_paths_to_non_member rf s_ref [.vecElem] env.pathEnv
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
        · simp only [rmap', hrt, ite_true] at hrmap_r
          obtain ⟨h1, h2⟩ := Prod.mk.inj (Option.some.inj hrmap_r)
          rw [← h1, ← h2]
          rcases hcond with ⟨x', bk', ms', hvar'⟩ | ⟨s', bk', hsite'⟩
          · rw [hrt] at hvar'
            exact absurd (hwt.varEnv_refs_in_pathEnv x' bt_r rf bk' ms' hvar') hrf_fresh_pe
          · by_cases heqs : s' = s
            · subst heqs; rw [lookup_insert_same] at hsite'
              simp only [Option.some.injEq, MoveType.ref.injEq] at hsite'
              rw [hrt] at hsite'; rw [← hsite'.1]
              exact ⟨elem, hreadRef_new, hht_elem⟩
            · rw [lookup_insert_ne _ s s' _ heqs] at hsite'
              have hne_src : s' ≠ src := by intro h; subst h; rw [lookup_delete_delete_first_none] at hsite'; cases hsite'
              have hne_idx : s' ≠ idx := by
                intro h; subst h; rw [lookup_delete_same] at hsite'; cases hsite'
              rw [lookup_delete_ne _ idx s' hne_idx, lookup_delete_ne _ src s' hne_src] at hsite'
              rw [hrt] at hsite'
              exact absurd (hwt.siteEnv_refs_in_pathEnv s' bt_r rf bk' hsite') hrf_fresh_pe
        · simp only [rmap', if_neg hrt] at hrmap_r
          have hold := hwt.rmap_has_type r_arg bt_r loc_r path_r hrmap_r
          rcases hcond with ⟨x', bk', ms', hvar'⟩ | ⟨s', bk', hsite'⟩
          · obtain ⟨val, hread, hht⟩ := hold (Or.inl ⟨x', bk', ms', hvar'⟩)
            have hlive_r : m.heap.readRef loc_r path_r ≠ none := by rw [hread]; exact fun h => nomatch h
            exact ⟨val, (hreadRef_old loc_r path_r (readRef_implies_read m.heap loc_r path_r hlive_r)).trans hread, hht⟩
          · by_cases heqs : s' = s
            · subst heqs; rw [lookup_insert_same] at hsite'
              simp only [Option.some.injEq, MoveType.ref.injEq] at hsite'
              exact absurd hsite'.2.1.symm hrt
            · rw [lookup_insert_ne _ s s' _ heqs] at hsite'
              have hne_src : s' ≠ src := by intro h; subst h; rw [lookup_delete_delete_first_none] at hsite'; cases hsite'
              have hne_idx : s' ≠ idx := by
                intro h; subst h; rw [lookup_delete_same] at hsite'; cases hsite'
              rw [lookup_delete_ne _ idx s' hne_idx, lookup_delete_ne _ src s' hne_src] at hsite'
              obtain ⟨val, hread, hht⟩ := hold (Or.inr ⟨s', bk', hsite'⟩)
              have hlive_r : m.heap.readRef loc_r path_r ≠ none := by rw [hread]; exact fun h => nomatch h
              exact ⟨val, (hreadRef_old loc_r path_r (readRef_implies_read m.heap loc_r path_r hlive_r)).trans hread, hht⟩
      funEnv_sig_consistent := hwt.funEnv_sig_consistent
      refs_tracked_mapped := by
        intro ref href
        rw [hrefs_eq] at href
        simp only [List.mem_cons] at href
        rcases href with heq | href_old
        · rw [heq]; right
          show (if rf = rf then some (elemLoc, []) else rmap.map rf) ≠ none
          simp
        · cases hwt.refs_tracked_mapped ref href_old with
          | inl h => exact Or.inl h
          | inr h =>
            right
            show (if ref = rf then some (elemLoc, []) else rmap.map ref) ≠ none
            have hne : ref ≠ rf := fun heq => hrf_fresh_pe (heq ▸ href_old)
            simp [hne]; exact h
      lenv_labels_in_blocks := hwt.lenv_labels_in_blocks
      has_return_info := hwt.has_return_info
      varStore_locs_bound := by
        intro y loc_y hvar
        have hlt := hwt.varStore_locs_bound y loc_y hvar
        exact lt_heap_alloc_nextLoc m.heap elem loc_y hlt
    }
  · simp at hstep

-- ============================================================
-- Part 8a-enum: Preservation for enum operations
-- ============================================================

/-- Bridge lemma: if a variant's field has type bt (unqualified lookup),
    then the same field has the same type in allEnumFieldTypes (qualified lookup).
    Uses NoDup on qualified field names to ensure List.lookup finds the right entry. -/
private theorem allEnumFieldTypes_lookup_bridge
    {enumEnv : EnumEnv} {ename vname : Id} {enumDef : EnumDef}
    {variantDef : EnumVariantDef} {f : Field} {bt : BasicMoveType}
    (hlookup_enum : enumEnv.lookup ename = some enumDef)
    (hlookup_var : enumDef.variants.lookup vname = some variantDef)
    (hlookup_f : lookup variantDef.fields f = some bt)
    (hnodup : ((allEnumFieldTypes enumDef).map Prod.fst).Nodup) :
    ∃ fentries, allEnumQualifiedFieldTypes enumEnv ename = some fentries ∧
      lookup fentries (qualifyField vname f) = some bt := by
  refine ⟨⟨allEnumFieldTypes enumDef⟩, ?_, ?_⟩
  · -- allEnumQualifiedFieldTypes succeeds
    simp only [allEnumQualifiedFieldTypes, hlookup_enum]
  · -- List.lookup finds (qualifyField vname f, bt) in the flat list
    simp only [AssocMap.lookup]
    apply list_lookup_of_mem_nodup _ hnodup
    -- Show (qualifyField vname f, bt) ∈ allEnumFieldTypes enumDef
    simp only [allEnumFieldTypes]
    apply List.mem_flatMap.mpr
    refine ⟨(vname, variantDef), ?_, ?_⟩
    · exact lookup_some enumDef.variants vname variantDef hlookup_var
    · apply List.mem_map.mpr
      exact ⟨(f, bt), lookup_some variantDef.fields f bt hlookup_f, rfl⟩

/-- Rewrite buildFlatVariantFields into the standard (key, val) pair form.
    The let/if/match structure always produces qualifyField as the first component. -/
private lemma buildFlatVariantFields_eq_map
    (eeEntries : List (Id × EnumDef)) (enumDef : EnumDef)
    (av : Id) (af : List (Field × Value)) :
    buildFlatVariantFields eeEntries enumDef av af =
    enumDef.variants.entries.flatMap fun (vn, vd) =>
      vd.fields.entries.map fun (f, bt) =>
        (qualifyField vn f,
         if vn == av then
           match af.lookup f with
           | some v => v
           | none => defaultValue eeEntries bt
         else defaultValue eeEntries bt) := by
  simp only [buildFlatVariantFields]
  congr 1
  funext ⟨vn, vd⟩
  congr 1
  funext ⟨f, bt⟩
  dsimp only []
  split
  · split <;> grind
  · rfl

/-- buildFlatVariantFields produces a value with HasType for the enum. -/
private theorem buildFlatVariantFields_HasType
    {enumEnv : EnumEnv} {ename vname : Id} {enumDef : EnumDef}
    {variantDef : EnumVariantDef}
    (eeEntries : List (Id × EnumDef))
    (activeFields : List (Field × Value))
    (hlookup_enum : enumEnv.lookup ename = some enumDef)
    (hlookup_var : enumDef.variants.lookup vname = some variantDef)
    (hvariant_nodup : (enumDef.variants.entries.map Prod.fst).Nodup)
    (hfields_nodup : (variantDef.fields.entries.map Prod.fst).Nodup)
    (htyped : ∀ f bt v, variantDef.fields.lookup f = some bt →
      activeFields.lookup f = some v → HasType enumEnv v bt)
    (hdefault : ∀ vn' vd' f' bt', (vn', vd') ∈ enumDef.variants.entries →
      (f', bt') ∈ vd'.fields.entries → HasType enumEnv (defaultValue eeEntries bt') bt') :
    HasType enumEnv
      (.variant vname ename (buildFlatVariantFields eeEntries enumDef vname activeFields))
      (.tenum ename) := by
  apply HasType.variant vname ename _ ⟨allEnumFieldTypes enumDef⟩
  · -- allEnumQualifiedFieldTypes
    unfold allEnumQualifiedFieldTypes; rw [hlookup_enum]
  · -- domain: fentries → fields
    intro qf hqf
    simp only [AssocMap.lookup] at hqf
    unfold allEnumFieldTypes at hqf
    rw [buildFlatVariantFields_eq_map]
    exact @flatMap_map_lookup_transfer Field BasicMoveType Id EnumVariantDef
      BasicMoveType Value _
      enumDef.variants.entries
      (fun _ vd => vd.fields.entries)
      (fun vn _ f _ => qualifyField vn f)
      (fun _ _ _ bt => bt)
      (fun vn _ f bt => if vn == vname then
        match activeFields.lookup f with | some v => v | none => defaultValue eeEntries bt
        else defaultValue eeEntries bt)
      qf hqf
  · -- domain: fields → fentries
    intro qf hqf
    rw [buildFlatVariantFields_eq_map] at hqf
    simp only [AssocMap.lookup]
    unfold allEnumFieldTypes
    exact @flatMap_map_lookup_transfer Field BasicMoveType Id EnumVariantDef
      Value BasicMoveType _
      enumDef.variants.entries
      (fun _ vd => vd.fields.entries)
      (fun vn _ f _ => qualifyField vn f)
      (fun vn _ f bt => if vn == vname then
        match activeFields.lookup f with | some v => v | none => defaultValue eeEntries bt
        else defaultValue eeEntries bt)
      (fun _ _ _ bt => bt)
      qf hqf
  · -- field typing
    intro qf bt v hqf_bt hqf_v
    simp only [AssocMap.lookup] at hqf_bt
    unfold allEnumFieldTypes at hqf_bt
    rw [buildFlatVariantFields_eq_map] at hqf_v
    obtain ⟨vn, vd, f, bt', hvn_mem, hf_mem, hqf_eq, hbt_eq, hv_eq⟩ :=
      @flatMap_map_lookup_pair Field BasicMoveType Id EnumVariantDef
        BasicMoveType Value _ _
        enumDef.variants.entries
        (fun _ vd => vd.fields.entries)
        (fun vn _ f _ => qualifyField vn f)
        (fun _ _ _ bt => bt)
        (fun vn _ f bt => if vn == vname then
          match activeFields.lookup f with | some v => v | none => defaultValue eeEntries bt
          else defaultValue eeEntries bt)
        qf bt v hqf_bt hqf_v
    subst hbt_eq; subst hv_eq
    by_cases hvn_eq : vn == vname
    · -- Active variant
      simp at hvn_eq; subst hvn_eq
      -- vd = variantDef since variant names are unique
      have hvd_eq : vd = variantDef := by
        have h1 := list_lookup_of_mem_nodup hvn_mem hvariant_nodup
        simp only [AssocMap.lookup] at hlookup_var
        rw [h1] at hlookup_var; exact Option.some.inj hlookup_var
      subst hvd_eq
      cases haf : activeFields.lookup f with
      | some val =>
        simp ; exact htyped f bt val (list_lookup_of_mem_nodup hf_mem hfields_nodup) haf
      | none => grind
    · -- Inactive variant: defaultValue
      simp [hvn_eq]; grind
  · -- enumVariantFields
    unfold enumVariantFields; rw [hlookup_enum]; simp
    rw [hlookup_var]; simp

private theorem preservation_packVariant (m m' : Machine) (env : TypeEnv) (lenv : LabelEnv)
    (retTypes : List ParamType) (rmap : RefMap)
    (hwt : WellTypedState m env lenv retTypes rmap)
    (hss : StackSafe env.enumEnv m.stack m.frame.returnInfo m.heap retTypes)
    (s : Site) (enumName : Id) (variantName : Id)
    (fieldSites : List (Field × Site)) (cont : Stmt)
    (hstmt : m.frame.stmt = .letBind s (.packVariant enumName variantName fieldSites) cont)
    (hstep : step (.running m) = .running m') :
    ∃ env' lenv' retTypes' rmap',
      env'.enumEnv = env.enumEnv ∧ WellTypedState m' env' lenv' retTypes' rmap' ∧
      StackSafe env.enumEnv m'.stack m'.frame.returnInfo m'.heap retTypes' := by
  obtain ⟨enumDef, variantDef, _hnotIn, hlookup_enum, hlookup_var, hfield_map, hcomplete, _hdistinct, hcont⟩ :=
    inv_packVariant (by rw [← hstmt]; exact hwt.stmt_typed)
  simp only [step, hstmt] at hstep
  split at hstep
  · cases hstep
  · rename_i fieldVals hcpf
    split at hstep
    · cases hstep
    · rename_i enumDef' heq_enum
      have heq_ed : enumDef' = enumDef := by
        rw [hwt.enumEnv_consistent] at heq_enum
        simp only [hlookup_enum, Option.some.injEq] at heq_enum; exact heq_enum.symm
      subst heq_ed
      simp only [ExecState.running.injEq] at hstep; subst hstep
      refine ⟨{env with siteEnv := insert (deleteAll env.siteEnv (fieldSites.map Prod.snd)) s
                                      (.basic (.tenum enumName))},
              lenv, retTypes, rmap, rfl, ?_, hss⟩
      exact {
      env_wf := TypeEnv.deleteAll_insert_wf env (fieldSites.map Prod.snd) s
                  (.basic (.tenum enumName)) hwt.env_wf trivial
      enumEnv_consistent := hwt.enumEnv_consistent
      enum_qualified_nodup := hwt.enum_qualified_nodup
      enum_names_nodup := hwt.enum_names_nodup
      enum_variant_nodup := hwt.enum_variant_nodup
      enum_fields_nodup := hwt.enum_fields_nodup
      defaultValues_typed := hwt.defaultValues_typed
      stmt_typed := hcont
      var_consistent := hwt.var_consistent
      site_consistent := by
        intro s' τ' hl
        by_cases heq : s' = s
        · subst heq; simp only [lookup_insert_same, Option.some.injEq] at hl; subst hl
          refine ⟨_, lookup_insert_same _ _ _, ?_⟩
          simp only [ValueMatchesType]
          apply buildFlatVariantFields_HasType m.enumEnv.entries fieldVals
            (hwt.enumEnv_consistent ▸ hlookup_enum) hlookup_var
            (hwt.enum_variant_nodup enumName enumDef'
              (hwt.enumEnv_consistent ▸ hlookup_enum))
            (hwt.enum_fields_nodup enumName enumDef' variantName variantDef
              (hwt.enumEnv_consistent ▸ hlookup_enum)
              (lookup_some _ _ _ hlookup_var))
          · -- Active fields are typed: from site_consistent + hfield_map + collectPackFields
            intro f bt v hbt_lookup haf_lookup
            obtain ⟨a, ha_mem, ha_val⟩ := collectPackFields_lookup_inv
              m.frame.siteStore fieldSites fieldVals hcpf f v haf_lookup
            obtain ⟨bt', henv_a, hfields_f⟩ := hfield_map f a ha_mem
            rw [hbt_lookup] at hfields_f
            simp only [Option.some.injEq] at hfields_f; subst hfields_f
            obtain ⟨v', hv'_store, hv'_typed⟩ := hwt.site_consistent a (.basic bt) henv_a
            simp only [ValueMatchesType] at hv'_typed
            rw [ha_val] at hv'_store
            simp only [Option.some.injEq] at hv'_store; subst hv'_store
            exact hv'_typed
          · -- Default values are typed
            intro vn' vd' f' bt' hvn' hf'
            exact hwt.defaultValues_typed enumName enumDef' vn' vd' f' bt'
              (hwt.enumEnv_consistent ▸ hlookup_enum) hvn' hf'
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
      funEnv_sig_consistent := hwt.funEnv_sig_consistent
      refs_tracked_mapped := hwt.refs_tracked_mapped
      lenv_labels_in_blocks := hwt.lenv_labels_in_blocks
      has_return_info := hwt.has_return_info
      varStore_locs_bound := hwt.varStore_locs_bound
    }

-- Helper: List.lookup success implies membership
private lemma list_lookup_mem_pair {α : Type} [BEq α] [LawfulBEq α] {β : Type}
    (l : List (α × β)) (k : α) (v : β) (h : l.lookup k = some v) : (k, v) ∈ l := by
  induction l with
  | nil => simp [List.lookup] at h
  | cons p rest ih =>
    obtain ⟨k', v'⟩ := p
    simp only [List.lookup] at h
    split at h
    · rename_i hk; rw [beq_iff_eq] at hk; subst hk
      injection h with h; subst h; exact .head _
    · exact List.mem_cons_of_mem _ (ih h)

-- Helper: extract field value + typing from HasType variant (qualified field version)
private theorem HasType_variant_field_typed
    {enumEnv : EnumEnv}
    {vname : Id} {fields : List (Field × Value)}
    {ename : Id}
    {fentries : AssocMap Field BasicMoveType} {f : Field} {bt : BasicMoveType}
    (hht : HasType enumEnv (.variant vname ename fields) (.tenum ename))
    (haqf : allEnumQualifiedFieldTypes enumEnv ename = some fentries)
    (hlookup_f : lookup fentries f = some bt) :
    ∃ vf, fields.lookup f = some vf ∧ HasType enumEnv vf bt := by
  cases hht with
  | variant _ _ _ fentries' haqf' hexists_fwd _ htyped _ =>
    have hfe_eq : fentries = fentries' := Option.some.inj (haqf.symm.trans haqf')
    subst hfe_eq
    have hne : fields.lookup f ≠ none := hexists_fwd f (by rw [hlookup_f]; simp)
    cases hfl : fields.lookup f with
    | none => exact absurd hfl hne
    | some vf => exact ⟨vf, rfl, htyped f bt vf hlookup_f hfl⟩

-- ============================================================
-- Ref variant unpack: siteStore fold helpers
-- ============================================================

/-- For a site NOT in the field list, the ref unpack siteStore fold doesn't change its lookup. -/
private theorem ref_unpack_foldl_lookup_not_in_fields
    (qualify : Field → Field)
    (loc : Loc) (pathR : List Field) (siteStore : AssocMap Site Value)
    (fields : List (Field × Site)) (a : Site)
    (hnotin : a ∉ fields.map Prod.snd) :
    lookup (fields.foldl (fun ss (fa : Field × Site) =>
      AssocMap.insert ss fa.2 (.ref loc (pathR ++ [qualify fa.1]))) siteStore) a = lookup siteStore a := by
  induction fields generalizing siteStore with
  | nil => simp [List.foldl]
  | cons hd tl ih =>
    obtain ⟨f, s⟩ := hd
    simp only [List.map, List.mem_cons, not_or] at hnotin
    obtain ⟨hne, hnotin_tl⟩ := hnotin
    simp only [List.foldl]
    rw [ih _ hnotin_tl]
    exact lookup_insert_ne siteStore s a _ hne

/-- For a site (f, a) IN the field list (with unique site), the ref unpack siteStore fold gives
    the expected ref value. -/
private theorem ref_unpack_foldl_lookup_mem
    (qualify : Field → Field)
    (loc : Loc) (pathR : List Field) (siteStore : AssocMap Site Value)
    (fields : List (Field × Site)) (f : Field) (a : Site)
    (hmem : (f, a) ∈ fields)
    (huniq : ∀ f', (f', a) ∈ fields → f' = f) :
    lookup (fields.foldl (fun ss (fa : Field × Site) =>
      AssocMap.insert ss fa.2 (.ref loc (pathR ++ [qualify fa.1]))) siteStore) a =
    some (.ref loc (pathR ++ [qualify f])) := by
  induction fields generalizing siteStore with
  | nil => nomatch hmem
  | cons hd tl ih =>
    obtain ⟨f', s⟩ := hd
    simp only [List.foldl]
    simp only [List.mem_cons, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | hmem_tl
    · -- head is (f, a)
      by_cases ha_tl : a ∈ tl.map Prod.snd
      · obtain ⟨⟨f'', _⟩, hmem_tl', heq⟩ := List.mem_map.mp ha_tl
        simp at heq; subst heq
        have hf'' : f'' = f := huniq f'' (List.mem_cons_of_mem _ hmem_tl')
        subst hf''
        exact ih _ hmem_tl' (fun f''' hf''' => huniq f''' (List.mem_cons_of_mem _ hf'''))
      · rw [ref_unpack_foldl_lookup_not_in_fields _ _ _ _ _ _ ha_tl]
        exact lookup_insert_same siteStore a _
    · have huniq_tl : ∀ f', (f', a) ∈ tl → f' = f :=
        fun f' hf' => huniq f' (List.mem_cons_of_mem _ hf')
      exact ih _ hmem_tl huniq_tl

/-- For a site NOT in the field list, addRefFieldSites doesn't change its siteEnv lookup. -/
private theorem addRefFieldSites_lookup_not_in_fields (r : Aref) (bk : BorrowingKind)
    (fentries : AssocMap Field BasicMoveType) (qualify : Field → Field) (fields : List (Field × Site)) (env : TypeEnv)
    (s : Site) (hnotin : s ∉ fields.map Prod.snd) :
    lookup (addRefFieldSites r bk fentries qualify fields env).siteEnv s = lookup env.siteEnv s := by
  unfold addRefFieldSites
  induction fields generalizing env with
  | nil => rfl
  | cons hd rest ih =>
    obtain ⟨f', s'⟩ := hd
    simp only [List.map, List.mem_cons, not_or] at hnotin
    obtain ⟨hne, hnotin_tl⟩ := hnotin
    simp only [List.foldl]
    cases hlook : lookup fentries f' with
    | none => exact ih env hnotin_tl
    | some bt =>
      rw [ih _ hnotin_tl]
      exact lookup_insert_ne _ s' s _ hne

-- ============================================================
-- Paired fold: builds env + rmap for ref variant unpack
-- ============================================================

/-- Paired fold that builds both the TypeEnv and RefMap simultaneously.
    The env component matches addRefFieldSites, and the rmap component
    maps each fresh ref to the corresponding heap location. -/
private def buildRefFieldEnvRmap (r : Aref) (bk : BorrowingKind)
    (fentries : AssocMap Field BasicMoveType)
    (qualify : Field → Field)
    (loc : Loc) (pathR : List Field) (fields : List (Field × Site))
    (env : TypeEnv) (rmap : RefMap) : TypeEnv × RefMap :=
  fields.foldl (fun (acc : TypeEnv × RefMap) (f_s : Field × Site) =>
    match lookup fentries f_s.1 with
    | some bt =>
      let rf := nextFreshRefInEnv acc.1
      ({acc.1 with siteEnv := insert acc.1.siteEnv f_s.2 (.ref bt rf bk),
                   pathEnv := update_with_extension rf r [.field (qualify f_s.1)] acc.1.pathEnv},
       { map := fun r' => if r' = rf then some (loc, pathR ++ [qualify f_s.1]) else acc.2.map r' })
    | none => acc) (env, rmap)

/-- The env component of buildRefFieldEnvRmap equals addRefFieldSites. -/
private theorem buildRefFieldEnvRmap_fst_eq (r : Aref) (bk : BorrowingKind)
    (fentries : AssocMap Field BasicMoveType)
    (qualify : Field → Field)
    (loc : Loc) (pathR : List Field)
    (fields : List (Field × Site)) (env : TypeEnv) (rmap : RefMap) :
    (buildRefFieldEnvRmap r bk fentries qualify loc pathR fields env rmap).1 =
    addRefFieldSites r bk fentries qualify fields env := by
  unfold buildRefFieldEnvRmap addRefFieldSites
  induction fields generalizing env rmap with
  | nil => rfl
  | cons hd rest ih =>
    simp only [List.foldl]
    cases lookup fentries hd.1 with
    | none => exact ih env rmap
    | some bt => exact ih _ _

/-- The rmap component preserves old mappings for refs that are not fresh. -/
private theorem buildRefFieldEnvRmap_old_ref (r_old : Aref) (r : Aref) (bk : BorrowingKind)
    (fentries : AssocMap Field BasicMoveType)
    (qualify : Field → Field)
    (loc : Loc) (pathR : List Field)
    (fields : List (Field × Site)) (env : TypeEnv) (rmap : RefMap)
    (h_old : r_old ∈ env.pathEnv.refs) :
    (buildRefFieldEnvRmap r bk fentries qualify loc pathR fields env rmap).2.map r_old = rmap.map r_old := by
  unfold buildRefFieldEnvRmap
  induction fields generalizing env rmap with
  | nil => rfl
  | cons hd rest ih =>
    simp only [List.foldl]
    cases hlook : lookup fentries hd.1 with
    | none => exact ih env rmap h_old
    | some bt =>
      have hfresh := nextFreshRefInEnv_not_in_pathEnv env
      have hne : r_old ≠ nextFreshRefInEnv env := fun h => hfresh (h ▸ h_old)
      dsimp only
      have hmem : r_old ∈ (update_with_extension (nextFreshRefInEnv env) r
          [.field (qualify hd.1)] env.pathEnv).refs := by
        simp only [update_with_extension, show (nextFreshRefInEnv env ∈ env.pathEnv.refs) = False
          from propext ⟨hfresh, False.elim⟩, not_false_eq_true, ↓reduceIte]
        exact List.mem_cons_of_mem _ h_old
      rw [ih _ _ hmem]
      simp only [if_neg hne]

/-- If r' is tracked in the result env and the rmap mapping is unchanged (hold case),
    then r' was already tracked in the original env. -/
private theorem buildRefFieldEnvRmap_map_cases_tracked (r : Aref) (bk : BorrowingKind)
    (fentries : AssocMap Field BasicMoveType)
    (qualify : Field → Field)
    (loc : Loc) (pathR : List Field)
    (fields : List (Field × Site)) (env : TypeEnv) (rmap : RefMap) (r' : Aref)
    (hmem : r' ∈ (buildRefFieldEnvRmap r bk fentries qualify loc pathR fields env rmap).1.pathEnv.refs) :
    (r' ∈ env.pathEnv.refs ∧
      (buildRefFieldEnvRmap r bk fentries qualify loc pathR fields env rmap).2.map r' = rmap.map r') ∨
    (∃ f bt, lookup fentries f = some bt ∧
      (buildRefFieldEnvRmap r bk fentries qualify loc pathR fields env rmap).2.map r' =
      some (loc, pathR ++ [qualify f])) := by
  unfold buildRefFieldEnvRmap at hmem ⊢
  induction fields generalizing env rmap with
  | nil => exact Or.inl ⟨hmem, rfl⟩
  | cons hd rest ih =>
    simp only [List.foldl] at hmem ⊢
    cases hlook : lookup fentries hd.1 with
    | none =>
      simp only [hlook] at hmem ⊢
      exact ih env rmap hmem
    | some bt =>
      simp only [hlook] at hmem ⊢
      have hfresh := nextFreshRefInEnv_not_in_pathEnv env
      let inner_env : TypeEnv :=
        {env with siteEnv := insert env.siteEnv hd.2 (.ref bt (nextFreshRefInEnv env) bk),
                  pathEnv := update_with_extension (nextFreshRefInEnv env) r [.field (qualify hd.1)] env.pathEnv}
      let inner_rmap : RefMap :=
        { map := fun r'' => if r'' = nextFreshRefInEnv env then some (loc, pathR ++ [qualify hd.1]) else rmap.map r'' }
      rcases ih inner_env inner_rmap hmem with ⟨hmem_inner, hhold⟩ | ⟨f, bt_f, hf_lookup, hf_map⟩
      · -- Hold case from IH: r' ∈ inner_env.pathEnv.refs and rmap unchanged through rest
        simp only [inner_env, update_with_extension,
          show (nextFreshRefInEnv env ∈ env.pathEnv.refs) = False
            from propext ⟨hfresh, False.elim⟩,
          not_false_eq_true, ↓reduceIte] at hmem_inner
        rcases List.mem_cons.mp hmem_inner with heq | hmem_old
        · -- r' = nextFreshRefInEnv env → maps to field path (right case)
          right
          exact ⟨hd.1, bt, hlook, by simp only [inner_rmap] at hhold; simp [heq] at hhold ⊢; exact hhold⟩
        · -- r' ∈ env.pathEnv.refs → hold case
          left
          refine ⟨hmem_old, ?_⟩
          simp only [inner_rmap] at hhold
          have hne : r' ≠ nextFreshRefInEnv env := fun h => hfresh (h ▸ hmem_old)
          simp [if_neg hne] at hhold
          exact hhold
      · -- Right case from IH: maps to field path
        exact Or.inr ⟨f, bt_f, hf_lookup, hf_map⟩

/-- Root is not mapped by the extended rmap. -/
private theorem buildRefFieldEnvRmap_root_none (r : Aref) (bk : BorrowingKind)
    (fentries : AssocMap Field BasicMoveType)
    (qualify : Field → Field)
    (loc : Loc) (pathR : List Field)
    (fields : List (Field × Site)) (env : TypeEnv) (rmap : RefMap)
    (hroot_in : Aref.root ∈ env.pathEnv.refs)
    (hroot_none : rmap.map .root = none) :
    (buildRefFieldEnvRmap r bk fentries qualify loc pathR fields env rmap).2.map .root = none := by
  rw [buildRefFieldEnvRmap_old_ref .root r bk fentries qualify loc pathR fields env rmap hroot_in]
  exact hroot_none

/-- For any ref r', the extended rmap either preserves the old mapping or maps to a field path
    with a known type in fentries. -/
private theorem buildRefFieldEnvRmap_map_cases (r : Aref) (bk : BorrowingKind)
    (fentries : AssocMap Field BasicMoveType)
    (qualify : Field → Field)
    (loc : Loc) (pathR : List Field)
    (fields : List (Field × Site)) (env : TypeEnv) (rmap : RefMap)
    (r' : Aref) :
    (buildRefFieldEnvRmap r bk fentries qualify loc pathR fields env rmap).2.map r' = rmap.map r' ∨
    (∃ f bt, lookup fentries f = some bt ∧
      (buildRefFieldEnvRmap r bk fentries qualify loc pathR fields env rmap).2.map r' =
      some (loc, pathR ++ [qualify f])) := by
  unfold buildRefFieldEnvRmap
  induction fields generalizing env rmap with
  | nil => exact Or.inl rfl
  | cons hd rest ih =>
    simp only [List.foldl]
    cases hlook : lookup fentries hd.1 with
    | none => exact ih env rmap
    | some bt =>
      rcases ih
        {env with siteEnv := insert env.siteEnv hd.2 (.ref bt (nextFreshRefInEnv env) bk),
                  pathEnv := update_with_extension (nextFreshRefInEnv env) r [.field (qualify hd.1)] env.pathEnv}
        { map := fun r'' => if r'' = nextFreshRefInEnv env then some (loc, pathR ++ [qualify hd.1]) else rmap.map r'' }
        with hold | ⟨f, hf⟩
      · -- Maps to inner rmap's value
        rw [hold]
        by_cases heq : r' = nextFreshRefInEnv env
        · right; exact ⟨hd.1, bt, hlook, by simp [heq]⟩
        · left; simp [heq]
      · exact Or.inr ⟨f, hf⟩

/-- For a field site (f, s) in the list, addRefFieldSites gives a ref entry with a fresh aref,
    and buildRefFieldEnvRmap maps that aref to the corresponding heap location. -/
private theorem buildRefFieldEnvRmap_field_consistent (r : Aref) (bk : BorrowingKind)
    (fentries : AssocMap Field BasicMoveType)
    (qualify : Field → Field)
    (loc : Loc) (pathR : List Field)
    (fields : List (Field × Site)) (env : TypeEnv) (rmap : RefMap)
    (f : Field) (s : Site) (hmem : (f, s) ∈ fields) (bt : BasicMoveType)
    (hbt : lookup fentries f = some bt)
    (huniq : ∀ f', (f', s) ∈ fields → f' = f) :
    ∃ rf,
      lookup (addRefFieldSites r bk fentries qualify fields env).siteEnv s = some (.ref bt rf bk) ∧
      (buildRefFieldEnvRmap r bk fentries qualify loc pathR fields env rmap).2.map rf = some (loc, pathR ++ [qualify f]) := by
  unfold addRefFieldSites buildRefFieldEnvRmap
  induction fields generalizing env rmap with
  | nil => nomatch hmem
  | cons hd rest ih =>
    obtain ⟨f', s'⟩ := hd
    simp only [List.foldl]
    simp only [List.mem_cons, Prod.mk.injEq] at hmem
    rcases hmem with ⟨rfl, rfl⟩ | hmem_tl
    · -- head is (f, s)
      rw [hbt]; simp only
      by_cases hs_tl : s ∈ rest.map Prod.snd
      · obtain ⟨⟨f'', _⟩, hmem_tl', heq⟩ := List.mem_map.mp hs_tl
        simp at heq; subst heq
        have hf'' : f'' = f := huniq f'' (List.mem_cons_of_mem _ hmem_tl')
        subst hf''
        exact ih _ _ hmem_tl' (fun f''' hf''' => huniq f''' (List.mem_cons_of_mem _ hf'''))
      · have hlookup_eq := addRefFieldSites_lookup_not_in_fields r bk fentries qualify rest
            {env with siteEnv := insert env.siteEnv s (.ref bt (nextFreshRefInEnv env) bk),
                      pathEnv := update_with_extension (nextFreshRefInEnv env) r [.field (qualify f)] env.pathEnv}
            s hs_tl
        unfold addRefFieldSites at hlookup_eq
        simp at hlookup_eq
        rw [hlookup_eq, lookup_insert_same]
        refine ⟨nextFreshRefInEnv env, rfl, ?_⟩
        have hfresh := nextFreshRefInEnv_not_in_pathEnv env
        have hmem_pe : nextFreshRefInEnv env ∈
            (update_with_extension (nextFreshRefInEnv env) r [.field (qualify f)] env.pathEnv).refs := by
          simp only [update_with_extension, show (nextFreshRefInEnv env ∈ env.pathEnv.refs) = False
            from propext ⟨hfresh, False.elim⟩, not_false_eq_true, ↓reduceIte]
          exact .head _
        let env' : TypeEnv :=
          {env with siteEnv := insert env.siteEnv s (.ref bt (nextFreshRefInEnv env) bk),
                    pathEnv := update_with_extension (nextFreshRefInEnv env) r [.field (qualify f)] env.pathEnv}
        let rmap' : RefMap :=
          { map := fun r' => if r' = nextFreshRefInEnv env then some (loc, pathR ++ [qualify f]) else rmap.map r' }
        show (buildRefFieldEnvRmap r bk fentries qualify loc pathR rest env' rmap').2.map (nextFreshRefInEnv env) =
          some (loc, pathR ++ [qualify f])
        rw [buildRefFieldEnvRmap_old_ref (nextFreshRefInEnv env) r bk fentries qualify loc pathR rest env' rmap' hmem_pe]
        show (if nextFreshRefInEnv env = nextFreshRefInEnv env then some (loc, pathR ++ [qualify f]) else rmap.map (nextFreshRefInEnv env)) = some (loc, pathR ++ [qualify f])
        rw [if_pos rfl]
    · -- tail case
      have huniq_tl : ∀ f', (f', s) ∈ rest → f' = f :=
        fun f' hf' => huniq f' (List.mem_cons_of_mem _ hf')
      cases hlook : lookup fentries f' with
      | none => exact ih env rmap hmem_tl huniq_tl
      | some bt' => exact ih _ _ hmem_tl huniq_tl

/-- no_paths_to_root is preserved by update_with_extension when both z ≠ root and x ≠ root. -/
private theorem no_paths_to_root_uwe (z x : Aref) (p : Path) (pe : PathEnv)
    (hz_ne_root : z ≠ .root) (hx_ne_root : x ≠ .root)
    (h : ∀ u path, interpret_regex (pe.paths (u, .root)) path → u = .root ∧ path = []) :
    ∀ u path, interpret_regex ((update_with_extension z x p pe).paths (u, .root)) path →
    u = .root ∧ path = [] := by
  have hroot_ne_z : ¬(.root = z) := Ne.symm hz_ne_root
  intro u path hinterp
  simp only [update_with_extension] at hinterp
  by_cases huz : u = z
  · -- u = z ≠ .root: paths(z, .root) = der (G(x, .root)) p
    subst huz
    simp only [hroot_ne_z, and_false, ite_false, ite_true] at hinterp
    -- G(x, .root) matches nothing (x ≠ .root), so der also matches nothing
    have hno_match : ∀ q, ¬interpret_regex (pe.paths (x, .root)) q := by
      intro q hq; exact hx_ne_root (h x q hq).1
    exact absurd hinterp (no_match_der p hno_match path)
  · -- u ≠ z, .root ≠ z: paths unchanged
    simp only [huz, hroot_ne_z, false_and, ite_false] at hinterp
    exact h u path hinterp

/-- no_paths_to_root is preserved by addRefFieldSites when the parent ref is not root. -/
private theorem addRefFieldSites_no_paths_to_root (r : Aref) (bk : BorrowingKind)
    (fentries : AssocMap Field BasicMoveType) (qualify : Field → Field) (fields : List (Field × Site)) (env : TypeEnv)
    (hr_ne_root : r ≠ .root)
    (hroot_in : Aref.root ∈ env.pathEnv.refs)
    (h : ∀ u p, interpret_regex (env.pathEnv.paths (u, .root)) p → u = .root ∧ p = []) :
    ∀ u p, interpret_regex ((addRefFieldSites r bk fentries qualify fields env).pathEnv.paths (u, .root)) p →
    u = .root ∧ p = [] := by
  unfold addRefFieldSites
  induction fields generalizing env with
  | nil => exact h
  | cons hd rest ih =>
    simp only [List.foldl]
    cases hlook : lookup fentries hd.1 with
    | none => exact ih env hroot_in h
    | some bt =>
      have hfresh := nextFreshRefInEnv_not_in_pathEnv env
      have hz_ne_root : nextFreshRefInEnv env ≠ .root := fun heq => hfresh (heq ▸ hroot_in)
      have hroot_in' : Aref.root ∈ (update_with_extension (nextFreshRefInEnv env) r
          [.field (qualify hd.1)] env.pathEnv).refs := by
        simp only [update_with_extension, show (nextFreshRefInEnv env ∈ env.pathEnv.refs) = False
          from propext ⟨hfresh, False.elim⟩, not_false_eq_true, ↓reduceIte]
        exact .tail _ hroot_in
      apply ih _ hroot_in'
      exact no_paths_to_root_uwe _ r _ _ hz_ne_root hr_ne_root h

/-- For old refs (both in env.pathEnv.refs), paths are unchanged by addRefFieldSites. -/
private theorem addRefFieldSites_old_paths_eq (r : Aref) (bk : BorrowingKind)
    (fentries : AssocMap Field BasicMoveType) (qualify : Field → Field) (fields : List (Field × Site)) (env : TypeEnv)
    (r1 r2 : Aref) (hr1 : r1 ∈ env.pathEnv.refs) (hr2 : r2 ∈ env.pathEnv.refs) :
    (addRefFieldSites r bk fentries qualify fields env).pathEnv.paths (r1, r2) =
    env.pathEnv.paths (r1, r2) := by
  unfold addRefFieldSites
  induction fields generalizing env with
  | nil => rfl
  | cons hd rest ih =>
    simp only [List.foldl]
    cases hlook : lookup fentries hd.1 with
    | none => exact ih env hr1 hr2
    | some bt =>
      have hfresh := nextFreshRefInEnv_not_in_pathEnv env
      have hr1_ne : r1 ≠ nextFreshRefInEnv env := fun h => hfresh (h ▸ hr1)
      have hr2_ne : r2 ≠ nextFreshRefInEnv env := fun h => hfresh (h ▸ hr2)
      have hr1' : r1 ∈ (update_with_extension (nextFreshRefInEnv env) r
          [.field (qualify hd.1)] env.pathEnv).refs := by
        show r1 ∈ (update_with_extension (nextFreshRefInEnv env) r
            [.field (qualify hd.1)] env.pathEnv).refs
        unfold update_with_extension
        simp only [hfresh, not_false_eq_true, ↓reduceIte]
        exact List.mem_cons_of_mem _ hr1
      have hr2' : r2 ∈ (update_with_extension (nextFreshRefInEnv env) r
          [.field (qualify hd.1)] env.pathEnv).refs := by
        show r2 ∈ (update_with_extension (nextFreshRefInEnv env) r
            [.field (qualify hd.1)] env.pathEnv).refs
        unfold update_with_extension
        simp only [hfresh, not_false_eq_true, ↓reduceIte]
        exact List.mem_cons_of_mem _ hr2
      have hstep : (update_with_extension (nextFreshRefInEnv env) r [.field (qualify hd.1)]
          env.pathEnv).paths (r1, r2) = env.pathEnv.paths (r1, r2) := by
        unfold update_with_extension
        simp only [hr1_ne, hr2_ne, false_and, ite_false]
      rw [ih _ hr1' hr2', hstep]

/-- self_loop_only_empty is preserved by update_with_extension (local copy of private lemma) -/
private lemma self_loop_only_empty_uwe' (z x : Aref) (p : Path) (pe : PathEnv)
    (h : ∀ u path, interpret_regex (pe.paths (u, u)) path → path = []) :
    ∀ u path, interpret_regex ((update_with_extension z x p pe).paths (u, u)) path → path = [] := by
  intro u path hinterp
  simp only [update_with_extension] at hinterp
  by_cases huz : u = z
  · subst huz; simp only [and_self, ↓reduceIte, interpret_regex] at hinterp; exact hinterp
  · simp only [show (u = z) = False from propext ⟨huz, False.elim⟩,
               false_and, ite_false] at hinterp
    exact h u path hinterp

/-- root_path_coherence is preserved by addRefFieldSites/buildRefFieldEnvRmap. -/
private theorem addRefFieldSites_root_path_coherence (r : Aref) (bk : BorrowingKind)
    (fentries : AssocMap Field BasicMoveType)
    (qualify : Field → Field)
    (loc : Loc) (pathR : List Field)
    (fields : List (Field × Site)) (env : TypeEnv) (rmap : RefMap)
    (_ : Heap) (varStore : AssocMap Var (Option Loc))
    (hr_mem : r ∈ env.pathEnv.refs)
    (hrmap_r : rmap.map r = some (loc, pathR))
    (hold : ∀ v y rest, v ∈ env.pathEnv.refs →
      interpret_regex (env.pathEnv.paths (.root, v)) (.root_to_var y :: rest) →
      ∀ loc_v path_v, rmap.map v = some (loc_v, path_v) →
      ∀ loc_y, lookup varStore y = some (some loc_y) →
      loc_v = loc_y → path_v = fieldPathOf rest)
    (hself : ∀ u p, interpret_regex (env.pathEnv.paths (u, u)) p → p = [])
    (hpaths_to_nm : ∀ u v p, v ∉ env.pathEnv.refs → v ≠ .root → u ≠ v →
      ¬interpret_regex (env.pathEnv.paths (u, v)) p)
    (hrmap_root_none : rmap.map .root = none)
    (hroot_in : Aref.root ∈ env.pathEnv.refs)
    (hrefs_tracked : ∀ r', r' ∈ env.pathEnv.refs → r' = .root ∨ rmap.map r' ≠ none) :
    ∀ v y rest, v ∈ (addRefFieldSites r bk fentries qualify fields env).pathEnv.refs →
      interpret_regex ((addRefFieldSites r bk fentries qualify fields env).pathEnv.paths (.root, v))
        (.root_to_var y :: rest) →
      ∀ loc_v path_v, (buildRefFieldEnvRmap r bk fentries qualify loc pathR fields env rmap).2.map v =
        some (loc_v, path_v) →
      ∀ loc_y, lookup varStore y = some (some loc_y) →
      loc_v = loc_y → path_v = fieldPathOf rest := by
  induction fields generalizing env rmap with
  | nil => exact hold
  | cons hd rest ih =>
    cases hlook : lookup fentries hd.1 with
    | none =>
      have hstep_a : addRefFieldSites r bk fentries qualify (hd :: rest) env =
          addRefFieldSites r bk fentries qualify rest env := by
        unfold addRefFieldSites; simp only [List.foldl, hlook]
      have hstep_b : buildRefFieldEnvRmap r bk fentries qualify loc pathR (hd :: rest) env rmap =
          buildRefFieldEnvRmap r bk fentries qualify loc pathR rest env rmap := by
        unfold buildRefFieldEnvRmap; simp only [List.foldl, hlook]
      rw [hstep_a, hstep_b]
      exact ih env rmap hr_mem hrmap_r hold hself hpaths_to_nm hrmap_root_none hroot_in hrefs_tracked
    | some bt =>
      have hfresh := nextFreshRefInEnv_not_in_pathEnv env
      have hz_ne_root : nextFreshRefInEnv env ≠ .root :=
        fun heq => hfresh (heq ▸ hroot_in)
      have hroot_ne_z : ¬(.root = nextFreshRefInEnv env) := Ne.symm hz_ne_root
      have hr_ne_z : r ≠ nextFreshRefInEnv env := fun h => hfresh (h ▸ hr_mem)
      -- Step equalities with inline structs
      have hstep_a : addRefFieldSites r bk fentries qualify (hd :: rest) env =
          addRefFieldSites r bk fentries qualify rest
            {env with siteEnv := insert env.siteEnv hd.2 (.ref bt (nextFreshRefInEnv env) bk),
                      pathEnv := update_with_extension (nextFreshRefInEnv env) r [.field (qualify hd.1)] env.pathEnv} := by
        unfold addRefFieldSites; simp only [List.foldl, hlook]
      have hstep_b : buildRefFieldEnvRmap r bk fentries qualify loc pathR (hd :: rest) env rmap =
          buildRefFieldEnvRmap r bk fentries qualify loc pathR rest
            {env with siteEnv := insert env.siteEnv hd.2 (.ref bt (nextFreshRefInEnv env) bk),
                      pathEnv := update_with_extension (nextFreshRefInEnv env) r [.field (qualify hd.1)] env.pathEnv}
            { map := fun r'' => if r'' = nextFreshRefInEnv env then some (loc, pathR ++ [qualify hd.1]) else rmap.map r'' } := by
        unfold buildRefFieldEnvRmap; simp only [List.foldl, hlook]
      rw [hstep_a, hstep_b]
      -- Apply IH with stepped env and rmap
      have hr_mem' : r ∈ (update_with_extension (nextFreshRefInEnv env) r [.field (qualify hd.1)]
          env.pathEnv).refs := by
        unfold update_with_extension; simp only [hfresh, not_false_eq_true, ↓reduceIte]
        exact List.mem_cons_of_mem _ hr_mem
      have hroot_in' : Aref.root ∈ (update_with_extension (nextFreshRefInEnv env) r [.field (qualify hd.1)]
          env.pathEnv).refs := by
        unfold update_with_extension; simp only [hfresh, not_false_eq_true, ↓reduceIte]
        exact List.mem_cons_of_mem _ hroot_in
      have hrefs_eq : (update_with_extension (nextFreshRefInEnv env) r [.field (qualify hd.1)]
          env.pathEnv).refs = nextFreshRefInEnv env :: env.pathEnv.refs := by
        unfold update_with_extension; simp only [hfresh, not_false_eq_true, ↓reduceIte]
      refine ih _ _ hr_mem' ?_ ?_ ?_ ?_ ?_ hroot_in' ?_
      · -- rmap_step.map r = some (loc, pathR)
        show (if r = nextFreshRefInEnv env then _ else _) = _
        simp [hr_ne_z, hrmap_r]
      · -- root_path_coherence for stepped env/rmap
        intro v y' rest' hv_mem' hp' loc_v path_v hrmap_v loc_y hloc heq
        rw [hrefs_eq] at hv_mem'
        simp only [List.mem_cons] at hv_mem'
        rcases hv_mem' with hv_eq | hv_old
        · -- v = nextFreshRefInEnv env (fresh ref)
          subst hv_eq
          -- paths(.root, z) in the updated pathEnv
          have hp_uwe : interpret_regex ((update_with_extension (nextFreshRefInEnv env) r
              [.field (qualify hd.1)] env.pathEnv).paths (.root, nextFreshRefInEnv env))
              (.root_to_var y' :: rest') := hp'
          simp only [update_with_extension, hroot_ne_z, false_and, ite_false, ite_true] at hp_uwe
          simp only [extend, List.foldl, interpret_regex] at hp_uwe
          obtain ⟨s1, s2, heq_p, hinterp, hs2_eq⟩ := hp_uwe
          subst hs2_eq
          -- rmap_step maps z to (loc, pathR ++ [qualify hd.1])
          show path_v = fieldPathOf rest'
          simp only at hrmap_v
          obtain ⟨h1, h2⟩ := Prod.mk.inj (Option.some.inj hrmap_v)
          subst h1; subst h2
          -- Decompose: .root_to_var y' :: rest' = s1 ++ [.field (qualify hd.1)]
          cases hs1 : s1 with
          | nil => rw [hs1] at heq_p; simp at heq_p
          | cons s1_hd s1_tl =>
            rw [hs1] at heq_p hinterp
            simp only [List.cons_append, List.cons.injEq] at heq_p
            obtain ⟨hhd_eq, hrest_eq⟩ := heq_p
            rw [← hhd_eq] at hinterp
            have hrpc := hold r y' s1_tl hr_mem hinterp loc pathR hrmap_r loc_y hloc heq
            rw [hrest_eq]; simp [fieldPathOf_append, fieldPathOf, hrpc]
        · -- v ∈ env.pathEnv.refs (old ref)
          have hv_ne : v ≠ nextFreshRefInEnv env := fun h => hfresh (h ▸ hv_old)
          have hp_uwe : interpret_regex ((update_with_extension (nextFreshRefInEnv env) r
              [.field (qualify hd.1)] env.pathEnv).paths (.root, v))
              (.root_to_var y' :: rest') := hp'
          simp only [update_with_extension, hroot_ne_z, hv_ne, false_and, ite_false] at hp_uwe
          simp only [if_neg hv_ne] at hrmap_v
          exact hold v y' rest' hv_old hp_uwe loc_v path_v hrmap_v loc_y hloc heq
      · -- self_loop_only_empty for stepped env
        exact self_loop_only_empty_uwe' _ r _ _ hself
      · -- paths_to_non_member for stepped env
        intro u v p hv_nm hv_ne_root huv_ne
        have hv_ne_z : v ≠ nextFreshRefInEnv env := by
          intro hvz; subst hvz
          have hmem : nextFreshRefInEnv env ∈
              (update_with_extension (nextFreshRefInEnv env) r [.field (qualify hd.1)] env.pathEnv).refs := by
            rw [hrefs_eq]; exact .head _
          exact hv_nm hmem
        have hv_not_old : v ∉ env.pathEnv.refs := by
          intro hv_in
          have hmem : v ∈
              (update_with_extension (nextFreshRefInEnv env) r [.field (qualify hd.1)] env.pathEnv).refs := by
            rw [hrefs_eq]; exact List.mem_cons_of_mem _ hv_in
          exact hv_nm hmem
        show ¬interpret_regex ((update_with_extension (nextFreshRefInEnv env) r
            [.field (qualify hd.1)] env.pathEnv).paths (u, v)) p
        simp only [update_with_extension, hv_ne_z, and_false, ite_false]
        by_cases hu_z : u = nextFreshRefInEnv env
        · subst hu_z; simp only [ite_true]
          have hr_ne_v : r ≠ v := fun h => hv_not_old (h ▸ hr_mem)
          exact no_match_der _ (fun q hq => hpaths_to_nm r v q hv_not_old hv_ne_root hr_ne_v hq) p
        · simp only [if_neg hu_z]
          exact hpaths_to_nm u v p hv_not_old hv_ne_root huv_ne
      · -- rmap_step root none
        dsimp only; simp [hroot_ne_z, hrmap_root_none]
      · -- refs_tracked for stepped env/rmap
        intro r' hr'_mem
        dsimp only at hr'_mem
        rw [hrefs_eq] at hr'_mem
        simp only [List.mem_cons] at hr'_mem
        rcases hr'_mem with rfl | hr'_old
        · right; dsimp only; simp
        · rcases hrefs_tracked r' hr'_old with rfl | hne
          · exact Or.inl rfl
          · right; dsimp only
            have hr'_ne_z : r' ≠ nextFreshRefInEnv env := fun h => hfresh (h ▸ hr'_old)
            simp [hr'_ne_z, hne]

/-- rmap_paths is preserved by addRefFieldSites/buildRefFieldEnvRmap. -/
private theorem addRefFieldSites_rmap_paths (r : Aref) (bk : BorrowingKind)
    (fentries : AssocMap Field BasicMoveType)
    (qualify : Field → Field)
    (loc : Loc) (pathR : List Field)
    (fields : List (Field × Site)) (env : TypeEnv) (rmap : RefMap)
    (heap : Heap)
    (hr_mem : r ∈ env.pathEnv.refs)
    (hrmap_r : rmap.map r = some (loc, pathR))
    (hold : ∀ r1 r2, r1 ∈ env.pathEnv.refs → r2 ∈ env.pathEnv.refs →
      ∀ p, interpret_regex (env.pathEnv.paths (r1, r2)) p →
      PathReflectedInHeap rmap heap r1 r2 p)
    (hself : ∀ u p, interpret_regex (env.pathEnv.paths (u, u)) p → p = [])
    (hpaths_to_nm : ∀ u v p, v ∉ env.pathEnv.refs → v ≠ .root → u ≠ v →
      ¬interpret_regex (env.pathEnv.paths (u, v)) p)
    (hpaths_from_nm : ∀ u v p, u ∉ env.pathEnv.refs → u ≠ .root → u ≠ v →
      ¬interpret_regex (env.pathEnv.paths (u, v)) p)
    (hrmap_root_none : rmap.map .root = none)
    (hroot_in : Aref.root ∈ env.pathEnv.refs)
    (hrefs_tracked : ∀ r', r' ∈ env.pathEnv.refs → r' = .root ∨ rmap.map r' ≠ none)
    (hreadref_fields : ∀ f, lookup fentries f ≠ none → heap.readRef loc (pathR ++ [qualify f]) ≠ none) :
    ∀ r1 r2, r1 ∈ (addRefFieldSites r bk fentries qualify fields env).pathEnv.refs →
      r2 ∈ (addRefFieldSites r bk fentries qualify fields env).pathEnv.refs →
      ∀ p, interpret_regex ((addRefFieldSites r bk fentries qualify fields env).pathEnv.paths (r1, r2)) p →
      PathReflectedInHeap (buildRefFieldEnvRmap r bk fentries qualify loc pathR fields env rmap).2 heap r1 r2 p := by
  induction fields generalizing env rmap with
  | nil => exact hold
  | cons hd rest ih =>
    cases hlook : lookup fentries hd.1 with
    | none =>
      have hstep_a : addRefFieldSites r bk fentries qualify (hd :: rest) env =
          addRefFieldSites r bk fentries qualify rest env := by
        unfold addRefFieldSites; simp only [List.foldl, hlook]
      have hstep_b : buildRefFieldEnvRmap r bk fentries qualify loc pathR (hd :: rest) env rmap =
          buildRefFieldEnvRmap r bk fentries qualify loc pathR rest env rmap := by
        unfold buildRefFieldEnvRmap; simp only [List.foldl, hlook]
      rw [hstep_a, hstep_b]
      exact ih env rmap hr_mem hrmap_r hold hself hpaths_to_nm hpaths_from_nm hrmap_root_none
        hroot_in hrefs_tracked
    | some bt =>
      have hfresh := nextFreshRefInEnv_not_in_pathEnv env
      have hz_ne_root : nextFreshRefInEnv env ≠ .root :=
        fun heq => hfresh (heq ▸ hroot_in)
      have hroot_ne_z : ¬(.root = nextFreshRefInEnv env) := Ne.symm hz_ne_root
      have hr_ne_z : r ≠ nextFreshRefInEnv env := fun h => hfresh (h ▸ hr_mem)
      -- Step equalities
      have hstep_a : addRefFieldSites r bk fentries qualify (hd :: rest) env =
          addRefFieldSites r bk fentries qualify rest
            {env with siteEnv := insert env.siteEnv hd.2 (.ref bt (nextFreshRefInEnv env) bk),
                      pathEnv := update_with_extension (nextFreshRefInEnv env) r [.field (qualify hd.1)] env.pathEnv} := by
        unfold addRefFieldSites; simp only [List.foldl, hlook]
      have hstep_b : buildRefFieldEnvRmap r bk fentries qualify loc pathR (hd :: rest) env rmap =
          buildRefFieldEnvRmap r bk fentries qualify loc pathR rest
            {env with siteEnv := insert env.siteEnv hd.2 (.ref bt (nextFreshRefInEnv env) bk),
                      pathEnv := update_with_extension (nextFreshRefInEnv env) r [.field (qualify hd.1)] env.pathEnv}
            { map := fun r'' => if r'' = nextFreshRefInEnv env then some (loc, pathR ++ [qualify hd.1]) else rmap.map r'' } := by
        unfold buildRefFieldEnvRmap; simp only [List.foldl, hlook]
      rw [hstep_a, hstep_b]
      have hrefs_eq : (update_with_extension (nextFreshRefInEnv env) r [.field (qualify hd.1)]
          env.pathEnv).refs = nextFreshRefInEnv env :: env.pathEnv.refs := by
        unfold update_with_extension; simp only [hfresh, not_false_eq_true, ↓reduceIte]
      have hr_mem' : r ∈ (update_with_extension (nextFreshRefInEnv env) r [.field (qualify hd.1)]
          env.pathEnv).refs := by rw [hrefs_eq]; exact List.mem_cons_of_mem _ hr_mem
      have hroot_in' : Aref.root ∈ (update_with_extension (nextFreshRefInEnv env) r [.field (qualify hd.1)]
          env.pathEnv).refs := by rw [hrefs_eq]; exact List.mem_cons_of_mem _ hroot_in
      -- readRef for field hd.1
      have hreadref_hd : heap.readRef loc (pathR ++ [qualify hd.1]) ≠ none :=
        hreadref_fields hd.1 (by rw [hlook]; simp)
      refine ih
                ({env with siteEnv := insert env.siteEnv hd.2 (.ref bt (nextFreshRefInEnv env) bk),
                           pathEnv := update_with_extension (nextFreshRefInEnv env) r [.field (qualify hd.1)] env.pathEnv})
                _ hr_mem' ?_ ?_ ?_ ?_ ?_ ?_ hroot_in' ?_
      · -- rmap_step.map r
        dsimp only; simp [hr_ne_z, hrmap_r]
      · -- rmap_paths for stepped env/rmap (one step)
        intro r1 r2 hr1 hr2 p hp
        dsimp only at hr1 hr2
        rw [hrefs_eq] at hr1 hr2
        simp only [List.mem_cons] at hr1 hr2
        rcases hr1 with rfl | hr1_mem <;> rcases hr2 with rfl | hr2_mem
        · -- (z, z): self-loop ε
          simp only [update_with_extension, ↓reduceIte] at hp; subst hp
          unfold PathReflectedInHeap; dsimp only; simp only
          intro _; exact ⟨by simp [fieldPathOf], hreadref_hd⟩
        · -- (z, r2): der(paths(r, r2), [.field (qualify hd.1)])
          have hr2_ne : r2 ≠ nextFreshRefInEnv env := fun h => hfresh (h ▸ hr2_mem)
          simp only [update_with_extension, hr2_ne, ite_false, ite_true] at hp
          simp only [der, List.foldl] at hp
          have hold_p := hold r r2 hr_mem hr2_mem (.field (qualify hd.1) :: p) hp
          unfold PathReflectedInHeap at hold_p ⊢; dsimp only
          simp only [if_neg hr2_ne]
          cases hrmap_r2 : rmap.map r2 with
          | none => simp
          | some lr2 =>
            obtain ⟨loc2, path2⟩ := lr2
            simp only [hrmap_r] at hold_p; rw [hrmap_r2] at hold_p
            intro heq_loc
            obtain ⟨hpath, hlive⟩ := hold_p heq_loc
            refine ⟨?_, hlive⟩
            simp only [fieldPathOf] at hpath
            rw [hpath]; simp [List.append_assoc]
        · -- (r1, z): extend(paths(r1, r), [.field (qualify hd.1)])
          have hr1_ne : r1 ≠ nextFreshRefInEnv env := fun h => hfresh (h ▸ hr1_mem)
          simp only [update_with_extension, hr1_ne, false_and, ite_false, ite_true] at hp
          simp only [extend, List.foldl, interpret_regex] at hp
          obtain ⟨s1, s2, heq_p, hinterp1, hs2_eq⟩ := hp
          subst hs2_eq
          have hold_p := hold r1 r hr1_mem hr_mem s1 hinterp1
          unfold PathReflectedInHeap at hold_p ⊢; dsimp only
          simp only [if_neg hr1_ne]
          cases hrmap_r1 : rmap.map r1 with
          | none => simp
          | some lr1 =>
            obtain ⟨loc1, path1⟩ := lr1
            simp only [hrmap_r] at hold_p; rw [hrmap_r1] at hold_p
            intro heq_loc
            obtain ⟨hpath1, _⟩ := hold_p heq_loc
            constructor
            · rw [heq_p, fieldPathOf_append, hpath1]
              simp [fieldPathOf, List.append_assoc]
            · exact hreadref_hd
        · -- (r1, r2): both old, paths unchanged
          have hr1_ne : r1 ≠ nextFreshRefInEnv env := fun h => hfresh (h ▸ hr1_mem)
          have hr2_ne : r2 ≠ nextFreshRefInEnv env := fun h => hfresh (h ▸ hr2_mem)
          simp only [update_with_extension, hr1_ne, hr2_ne, false_and, ite_false] at hp
          have hold_p := hold r1 r2 hr1_mem hr2_mem p hp
          unfold PathReflectedInHeap at hold_p ⊢; dsimp only
          rw [if_neg hr1_ne, if_neg hr2_ne]
          exact hold_p
      · -- self_loop_only_empty for stepped env
        exact self_loop_only_empty_uwe' _ r _ _ hself
      · -- paths_to_non_member
        intro u v p hv_nm hv_ne_root huv_ne
        have hv_ne_z : v ≠ nextFreshRefInEnv env := by
          intro hvz; subst hvz
          have hmem : nextFreshRefInEnv env ∈
              (update_with_extension (nextFreshRefInEnv env) r [.field (qualify hd.1)] env.pathEnv).refs := by
            rw [hrefs_eq]; exact .head _
          exact hv_nm hmem
        have hv_not_old : v ∉ env.pathEnv.refs := by
          intro hv_in
          have hmem : v ∈
              (update_with_extension (nextFreshRefInEnv env) r [.field (qualify hd.1)] env.pathEnv).refs := by
            rw [hrefs_eq]; exact List.mem_cons_of_mem _ hv_in
          exact hv_nm hmem
        show ¬interpret_regex ((update_with_extension (nextFreshRefInEnv env) r
            [.field (qualify hd.1)] env.pathEnv).paths (u, v)) p
        simp only [update_with_extension, hv_ne_z, and_false, ite_false]
        by_cases hu_z : u = nextFreshRefInEnv env
        · subst hu_z; simp only [ite_true]
          have hr_ne_v : r ≠ v := fun h => hv_not_old (h ▸ hr_mem)
          exact no_match_der _ (fun q hq => hpaths_to_nm r v q hv_not_old hv_ne_root hr_ne_v hq) p
        · simp only [if_neg hu_z]
          exact hpaths_to_nm u v p hv_not_old hv_ne_root huv_ne
      · -- paths_from_non_member
        intro u v p hu_nm hu_ne_root huv_ne
        have hu_ne_z : u ≠ nextFreshRefInEnv env := by
          intro huz; subst huz
          have hmem : nextFreshRefInEnv env ∈
              (update_with_extension (nextFreshRefInEnv env) r [.field (qualify hd.1)] env.pathEnv).refs := by
            rw [hrefs_eq]; exact .head _
          exact hu_nm hmem
        have hu_not_old : u ∉ env.pathEnv.refs := by
          intro hu_in
          have hmem : u ∈
              (update_with_extension (nextFreshRefInEnv env) r [.field (qualify hd.1)] env.pathEnv).refs := by
            rw [hrefs_eq]; exact List.mem_cons_of_mem _ hu_in
          exact hu_nm hmem
        show ¬interpret_regex ((update_with_extension (nextFreshRefInEnv env) r
            [.field (qualify hd.1)] env.pathEnv).paths (u, v)) p
        simp only [update_with_extension, hu_ne_z, false_and, ite_false]
        by_cases hv_z : v = nextFreshRefInEnv env
        · subst hv_z; simp only [ite_true]
          have hr_ne_u : r ≠ u := fun h => hu_not_old (h ▸ hr_mem)
          exact no_match_extend [.field (qualify hd.1)] (fun q hq => hpaths_from_nm u r q hu_not_old hu_ne_root (Ne.symm hr_ne_u) hq) p
        · simp only [if_neg hv_z]
          exact hpaths_from_nm u v p hu_not_old hu_ne_root huv_ne
      · -- rmap_step root none
        dsimp only; simp [hroot_ne_z, hrmap_root_none]
      · -- refs_tracked
        intro r' hr'_mem
        dsimp only at hr'_mem
        rw [hrefs_eq] at hr'_mem
        simp only [List.mem_cons] at hr'_mem
        rcases hr'_mem with rfl | hr'_old
        · right; dsimp only; simp
        · rcases hrefs_tracked r' hr'_old with rfl | hne
          · exact Or.inl rfl
          · right; dsimp only
            have hr'_ne_z : r' ≠ nextFreshRefInEnv env := fun h => hfresh (h ▸ hr'_old)
            simp [hr'_ne_z, hne]

/-- A fresh ref (not in old pathEnv.refs) that ends up in the new pathEnv.refs
    is mapped to something by buildRefFieldEnvRmap. -/
private theorem buildRefFieldEnvRmap_new_ref_mapped (r : Aref) (bk : BorrowingKind)
    (fentries : AssocMap Field BasicMoveType)
    (qualify : Field → Field)
    (loc : Loc) (pathR : List Field)
    (fields : List (Field × Site)) (env : TypeEnv) (rmap : RefMap)
    (r' : Aref) (hr' : r' ∈ (addRefFieldSites r bk fentries qualify fields env).pathEnv.refs)
    (hr'_not_old : r' ∉ env.pathEnv.refs) :
    (buildRefFieldEnvRmap r bk fentries qualify loc pathR fields env rmap).2.map r' ≠ none := by
  induction fields generalizing env rmap with
  | nil => exact absurd hr' hr'_not_old
  | cons hd rest ih =>
    cases hlook : lookup fentries hd.1 with
    | none =>
      have hstep_a : addRefFieldSites r bk fentries qualify (hd :: rest) env =
          addRefFieldSites r bk fentries qualify rest env := by
        unfold addRefFieldSites; simp only [List.foldl, hlook]
      have hstep_b : buildRefFieldEnvRmap r bk fentries qualify loc pathR (hd :: rest) env rmap =
          buildRefFieldEnvRmap r bk fentries qualify loc pathR rest env rmap := by
        unfold buildRefFieldEnvRmap; simp only [List.foldl, hlook]
      rw [hstep_a] at hr'; rw [hstep_b]
      exact ih env rmap hr' hr'_not_old
    | some bt =>
      have hfresh := nextFreshRefInEnv_not_in_pathEnv env
      have hstep_a : addRefFieldSites r bk fentries qualify (hd :: rest) env =
          addRefFieldSites r bk fentries qualify rest
            {env with siteEnv := insert env.siteEnv hd.2 (.ref bt (nextFreshRefInEnv env) bk),
                      pathEnv := update_with_extension (nextFreshRefInEnv env) r [.field (qualify hd.1)] env.pathEnv} := by
        unfold addRefFieldSites; simp only [List.foldl, hlook]
      have hstep_b : buildRefFieldEnvRmap r bk fentries qualify loc pathR (hd :: rest) env rmap =
          buildRefFieldEnvRmap r bk fentries qualify loc pathR rest
            {env with siteEnv := insert env.siteEnv hd.2 (.ref bt (nextFreshRefInEnv env) bk),
                      pathEnv := update_with_extension (nextFreshRefInEnv env) r [.field (qualify hd.1)] env.pathEnv}
            { map := fun r'' => if r'' = nextFreshRefInEnv env then some (loc, pathR ++ [qualify hd.1]) else rmap.map r'' } := by
        unfold buildRefFieldEnvRmap; simp only [List.foldl, hlook]
      rw [hstep_a] at hr'; rw [hstep_b]
      -- Now hr' and goal use rest with stepped env/rmap
      -- env'.pathEnv = update_with_extension (nextFreshRefInEnv env) r [.field (qualify hd.1)] env.pathEnv
      by_cases hr'_in_env' : r' ∈ (update_with_extension (nextFreshRefInEnv env) r
          [.field (qualify hd.1)] env.pathEnv).refs
      · simp only [update_with_extension, show (nextFreshRefInEnv env ∈ env.pathEnv.refs) = False
          from propext ⟨hfresh, False.elim⟩, not_false_eq_true, ↓reduceIte] at hr'_in_env'
        cases hr'_in_env' with
        | head _ => -- r' = nextFreshRefInEnv env
          have hmem : nextFreshRefInEnv env ∈
              (update_with_extension (nextFreshRefInEnv env) r [.field (qualify hd.1)] env.pathEnv).refs := by
            simp only [update_with_extension, show (nextFreshRefInEnv env ∈ env.pathEnv.refs) = False
              from propext ⟨hfresh, False.elim⟩, not_false_eq_true, ↓reduceIte]
            exact .head _
          rw [buildRefFieldEnvRmap_old_ref _ r bk fentries qualify loc pathR rest _ _ hmem]
          simp
        | tail _ hmem => exact absurd hmem hr'_not_old
      · exact ih _ _ hr' hr'_in_env'

/-- readRef at a variant field path is non-none when HasType confirms the field exists.
    TODO: Update for flat encoding — field names in the value are qualified (qualifyField vname f),
    so this theorem needs qualified field names in fentries and path extensions.
    Requires updating addRefFieldSites/buildRefFieldEnvRmap to use qualified field names. -/
private theorem readRef_variant_field_ne_none
    {enumEnv : EnumEnv}
    (heap : Heap) (loc : Loc) (path : List Field) (f : Field)
    (vname : Id) (ename : Id)
    (fentries : AssocMap Field BasicMoveType) (bt : BasicMoveType)
    (hread : ∃ v, heap.readRef loc path = some v ∧
      HasType enumEnv v (.tenum ename))
    (hlookup_evf : enumVariantFields enumEnv ename vname = some fentries)
    (hbt : lookup fentries f = some bt)
    (hv_is_vname : ∀ v, heap.readRef loc path = some v →
      ∃ recFields, v = .variant vname ename recFields)
    (hnodup : ((allEnumFieldTypes (enumEnv.lookup ename).get!).map Prod.fst).Nodup) :
    heap.readRef loc (path ++ [qualifyField vname f]) ≠ none := by
  obtain ⟨v, hv_read, hht_v⟩ := hread
  obtain ⟨recFields, hrec_eq⟩ := hv_is_vname v hv_read
  subst hrec_eq
  -- From HasType.variant, get allEnumQualifiedFieldTypes and domain completeness
  cases hht_v with
  | variant vn en fields_v flat_fentries haqf hdom_complete _ _ _ =>
    -- From enumVariantFields, extract enumDef and variantDef
    simp only [enumVariantFields] at hlookup_evf
    cases hee : enumEnv.lookup ename with
    | none => simp [hee] at hlookup_evf
    | some enumDef =>
      simp [hee] at hlookup_evf
      cases hvv : enumDef.variants.lookup vname with
      | none => simp [hvv] at hlookup_evf
      | some variantDef =>
        simp [hvv] at hlookup_evf
        subst hlookup_evf
        -- Use bridge lemma to get qualifyField vname f in flat fentries
        simp [hee] at hnodup
        have ⟨flat_fe, haqf', hlookup_qf⟩ :=
          allEnumFieldTypes_lookup_bridge hee hvv hbt hnodup
        -- Unify flat_fentries and flat_fe via haqf/haqf'
        simp only [allEnumQualifiedFieldTypes, hee] at haqf haqf'
        have heq1 : flat_fentries = ⟨allEnumFieldTypes enumDef⟩ := by
          exact Option.some.inj haqf.symm
        have heq2 : flat_fe = ⟨allEnumFieldTypes enumDef⟩ := by
          exact Option.some.inj haqf'.symm
        rw [heq2] at hlookup_qf; rw [heq1] at hdom_complete
        -- From HasType domain completeness: fields_v has the qualified field
        have hfields_ne_none := hdom_complete (qualifyField vname f) (by rw [hlookup_qf]; exact fun h => nomatch h)
        -- Unfold readRef: heap.read loc >>= fun v => readPath v (path ++ [qualifyField vname f])
        -- We know heap.readRef loc path = some (.variant vname ename recFields)
        -- So readPath (.variant vname ename recFields) [qualifyField vname f] ≠ none
        unfold Heap.readRef at hv_read ⊢
        simp only [bind, Option.bind] at hv_read ⊢
        cases hread_loc : heap.read loc with
        | none => simp [hread_loc] at hv_read
        | some v_loc =>
          simp only [hread_loc] at hv_read ⊢
          -- readPath v_loc path = some (.variant ...)
          -- readPath v_loc (path ++ [qualifyField vname f]) unfolds to readPath of readPath
          rw [readPath_append]
          · simp only [hv_read]
            cases hfl : recFields.lookup (qualifyField vname f) with
            | none => exact absurd hfl hfields_ne_none
            | some v' => simp [readPath, hfl]

/-- Reading a qualified field from a variant ref gives a typed value. -/
private theorem readRef_variant_field_HasType
    {enumEnv : EnumEnv}
    (heap : Heap) (loc : Loc) (path : List Field) (f : Field)
    (vname : Id) (ename : Id)
    (fentries : AssocMap Field BasicMoveType) (bt : BasicMoveType)
    (hv_read : heap.readRef loc path = some (.variant vname ename (recFields : List (Field × Value))))
    (hht_v : HasType enumEnv (.variant vname ename recFields) (.tenum ename))
    (hlookup_evf : enumVariantFields enumEnv ename vname = some fentries)
    (hbt : lookup fentries f = some bt)
    (hnodup : ((allEnumFieldTypes (enumEnv.lookup ename).get!).map Prod.fst).Nodup) :
    ∃ val, heap.readRef loc (path ++ [qualifyField vname f]) = some val ∧
      HasType enumEnv val bt := by
  -- Get enumDef and variantDef from enumVariantFields
  simp only [enumVariantFields] at hlookup_evf
  cases hee : enumEnv.lookup ename with
  | none => simp [hee] at hlookup_evf
  | some enumDef =>
    simp [hee] at hlookup_evf
    cases hvv : enumDef.variants.lookup vname with
    | none => simp [hvv] at hlookup_evf
    | some variantDef =>
      simp [hvv] at hlookup_evf; subst hlookup_evf
      -- Get qualified field in flat fentries
      simp [hee] at hnodup
      have ⟨flat_fe, haqf, hlookup_qf⟩ :=
        allEnumFieldTypes_lookup_bridge hee hvv hbt hnodup
      -- Get typed value from HasType
      obtain ⟨vf, hvf_lookup, hvf_typed⟩ :=
        HasType_variant_field_typed hht_v haqf hlookup_qf
      -- readRef gives vf
      refine ⟨vf, ?_, hvf_typed⟩
      unfold Heap.readRef at hv_read ⊢
      simp only [bind, Option.bind] at hv_read ⊢
      cases hread_loc : heap.read loc with
      | none => simp [hread_loc] at hv_read
      | some v_loc =>
        simp only [hread_loc] at hv_read ⊢
        rw [readPath_append]
        simp only [hv_read, Option.bind, readPath, hvf_lookup]

private theorem preservation_unpackVariant (m m' : Machine) (env : TypeEnv) (lenv : LabelEnv)
    (retTypes : List ParamType) (rmap : RefMap)
    (hwt : WellTypedState m env lenv retTypes rmap)
    (hss : StackSafe env.enumEnv m.stack m.frame.returnInfo m.heap retTypes)
    (vname : Id) (fields : List (Field × Site)) (src : Site) (cont : Stmt)
    (hstmt : m.frame.stmt = .unpackVariant vname fields src cont)
    (hstep : step (.running m) = .running m') :
    ∃ env' lenv' retTypes' rmap',
      env'.enumEnv = env.enumEnv ∧ WellTypedState m' env' lenv' retTypes' rmap' ∧
      StackSafe env.enumEnv m'.stack m'.frame.returnInfo m'.heap retTypes' := by
  -- TODO: Update for EnumEnv refactoring (tenum now 1-arg, variant 3-arg, uses enumVariantFields)
  rcases inv_unpackVariant (by rw [← hstmt]; exact hwt.stmt_typed) with
    ⟨ename, enumDef, variantDef, hlookup_src, hlookup_enum, hlookup_var, hfresh, hdistinct, hexist, hcont⟩ |
    ⟨ename, enumDef, variantDef, r, bk, hlookup_src, hlookup_enum, hlookup_var, hfresh, hdistinct, hexist, hcont⟩
  · -- OWNED case: src has type .basic (.tenum ename variants)
    -- 2. Get variant value from site_consistent
    obtain ⟨vsrc, hvsrc, hmatch_src⟩ := hwt.site_consistent src _ hlookup_src
    simp only [ValueMatchesType] at hmatch_src
    obtain ⟨actualVariant, recFields, hrec_eq⟩ := HasType.variant_fields hmatch_src
    subst hrec_eq
    -- 3. readSite succeeds → simplify step
    have hrs : readSite m src = some (.variant actualVariant ename recFields) := hvsrc
    simp only [step, hstmt, hrs] at hstep
    -- actualVariant == vname must be true (otherwise step gives error)
    split at hstep
    · rename_i heq_true
      simp only [ExecState.running.injEq] at hstep; subst hstep
      rw [beq_iff_eq] at heq_true; subst heq_true
      -- Now actualVariant = vname, so HasType gives us variantDef.fields for this variant
      -- Derive enumVariantFields from hlookup_enum and hlookup_var
      have hevf : enumVariantFields env.enumEnv ename actualVariant = some variantDef.fields := by
        simp [enumVariantFields, hlookup_enum, hlookup_var]
      -- 4. Derive site uniqueness from distinctness
      have huniq_site : ∀ (a : Site), ∀ f f', (f, a) ∈ fields → (f', a) ∈ fields → f' = f := by
        intro a f f' hfa hf'a
        by_contra hne
        exact absurd rfl (hdistinct a a ⟨f, f', hfa, hf'a, Ne.symm hne⟩)
      -- 5. Helper: any field site in addFieldSites has basic type
      have field_site_lookup : ∀ sd fd,
          (fd, sd) ∈ fields →
          ∃ bt, lookup variantDef.fields fd = some bt ∧
            lookup (addFieldSites variantDef.fields (delete env.siteEnv src) fields) sd = some (.basic bt) :=
        fun sd fd hmem =>
          let ⟨bt, hbt⟩ := hexist fd sd hmem
          ⟨bt, hbt, addFieldSites_lookup_mem variantDef.fields _ fields fd sd bt hmem hbt
            (fun f' hf' => huniq_site sd fd f' hmem hf')⟩
      -- 6. Construct new WellTypedState (follows preservation_unpack exactly)
      refine ⟨{env with siteEnv := addFieldSites variantDef.fields (delete env.siteEnv src) fields},
              lenv, retTypes, rmap, rfl, ?_, hss⟩
      exact {
        env_wf := by
          constructor
          · exact hwt.env_wf.pathEnv_wf
          · exact addFieldSites_refs_not_root variantDef.fields _ fields
                  (SiteEnv.delete_refs_not_root env.siteEnv src hwt.env_wf.siteEnv_wf)
          · exact hwt.env_wf.varEnv_wf
        enumEnv_consistent := hwt.enumEnv_consistent
        enum_qualified_nodup := hwt.enum_qualified_nodup
        enum_names_nodup := hwt.enum_names_nodup
        enum_variant_nodup := hwt.enum_variant_nodup
        enum_fields_nodup := hwt.enum_fields_nodup
        defaultValues_typed := hwt.defaultValues_typed
        stmt_typed := hcont
        var_consistent := hwt.var_consistent
        site_consistent := by
          intro s' τ' hl
          by_cases hs'_in : s' ∈ fields.map Prod.snd
          · -- New field site
            obtain ⟨⟨fd, sd⟩, hmem_fd, heq_s'⟩ := List.mem_map.mp hs'_in
            simp at heq_s'; subst heq_s'
            obtain ⟨bt', hbt', hlookup_new⟩ := field_site_lookup sd fd hmem_fd
            rw [hlookup_new] at hl; cases hl
            -- Use bridge lemma to get qualified field type
            obtain ⟨fentries, haqf, hlookup_qf⟩ :=
              allEnumFieldTypes_lookup_bridge hlookup_enum hlookup_var hbt'
                (hwt.enum_qualified_nodup ename _ hlookup_enum)
            -- Use HasType_variant_field_typed to type the value
            obtain ⟨vf, hvf_lookup, hvf_typed⟩ :=
              HasType_variant_field_typed hmatch_src haqf hlookup_qf
            -- The siteStore has vf at sd (from the foldl with qualifyField)
            have hfoldl_sd := variant_unpack_foldl_lookup_mem actualVariant recFields
              m.frame.siteStore fields fd sd vf hmem_fd hvf_lookup
              (fun f' hf' => huniq_site sd fd f' hmem_fd hf')
            exact ⟨vf, hfoldl_sd, hvf_typed⟩
          · -- Old site (not in fields)
            have hlookup_env := addFieldSites_lookup_not_in_fields variantDef.fields
              (delete env.siteEnv src) fields s' hs'_in
            rw [hlookup_env] at hl
            have hne_src : s' ≠ src := by
              intro h; subst h; rw [lookup_delete_same] at hl; cases hl
            rw [lookup_delete_ne _ src s' hne_src] at hl
            obtain ⟨v, hv, hm⟩ := hwt.site_consistent s' τ' hl
            -- siteStore for old sites is preserved (foldl only inserts at field sites)
            have hfoldl_old := variant_unpack_foldl_lookup_not_in_fields actualVariant recFields
              m.frame.siteStore fields s' hs'_in
            exact ⟨v, hfoldl_old ▸ hv, hm⟩
        rmap_live := hwt.rmap_live
        rmap_paths := hwt.rmap_paths
        varEnv_refs_in_pathEnv := hwt.varEnv_refs_in_pathEnv
        siteEnv_refs_in_pathEnv := by
          intro s' bt r bk hlookup_s'
          by_cases hs'_in : s' ∈ fields.map Prod.snd
          · obtain ⟨⟨fd, sd⟩, hmem_fd, heq_s'⟩ := List.mem_map.mp hs'_in
            simp at heq_s'; subst heq_s'
            obtain ⟨bt', _, hlookup_new⟩ := field_site_lookup sd fd hmem_fd
            rw [hlookup_new] at hlookup_s'; cases hlookup_s'
          · have hlookup_env := addFieldSites_lookup_not_in_fields variantDef.fields
              (delete env.siteEnv src) fields s' hs'_in
            rw [hlookup_env] at hlookup_s'
            have hne_src : s' ≠ src := by
              intro h; subst h; rw [lookup_delete_same] at hlookup_s'; cases hlookup_s'
            rw [lookup_delete_ne _ src s' hne_src] at hlookup_s'
            exact hwt.siteEnv_refs_in_pathEnv s' bt r bk hlookup_s'
        live_refs_unique := by
          intro r
          refine ⟨?_, ?_, ?_⟩
          · intro x bt bk ms s' bt' bk' hvar hlookup_s'
            by_cases hs'_in : s' ∈ fields.map Prod.snd
            · obtain ⟨⟨fd, sd⟩, hmem_fd, heq_s'⟩ := List.mem_map.mp hs'_in
              simp at heq_s'; subst heq_s'
              obtain ⟨_, _, hlookup_new⟩ := field_site_lookup sd fd hmem_fd
              rw [hlookup_new] at hlookup_s'; cases hlookup_s'
            · have hlookup_env := addFieldSites_lookup_not_in_fields variantDef.fields
                (delete env.siteEnv src) fields s' hs'_in
              rw [hlookup_env] at hlookup_s'
              have hne_src : s' ≠ src := by
                intro h; subst h; rw [lookup_delete_same] at hlookup_s'; cases hlookup_s'
              rw [lookup_delete_ne _ src s' hne_src] at hlookup_s'
              exact (hwt.live_refs_unique r).1 x bt bk ms s' bt' bk' hvar hlookup_s'
          · intro s1 s2 bt1 bt2 bk1 bk2 hne12 hs1 hs2
            have get_old : ∀ s bt' bk', lookup (addFieldSites variantDef.fields (delete env.siteEnv src) fields) s
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
          intro r bt loc path hrmap hcond
          apply hwt.rmap_has_type r bt loc path hrmap
          rcases hcond with ⟨x, bk, ms, hvar⟩ | ⟨s', bk, hsite⟩
          · exact Or.inl ⟨x, bk, ms, hvar⟩
          · by_cases hs'_in : s' ∈ fields.map Prod.snd
            · obtain ⟨⟨fd, sd⟩, hmem_fd, heq_s'⟩ := List.mem_map.mp hs'_in
              simp at heq_s'; subst heq_s'
              obtain ⟨_, _, hlookup_new⟩ := field_site_lookup sd fd hmem_fd
              rw [hlookup_new] at hsite; cases hsite
            · have hlookup_env := addFieldSites_lookup_not_in_fields variantDef.fields
                (delete env.siteEnv src) fields s' hs'_in
              rw [hlookup_env] at hsite
              have hne_src : s' ≠ src := by
                intro h; subst h; rw [lookup_delete_same] at hsite; cases hsite
              rw [lookup_delete_ne _ src s' hne_src] at hsite
              exact Or.inr ⟨s', bk, hsite⟩
        funEnv_sig_consistent := hwt.funEnv_sig_consistent
        refs_tracked_mapped := hwt.refs_tracked_mapped
        lenv_labels_in_blocks := hwt.lenv_labels_in_blocks
        has_return_info := hwt.has_return_info
        varStore_locs_bound := hwt.varStore_locs_bound
      }
    · -- actualVariant ≠ vname → step gives error, contradiction
      simp at hstep
  · -- REF case: src has type .ref (.tenum ename) r bk
    -- 2. Get ref value from site_consistent
    obtain ⟨vsrc, hvsrc, hmatch_src⟩ := hwt.site_consistent src _ hlookup_src
    obtain ⟨loc, pathR, hv_eq, hrmap_r⟩ := hmatch_src
    subst hv_eq
    -- 3. readRef succeeds → variant value
    have hr_tracked := hwt.siteEnv_refs_in_pathEnv src (.tenum ename) r bk hlookup_src
    have hlive_r := hwt.rmap_live r loc pathR hr_tracked hrmap_r
    have hht_r := hwt.rmap_has_type r (.tenum ename) loc pathR hrmap_r
      (Or.inr ⟨src, bk, hlookup_src⟩)
    -- 4. readSite succeeds → simplify step
    have hrs : readSite m src = some (.ref loc pathR) := hvsrc
    obtain ⟨v_at_ref, hv_read, hht_v⟩ := hht_r
    simp only [step, hstmt, hrs, hv_read] at hstep
    -- v_at_ref must be a variant (from HasType)
    obtain ⟨actualVariant, recFields, hrec_eq⟩ := HasType.variant_fields hht_v
    subst hrec_eq
    simp only at hstep
    split at hstep
    · rename_i heq_true
      simp only [ExecState.running.injEq] at hstep; subst hstep
      rw [beq_iff_eq] at heq_true; subst heq_true
      -- Now actualVariant = vname
      -- 4b. Define qualify and fentries for enum variant fields
      let qualify := MoveLight.qualifyField actualVariant
      let fentries := variantDef.fields
      have hevf : enumVariantFields env.enumEnv ename actualVariant = some fentries := by
        simp only [enumVariantFields, hlookup_enum, hlookup_var]; rfl
      -- 5. Derive site uniqueness
      have huniq_site : ∀ (a : Site), ∀ f f', (f, a) ∈ fields → (f', a) ∈ fields → f' = f := by
        intro a f f' hfa hf'a
        by_contra hne
        exact absurd rfl (hdistinct a a ⟨f, f', hfa, hf'a, Ne.symm hne⟩)
      -- 6. Define env0 and env'
      let env0 : TypeEnv := {env with siteEnv := delete env.siteEnv src}
      have haddEnumEnv : (addRefFieldSites r bk fentries qualify fields env0).enumEnv = env.enumEnv :=
        addRefFieldSites_enumEnv_eq r bk fentries qualify fields env0
      -- 7. Define rmap' using paired fold
      let pair := buildRefFieldEnvRmap r bk variantDef.fields qualify loc pathR fields env0 rmap
      let rmap' := pair.2
      have henv_eq : pair.1 = addRefFieldSites r bk variantDef.fields qualify fields env0 :=
        buildRefFieldEnvRmap_fst_eq r bk variantDef.fields qualify loc pathR fields env0 rmap
      -- 8. Key facts about rmap'
      have hr_in_refs : r ∈ env0.pathEnv.refs :=
        hwt.siteEnv_refs_in_pathEnv src (.tenum ename) r bk hlookup_src
      have hrmap'_r : rmap'.map r = some (loc, pathR) :=
        buildRefFieldEnvRmap_old_ref r r bk fentries qualify loc pathR fields env0 rmap hr_in_refs ▸ hrmap_r
      have hrmap'_root : rmap'.map .root = none :=
        buildRefFieldEnvRmap_root_none r bk fentries qualify loc pathR fields env0 rmap
          hwt.env_wf.pathEnv_wf.root_in_refs hwt.rmap_root_none
      -- Helper: RefsUnique for env0
      have huniq0 : RefsUnique env0.varEnv env0.siteEnv := by
        intro r'
        refine ⟨fun x bt' bk' ms s bt'' bk'' hv hs => ?_,
                fun s s' bt' bt'' bk' bk'' hne hs hs' => ?_,
                (hwt.live_refs_unique r').2.2⟩
        · show False
          by_cases hsa : s = src
          · subst hsa; rw [lookup_delete_same] at hs; cases hs
          · rw [lookup_delete_ne _ _ _ hsa] at hs
            exact (hwt.live_refs_unique r').1 _ _ _ _ _ _ _ hv hs
        · show False
          by_cases hsa : s = src
          · subst hsa; rw [lookup_delete_same] at hs; cases hs
          · by_cases hsa' : s' = src
            · subst hsa'; rw [lookup_delete_same] at hs'; cases hs'
            · rw [lookup_delete_ne _ _ _ hsa] at hs
              rw [lookup_delete_ne _ _ _ hsa'] at hs'
              exact (hwt.live_refs_unique r').2.1 _ _ _ _ _ _ hne hs hs'
      -- Helper: siteEnv_refs_in_pathEnv for env0
      have hsite_tracked0 : ∀ s bt' r' bk',
          lookup env0.siteEnv s = some (.ref bt' r' bk') → r' ∈ env0.pathEnv.refs := by
        intro s bt' r' bk' hs
        by_cases hsa : s = src
        · subst hsa; rw [lookup_delete_same] at hs; cases hs
        · rw [lookup_delete_ne _ _ _ hsa] at hs
          exact hwt.siteEnv_refs_in_pathEnv s bt' r' bk' hs
      -- 9. Construct WellTypedState
      refine ⟨addRefFieldSites r bk fentries qualify fields env0,
              lenv, retTypes, rmap', haddEnumEnv, ?_, hss⟩
      have henv0_wf_path := hwt.env_wf.pathEnv_wf
      have henv0_wf_site := SiteEnv.delete_refs_not_root env.siteEnv src hwt.env_wf.siteEnv_wf
      exact {
        env_wf := ⟨addRefFieldSites_pathEnv_wf r bk fentries qualify fields env0 henv0_wf_path,
                   addRefFieldSites_siteEnv_wf r bk fentries qualify fields env0 henv0_wf_site,
                   addRefFieldSites_varEnv_eq r bk fentries qualify fields env0 ▸ hwt.env_wf.varEnv_wf⟩
        enumEnv_consistent := hwt.enumEnv_consistent.trans haddEnumEnv.symm
        enum_qualified_nodup := by rw [addRefFieldSites_enumEnv_eq]; exact hwt.enum_qualified_nodup
        enum_names_nodup := by rw [addRefFieldSites_enumEnv_eq]; exact hwt.enum_names_nodup
        enum_variant_nodup := by rw [addRefFieldSites_enumEnv_eq]; intro ename ed he; exact hwt.enum_variant_nodup ename ed he
        enum_fields_nodup := by rw [addRefFieldSites_enumEnv_eq]; intro ename ed vn vd he hvn; exact hwt.enum_fields_nodup ename ed vn vd he hvn
        defaultValues_typed := by
          rw [addRefFieldSites_enumEnv_eq]; intro ename ed vn vd f bt he hv hf
          exact hwt.defaultValues_typed ename ed vn vd f bt he hv hf
        stmt_typed := hcont
        var_consistent := by
          intro x isv τ ms hlook
          rw [addRefFieldSites_varEnv_eq] at hlook
          have hvc := hwt.var_consistent x isv τ ms hlook
          cases isv with
          | invalidVar => exact hvc
          | validVar =>
            obtain ⟨loc_x, v_x, hloc, hread, hm⟩ := hvc
            refine ⟨loc_x, v_x, hloc, hread, ?_⟩
            cases τ with
            | basic bt' =>
              simp only [ValueMatchesType] at hm ⊢
              rw [haddEnumEnv]; exact hm
            | ref bt' r' bk' =>
              simp only [ValueMatchesType] at hm ⊢
              obtain ⟨loc', path', hv_eq, hrmap_r'⟩ := hm
              exact ⟨loc', path', hv_eq,
                buildRefFieldEnvRmap_old_ref r' r bk fentries qualify loc pathR fields env0 rmap
                  (hwt.varEnv_refs_in_pathEnv x bt' r' bk' ms hlook) ▸ hrmap_r'⟩
        site_consistent := by
          intro s' τ' hl
          by_cases hs'_in : s' ∈ fields.map Prod.snd
          · -- New field site
            obtain ⟨⟨fd, sd⟩, hmem_fd, heq_s'⟩ := List.mem_map.mp hs'_in
            simp at heq_s'; subst heq_s'
            obtain ⟨bt_fd, hbt_fd⟩ := hexist fd sd hmem_fd
            -- Get siteEnv lookup and rmap mapping for new ref
            obtain ⟨rf, hlookup_new, hrmap_rf⟩ :=
              buildRefFieldEnvRmap_field_consistent r bk fentries qualify loc pathR fields env0 rmap
                fd sd hmem_fd bt_fd hbt_fd
                (fun f' hf' => huniq_site sd fd f' hmem_fd hf')
            rw [hlookup_new] at hl; cases hl
            -- siteStore has .ref loc (pathR ++ [qualify fd]) at sd
            have hfoldl_sd := ref_unpack_foldl_lookup_mem qualify loc pathR
              m.frame.siteStore fields fd sd hmem_fd
              (fun f' hf' => huniq_site sd fd f' hmem_fd hf')
            refine ⟨.ref loc (pathR ++ [qualify fd]), hfoldl_sd, ?_⟩
            simp only [ValueMatchesType]
            exact ⟨loc, pathR ++ [qualify fd], rfl, hrmap_rf⟩
          · -- Old site (not in fields)
            have hlookup_env := addRefFieldSites_lookup_not_in_fields r bk fentries qualify fields
              env0 s' hs'_in
            rw [hlookup_env] at hl
            have hne_src : s' ≠ src := by
              intro h; subst h; rw [lookup_delete_same] at hl; cases hl
            rw [lookup_delete_ne _ src s' hne_src] at hl
            obtain ⟨v, hv, hm⟩ := hwt.site_consistent s' τ' hl
            -- siteStore for old sites is preserved
            have hfoldl_old := ref_unpack_foldl_lookup_not_in_fields qualify loc pathR
              m.frame.siteStore fields s' hs'_in
            refine ⟨v, hfoldl_old ▸ hv, ?_⟩
            cases τ' with
            | basic bt' =>
              simp only [ValueMatchesType] at hm ⊢
              rw [haddEnumEnv]; exact hm
            | ref bt' r' bk' =>
              simp only [ValueMatchesType] at hm ⊢
              obtain ⟨loc', path', hv_eq, hrmap_r'⟩ := hm
              exact ⟨loc', path', hv_eq,
                buildRefFieldEnvRmap_old_ref r' r bk fentries qualify loc pathR fields env0 rmap
                  (hwt.siteEnv_refs_in_pathEnv s' bt' r' bk' hl) ▸ hrmap_r'⟩
        rmap_live := by
          intro r' loc' path' hr'_mem hrmap'_eq
          rcases buildRefFieldEnvRmap_map_cases_tracked r bk fentries qualify loc pathR fields env0 rmap r'
            (henv_eq ▸ hr'_mem) with ⟨hr'_old, hmap_eq⟩ | ⟨f_map, bt_map, hbt_map, hmap_eq⟩
          · -- Old ref: rmap' preserves old mapping
            rw [hmap_eq] at hrmap'_eq
            exact hwt.rmap_live r' loc' path' hr'_old hrmap'_eq
          · -- New ref: rmap' maps to (loc, pathR ++ [qualify f_map])
            rw [hmap_eq] at hrmap'_eq; cases hrmap'_eq
            -- Need: heap.readRef loc (pathR ++ [qualify f_map]) ≠ none
            exact readRef_variant_field_ne_none m.heap loc pathR f_map actualVariant ename
              fentries bt_map ⟨_, hv_read, hht_v⟩ hevf hbt_map
              (fun v hv => by rw [hv_read] at hv; simp at hv; exact ⟨recFields, hv.symm⟩)
              (by rw [hlookup_enum]; simp; exact hwt.enum_qualified_nodup ename enumDef hlookup_enum)
        rmap_paths := by
          have hreadref_all : ∀ f, lookup fentries f ≠ none →
              m.heap.readRef loc (pathR ++ [qualify f]) ≠ none := by
            intro f hf
            cases hbt' : lookup fentries f with
            | none => exact absurd hbt' hf
            | some bt' =>
              exact readRef_variant_field_ne_none m.heap loc pathR f actualVariant ename
                fentries bt' ⟨_, hv_read, hht_v⟩ hevf hbt'
                (fun v hv => by rw [hv_read] at hv; simp at hv; exact ⟨recFields, hv.symm⟩)
                (by rw [hlookup_enum]; simp; exact hwt.enum_qualified_nodup ename enumDef hlookup_enum)
          exact addRefFieldSites_rmap_paths r bk fentries qualify loc pathR fields env0 rmap m.heap
            hr_in_refs hrmap_r hwt.rmap_paths
            hwt.self_loop_only_empty hwt.paths_to_non_member_empty
            hwt.paths_from_non_member_empty
            hwt.rmap_root_none hwt.env_wf.pathEnv_wf.root_in_refs hwt.refs_tracked_mapped
            hreadref_all
        varEnv_refs_in_pathEnv :=
          addRefFieldSites_var_tracked r bk fentries qualify fields env0
            hwt.varEnv_refs_in_pathEnv
        siteEnv_refs_in_pathEnv :=
          addRefFieldSites_site_tracked r bk fentries qualify fields env0
            hsite_tracked0 hr_in_refs
        live_refs_unique :=
          addRefFieldSites_RefsUnique r bk fentries qualify fields env0 huniq0
        blocks_typed := hwt.blocks_typed
        lenv_empty_siteEnv := hwt.lenv_empty_siteEnv
        lenv_wf := hwt.lenv_wf
        lenv_var_tracked := hwt.lenv_var_tracked
        lenv_var_unique := hwt.lenv_var_unique
        lenv_funEnv_eq := by
          intro L envL hlook
          rw [hwt.lenv_funEnv_eq L envL hlook, addRefFieldSites_funEnv_eq]
        funEnv_typed := by
          have : (addRefFieldSites r bk fentries qualify fields env0).enumEnv = env.enumEnv := haddEnumEnv
          rw [this]; exact hwt.funEnv_typed
        heap_loc_bound := hwt.heap_loc_bound
        lenv_labels_in_blocks := hwt.lenv_labels_in_blocks
        has_return_info := hwt.has_return_info
        rmap_root_none := hrmap'_root
        no_paths_to_root := by
          have hr_ne_root : r ≠ .root := fun h => by
            rw [h] at hrmap_r; rw [hwt.rmap_root_none] at hrmap_r; cases hrmap_r
          exact addRefFieldSites_no_paths_to_root r bk fentries qualify fields env0
            hr_ne_root hwt.env_wf.pathEnv_wf.root_in_refs hwt.no_paths_to_root
        root_path_coherence :=
          addRefFieldSites_root_path_coherence r bk fentries qualify loc pathR fields env0 rmap
            m.heap m.frame.varStore
            hr_in_refs hrmap_r hwt.root_path_coherence
            hwt.self_loop_only_empty hwt.paths_to_non_member_empty
            hwt.rmap_root_none hwt.env_wf.pathEnv_wf.root_in_refs hwt.refs_tracked_mapped
        paths_from_non_member_empty :=
          addRefFieldSites_paths_from_nm r bk fentries qualify fields env0
            hwt.paths_from_non_member_empty hr_in_refs
        paths_to_non_member_empty :=
          addRefFieldSites_paths_to_nm r bk fentries qualify fields env0
            hwt.paths_to_non_member_empty hr_in_refs
        self_loop_only_empty :=
          addRefFieldSites_self_loop_only_empty r bk fentries qualify fields env0
            hwt.self_loop_only_empty
        rmap_has_type := by
          intro r' bt' loc' path' hrmap'_eq hcond
          rcases hcond with ⟨x, bk', ms, hvar⟩ | ⟨s', bk', hsite⟩
          · -- r' used in varEnv (unchanged) → old ref
            rw [addRefFieldSites_varEnv_eq] at hvar
            have hr'_old := hwt.varEnv_refs_in_pathEnv x bt' r' bk' ms hvar
            rw [buildRefFieldEnvRmap_old_ref r' r bk fentries qualify loc pathR fields env0 rmap hr'_old]
              at hrmap'_eq
            obtain ⟨val, hreadref, hht_val⟩ := hwt.rmap_has_type r' bt' loc' path' hrmap'_eq (Or.inl ⟨x, bk', ms, hvar⟩)
            exact ⟨val, hreadref, haddEnumEnv ▸ hht_val⟩
          · -- r' used in siteEnv
            by_cases hs'_in : s' ∈ fields.map Prod.snd
            · -- Field site: r' is a fresh ref
              obtain ⟨⟨fd, sd⟩, hmem_fd, heq_s'⟩ := List.mem_map.mp hs'_in
              simp at heq_s'; subst heq_s'
              obtain ⟨bt_fd, hbt_fd⟩ := hexist fd sd hmem_fd
              obtain ⟨rf, hlookup_new, hrmap_rf⟩ :=
                buildRefFieldEnvRmap_field_consistent r bk fentries qualify loc pathR fields env0 rmap
                  fd sd hmem_fd bt_fd hbt_fd
                  (fun f' hf' => huniq_site sd fd f' hmem_fd hf')
              rw [hlookup_new] at hsite
              cases hsite -- gives bt' = bt_fd, r' = rf, bk' = bk
              rw [hrmap_rf] at hrmap'_eq; cases hrmap'_eq
              -- Use readRef_variant_field_HasType to get typed value
              obtain ⟨val, hreadref_val, hht_val⟩ :=
                readRef_variant_field_HasType m.heap loc pathR fd actualVariant ename
                  fentries _ hv_read hht_v hevf hbt_fd
                  (by rw [hlookup_enum]; simp; exact hwt.enum_qualified_nodup ename enumDef hlookup_enum)
              exact ⟨val, hreadref_val, haddEnumEnv ▸ hht_val⟩
            · -- Old site: r' is an old ref
              have hlookup_env := addRefFieldSites_lookup_not_in_fields r bk fentries qualify fields
                env0 s' hs'_in
              rw [hlookup_env] at hsite
              have hne_src : s' ≠ src := by
                intro h; subst h; rw [lookup_delete_same] at hsite; cases hsite
              rw [lookup_delete_ne _ src s' hne_src] at hsite
              have hr'_old := hwt.siteEnv_refs_in_pathEnv s' bt' r' bk' hsite
              rw [buildRefFieldEnvRmap_old_ref r' r bk fentries qualify loc pathR fields env0 rmap hr'_old]
                at hrmap'_eq
              obtain ⟨val, hreadref, hht_val⟩ := hwt.rmap_has_type r' bt' loc' path' hrmap'_eq (Or.inr ⟨s', bk', hsite⟩)
              exact ⟨val, hreadref, haddEnumEnv ▸ hht_val⟩
        funEnv_sig_consistent := by
          rw [addRefFieldSites_funEnv_eq]
          exact hwt.funEnv_sig_consistent
        refs_tracked_mapped := by
          intro r' hr'_mem
          by_cases hr'_old : r' ∈ env0.pathEnv.refs
          · rcases hwt.refs_tracked_mapped r' hr'_old with rfl | hne
            · exact Or.inl rfl
            · right
              rw [buildRefFieldEnvRmap_old_ref r' r bk fentries qualify loc pathR fields env0 rmap hr'_old]
              exact hne
          · right
            exact buildRefFieldEnvRmap_new_ref_mapped r bk fentries qualify loc pathR fields env0 rmap
              r' hr'_mem hr'_old
        varStore_locs_bound := hwt.varStore_locs_bound
      }
    · -- actualVariant ≠ vname → step gives error
      simp at hstep

private theorem preservation_variantSwitch (m m' : Machine) (env : TypeEnv) (lenv : LabelEnv)
    (retTypes : List ParamType) (rmap : RefMap)
    (hwt : WellTypedState m env lenv retTypes rmap)
    (hss : StackSafe env.enumEnv m.stack m.frame.returnInfo m.heap retTypes)
    (src : Site) (cases_list : List (Id × Label))
    (hstmt : m.frame.stmt = .variantSwitch src cases_list)
    (hstep : step (.running m) = .running m') :
    ∃ env' lenv' retTypes' rmap',
      env'.enumEnv = env.enumEnv ∧ WellTypedState m' env' lenv' retTypes' rmap' ∧
      StackSafe env.enumEnv m'.stack m'.frame.returnInfo m'.heap retTypes' := by
  -- 1. Invert typing
  obtain ⟨ename, enumDef, r, bk, hlookup_src, hlookup_enum, hcoverage, hcases⟩ :=
    inv_variantSwitch (by rw [← hstmt]; exact hwt.stmt_typed)
  -- 2. Get concrete values from site_consistent and rmap
  obtain ⟨v_src, hsite_src, hvmt⟩ := hwt.site_consistent src _ hlookup_src
  obtain ⟨loc, path, hv_ref, hrmap_r⟩ := hvmt
  subst hv_ref
  -- 3. readRef succeeds (from rmap_live)
  have hr_tracked := hwt.siteEnv_refs_in_pathEnv src (.tenum ename) r bk hlookup_src
  have hread_ne := hwt.rmap_live r loc path hr_tracked hrmap_r
  obtain ⟨heap_val, hread⟩ := Option.ne_none_iff_exists'.mp hread_ne
  -- 4. heap value has type tenum → must be a variant
  have hhas_type : HasType env.enumEnv heap_val (.tenum ename) := by
    obtain ⟨v', hread', hht⟩ := hwt.rmap_has_type r (.tenum ename) loc path hrmap_r
      (Or.inr ⟨src, bk, hlookup_src⟩)
    simp only [hread, Option.some.injEq] at hread'; subst hread'; exact hht
  obtain ⟨actualVariant, actualFields, hval_eq⟩ := HasType.variant_fields hhas_type
  subst hval_eq
  -- 5. variant name is in enumDef.variants → in cases (coverage)
  have hlook_variant : AssocMap.lookup enumDef.variants actualVariant ≠ none := by
    cases hhas_type with
    | variant _ _ _ _ _ _ _ _ hvv =>
      simp only [enumVariantFields, hlookup_enum] at hvv
      cases hv : AssocMap.lookup enumDef.variants actualVariant with
      | none => simp [hv] at hvv
      | some _ => exact Option.some_ne_none _
  obtain ⟨label, hlabel_in⟩ := hcoverage actualVariant hlook_variant
  -- 6. Simplify step with known readSite and readRef
  simp only [step, hstmt, readSite, hsite_src, hread] at hstep
  -- 7. Case split on cases_list.lookup and findBlock (step requires both to succeed)
  cases hcl : cases_list.lookup actualVariant with
  | none => simp only [hcl] at hstep; exact absurd hstep (by simp)
  | some label' =>
    cases hfb : findBlock m.frame.blocks label' with
    | none => simp only [hcl, hfb] at hstep; exact absurd hstep (by simp)
    | some block =>
    simp only [hcl, hfb, ExecState.running.injEq] at hstep; subst hstep
    -- 8. Get envL from hcases: we know (actualVariant, label') ∈ cases_list
    have hlabel_in' : (actualVariant, label') ∈ cases_list :=
      list_lookup_mem_pair cases_list actualVariant label' hcl
    obtain ⟨envL, hlenv, hsubsumes⟩ := hcases actualVariant label' hlabel_in'
    obtain ⟨hmem_block, hlabel_eq⟩ := findBlock_spec m.frame.blocks label' block hfb
    -- 9. Set up modified env
    let env_mod : TypeEnv :=
      {env with siteEnv := delete env.siteEnv src
                pathEnv := delete_ref_node env.pathEnv r}
    -- 10. siteEnv of env_mod is empty (from subsumes + lenv_empty_siteEnv)
    have hse_empty : ∀ s, lookup env_mod.siteEnv s = none :=
      siteEnv_empty_from_subsumes envL env_mod hsubsumes
        (hwt.lenv_empty_siteEnv label' envL hlenv)
    -- 11. env_mod is WellFormed
    have hr_not_root : r ≠ .root := hwt.env_wf.siteEnv_wf src _ hlookup_src
    have hwfL := hwt.lenv_wf label' envL hlenv
    have hwf_mod : TypeEnv.WellFormed env_mod :=
      ⟨delete_ref_node_wellformed env.pathEnv r hwt.env_wf.pathEnv_wf hr_not_root,
       fun s τ hs => by rw [hse_empty s] at hs; exact absurd hs (by simp),
       hwt.env_wf.varEnv_wf⟩
    -- 12. Get stmt_typed via weakening
    have hblock := hwt.blocks_typed block hmem_block envL (hlabel_eq ▸ hlenv)
    have hsite_empty := hwt.lenv_empty_siteEnv label' envL hlenv
    have hstmt' := typecheck_stmt_weaken lenv envL env_mod block.body retTypes
        hblock hsubsumes (hwt.lenv_funEnv_eq label' envL hlenv) hwfL hwf_mod
        (fun s _ _ _ h => absurd h (by rw [hsite_empty s]; simp))
        (hwt.lenv_var_tracked label' envL hlenv)
        (fun r' => ⟨fun _ _ _ _ s _ _ _ h => by rw [hsite_empty s] at h; simp at h,
                     fun s _ _ _ _ _ _ h => by rw [hsite_empty s] at h; simp at h,
                     hwt.lenv_var_unique label' envL hlenv r'⟩)
        (delete_ref_node_paths_to_non_member env.pathEnv r hwt.paths_to_non_member_empty)
        (delete_ref_node_paths_from_non_member env.pathEnv r hwt.paths_from_non_member_empty)
        (by intro u p hp
            change interpret_regex ((delete_ref_node env.pathEnv r).paths (u, u)) p at hp
            simp only [delete_ref_node] at hp
            by_cases hu : u = r
            · subst hu; rw [if_pos ⟨rfl, rfl⟩] at hp; exact hp
            · simp only [hu, false_or, ↓reduceIte] at hp
              exact hwt.self_loop_only_empty u p hp)
    -- 13. Construct WellTypedState
    refine ⟨env_mod, lenv, retTypes, rmap, rfl, ?_, hss⟩
    exact {
      env_wf := hwf_mod
      enumEnv_consistent := hwt.enumEnv_consistent
      enum_qualified_nodup := hwt.enum_qualified_nodup
      enum_names_nodup := hwt.enum_names_nodup
      enum_variant_nodup := hwt.enum_variant_nodup
      enum_fields_nodup := hwt.enum_fields_nodup
      defaultValues_typed := hwt.defaultValues_typed
      stmt_typed := hstmt'
      var_consistent := hwt.var_consistent
      site_consistent := fun s τ h => by rw [hse_empty s] at h; exact absurd h (by simp)
      rmap_live := by
        intro r' loc' path' hr'_tracked hrmap'
        have hr'_old : r' ∈ env.pathEnv.refs := by
          rw [delete_ref_node_refs] at hr'_tracked
          exact (List.mem_filter.mp hr'_tracked).1
        exact hwt.rmap_live r' loc' path' hr'_old hrmap'
      rmap_paths := rmap_paths_delete_ref_node env m rmap r hwt.rmap_paths
      varEnv_refs_in_pathEnv :=
        varEnv_refs_in_pathEnv_delete_ref_node hwt r src (.tenum ename) bk hlookup_src
      siteEnv_refs_in_pathEnv := fun s _ _ _ h => by rw [hse_empty s] at h; exact absurd h (by simp)
      live_refs_unique := by
        intro r'
        exact ⟨fun _ _ _ _ s _ _ _ h => by rw [hse_empty s] at h; exact absurd h (by simp),
               fun s _ _ _ _ _ _ h => by rw [hse_empty s] at h; exact absurd h (by simp),
               (hwt.live_refs_unique r').2.2⟩
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
        change interpret_regex ((delete_ref_node env.pathEnv r).paths (u, u)) p at hp
        simp only [delete_ref_node] at hp
        by_cases hu : u = r
        · subst hu; rw [if_pos ⟨rfl, rfl⟩] at hp; exact hp
        · simp only [hu, false_or, ↓reduceIte] at hp
          exact hwt.self_loop_only_empty u p hp
      rmap_has_type := by
        intro r' bt' loc' path' hrmap hcond
        apply hwt.rmap_has_type r' bt' loc' path' hrmap
        rcases hcond with ⟨x, bk', ms, hvar⟩ | ⟨s', bk', hsite⟩
        · exact Or.inl ⟨x, bk', ms, hvar⟩
        · rw [hse_empty s'] at hsite; exact absurd hsite nofun
      funEnv_sig_consistent := hwt.funEnv_sig_consistent
      refs_tracked_mapped := by
        intro ref href
        change ref ∈ (delete_ref_node env.pathEnv r).refs at href
        simp only [delete_ref_node_refs, List.mem_filter, decide_eq_true_eq] at href
        exact hwt.refs_tracked_mapped ref href.1
      lenv_labels_in_blocks := hwt.lenv_labels_in_blocks
      has_return_info := hwt.has_return_info
      varStore_locs_bound := hwt.varStore_locs_bound
    }

-- ============================================================
-- Part 8b: Main Preservation Theorem (dispatches to case lemmas)
-- ============================================================

theorem preservation (m m' : Machine) (env : TypeEnv) (lenv : LabelEnv)
    (retTypes : List ParamType) (rmap : RefMap)
    (hwt : WellTypedState m env lenv retTypes rmap)
    (hss : StackSafe env.enumEnv m.stack m.frame.returnInfo m.heap retTypes)
    (hstep : step (.running m) = .running m') :
    ∃ env' lenv' retTypes' rmap',
      env'.enumEnv = env.enumEnv ∧ WellTypedState m' env' lenv' retTypes' rmap' ∧
      StackSafe env.enumEnv m'.stack m'.frame.returnInfo m'.heap retTypes' := by
  cases hstmt : m.frame.stmt with
  | skip =>
    exfalso; simp only [step, hstmt] at hstep
    split at hstep <;> simp at hstep
  | abort msg =>
    exfalso; simp only [step, hstmt] at hstep; contradiction
  | letBind s expr cont =>
    cases expr with
    | intLit n => exact preservation_intLit m m' env lenv retTypes rmap hwt hss s n cont hstmt hstep
    | usage u =>
      cases u with
      | copy x =>
        rcases inv_copy (by rw [← hstmt]; exact hwt.stmt_typed) with
          ⟨bt, ms, hvar, hcont⟩ | ⟨τ_ref, ms, s_orig, t, isBor, hvar, hfresh_t, hcont⟩
        · exact preservation_copy_val m m' env lenv retTypes rmap hwt hss s x cont bt ms hstmt hvar hcont hstep
        · exact preservation_copy_ref m m' env lenv retTypes rmap hwt hss s x cont
            τ_ref ms s_orig t isBor hvar hfresh_t hcont hstmt hstep
      | move x => exact preservation_move m m' env lenv retTypes rmap hwt hss s x cont hstmt hstep
      | borrowImm x => exact preservation_borrowImm m m' env lenv retTypes rmap hwt hss s x cont hstmt hstep
      | borrowMut x => exact preservation_borrowMut m m' env lenv retTypes rmap hwt hss s x cont hstmt hstep
    | borrowField src bt field => exact preservation_borrowFieldImm m m' env lenv retTypes rmap hwt hss s src bt field cont hstmt hstep
    | borrowMutField src bt field => exact preservation_borrowMutField m m' env lenv retTypes rmap hwt hss s src bt field cont hstmt hstep
    | readRef src => exact preservation_readRef m m' env lenv retTypes rmap hwt hss s src cont hstmt hstep
    | freeze src => exact preservation_freeze m m' env lenv retTypes rmap hwt hss s src cont hstmt hstep
    | pack name fieldSites => exact preservation_pack m m' env lenv retTypes rmap hwt hss s name fieldSites cont hstmt hstep
    | binop op a b => exact preservation_binop m m' env lenv retTypes rmap hwt hss s op a b cont hstmt hstep
    | unop op a => exact preservation_unop m m' env lenv retTypes rmap hwt hss s op a cont hstmt hstep
    -- Vector Expr operations
    | vecPack T elems => exact preservation_vecPack m m' env lenv retTypes rmap hwt hss s T elems cont hstmt hstep
    | vecLen src => exact preservation_vecLen m m' env lenv retTypes rmap hwt hss s src cont hstmt hstep
    | vecImmBorrow src idx => exact preservation_vecImmBorrow m m' env lenv retTypes rmap hwt hss s src idx cont hstmt hstep
    | vecMutBorrow src idx => exact preservation_vecMutBorrow m m' env lenv retTypes rmap hwt hss s src idx cont hstmt hstep
    | vecPopBack src => exact preservation_vecPopBack m m' env lenv retTypes rmap hwt hss s src cont hstmt hstep
    -- Enum Expr operations (packVariant follows same pattern as pack)
    | packVariant ename vname fieldSites =>
      exact preservation_packVariant m m' env lenv retTypes rmap hwt hss s ename vname fieldSites cont hstmt hstep
  | release site cont => exact preservation_release m m' env lenv retTypes rmap hwt hss site cont hstmt hstep
  | assign x site cont =>
    rcases inv_assign (by rw [← hstmt]; exact hwt.stmt_typed) with
      ⟨ax, τ, ms, r, hvar, ha_type, hfresh, hnotin, hcont⟩ |
      ⟨τ_old, r_old, bk_old, τ', ms, hle, hvar, hsite, hcont⟩ |
      ⟨τ, τ', hvar, hsite, hcompat, hcont⟩ |
      ⟨isv, τ, hvar, hsite, hcont⟩
    · exact preservation_assign_valid m m' env lenv retTypes rmap hwt hss x site cont ax τ ms r
        hvar ha_type hfresh hnotin hcont hstmt hstep
    · exact preservation_assign_valid_ref m m' env lenv retTypes rmap hwt hss x site cont
        τ_old r_old bk_old τ' ms hle hvar hsite hcont hstmt hstep
    · exact preservation_assign_invalid m m' env lenv retTypes rmap hwt hss x site cont τ τ'
        hvar hsite hcompat hcont hstmt hstep
    · exact preservation_assign_overwrite_basic m m' env lenv retTypes rmap hwt hss x site cont
        isv τ hvar hsite hcont hstmt hstep
  | writeRef dst val cont => exact preservation_writeRef m m' env lenv retTypes rmap hwt hss dst val cont hstmt hstep
  | unpack fields src cont => exact preservation_unpack m m' env lenv retTypes rmap hwt hss fields src cont hstmt hstep
  | jump label => exact preservation_jump m m' env lenv retTypes rmap hwt hss label hstmt hstep
  | branch c l1 l2 => exact preservation_branch m m' env lenv retTypes rmap hwt hss c l1 l2 hstmt hstep
  | ret sites => exact preservation_ret m m' env lenv retTypes rmap hwt hss sites hstmt hstep
  | call results fname argSites cont => exact preservation_call m m' env lenv retTypes rmap hwt hss results fname argSites cont hstmt hstep
  -- Vector Stmt operations
  | vecUnpack T results src cont => exact preservation_vecUnpack m m' env lenv retTypes rmap hwt hss T results src cont hstmt hstep
  | vecPushBack refSite val cont => exact preservation_vecPushBack m m' env lenv retTypes rmap hwt hss refSite val cont hstmt hstep
  | vecSwap refSite idx1 idx2 cont => exact preservation_vecSwap m m' env lenv retTypes rmap hwt hss refSite idx1 idx2 cont hstmt hstep
  -- Enum Stmt operations
  | unpackVariant vname fields src cont => exact preservation_unpackVariant m m' env lenv retTypes rmap hwt hss vname fields src cont hstmt hstep
  | variantSwitch src cases_list => exact preservation_variantSwitch m m' env lenv retTypes rmap hwt hss src cases_list hstmt hstep

end LeanMove.Typing.TypeSoundness
