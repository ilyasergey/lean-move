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

import LeanMove.Checker.Algorithmic.AlgorithmicTypingSoundness

/-!
# Algorithmic Typing Completeness for MoveLight

This file contains completeness proofs for the algorithmic type
checker defined in `TypeCheckingAlgorithmic.lean` with respect to the relational
specification in `TypeChecking.lean`.

## Main Results

- `check_stmt_complete`: Statement-level completeness
- `check_fun_complete`: If `typecheck_fun f lenv`, then `check_fun f lenv = true`
- `check_fun_equiv`: `check_fun f lenv = true ↔ typecheck_fun f lenv`

Soundness proofs are in `AlgorithmicTypingSoundness.lean`.
-/

namespace LeanMove.Checker

open Lang
open Lang.MoveLight
open AssocMap
open Regex

/- ---------------------------------------------------- -/
/-       Statement type checking completeness            -/
/- ---------------------------------------------------- -/

/-- Completeness: If the relational judgment holds, the algorithmic check succeeds.

    NOTE: This theorem has sorries for cases requiring:
    1. Completeness of no_locals_borrowed_bool
    2. Matching the exact fresh reference in the derivation with nextFreshRef
-/
theorem check_stmt_complete (lenv : LabelEnv) (env : TypeEnv) (s : Stmt) (retType : MoveType) :
    typecheck_stmt lenv env s retType → (check_stmt lenv env s retType).isSome = true := by
  intro h
  -- Induction on the typecheck_stmt derivation
  induction h with
  | skip => simp [check_stmt]

  | jump =>
    rename_i env' L envL hlookup hsubsumes
    simp only [check_stmt, hlookup]
    -- TODO: need subsumes_implies_subsumes_bool lemma
    sorry

  | branch =>
    rename_i env' a L1 L2 envL1 envL2 hbool hlookup1 hlookup2 hsubsumes1 hsubsumes2
    simp only [check_stmt, hbool, hlookup1, hlookup2]
    -- TODO: need subsumes_implies_subsumes_bool lemma
    sorry

  | ret =>
    simp only [check_stmt]
    -- Need completeness for no_locals_borrowed_bool
    sorry

  | abort =>
    rename_i env' a _ hlookup
    simp only [check_stmt, hlookup, Option.isSome_some]

  -- Non-terminal statements with continuations - all require sorries
  -- These cases need:
  -- 1. Completeness of not_borrowed_bool
  -- 2. The algorithmic checker uses nextFreshRef, while the derivation may use any fresh ref
  | let_bind_move => sorry
  | let_bind_copy_val => sorry
  | let_bind_copy_ref => sorry
  | let_bind_borrowImm => sorry
  | let_bind_borrowMut => sorry
  | let_bind_intLit => sorry
  | let_bind_borrowField => sorry
  | let_bind_borrowMutField => sorry
  | let_bind_binop => sorry
  | let_bind_readRef => sorry
  | let_bind_freeze => sorry
  | let_bind_pack => sorry
  | write_ref => sorry
  | var_assign_valid => sorry
  | var_assign_invalid => sorry
  | call => sorry
  | release => sorry
  | unpack => sorry

/- ---------------------------------------------------- -/
/-       Function type checking completeness             -/
/- ---------------------------------------------------- -/

/-- Completeness: If the relational judgment holds, the algorithmic check succeeds -/
theorem check_fun_complete (f : FunDef) (lenv : LabelEnv) :
    typecheck_fun f lenv → check_fun f lenv = true := by
  intro h
  cases h with
  | fun_ok initEnv hvarEnv hsiteEnv hpathEnv hnonempty hentry hblocks =>
    simp only [check_fun]
    cases hblocks_eq : f.blocks with
    | nil => exact absurd hblocks_eq hnonempty
    | cons entry rest =>
      cases hlookup : lookup lenv entry.label with
      | none =>
        exfalso
        have hentry_in : entry ∈ f.blocks := by simp [hblocks_eq]
        have htc := hblocks entry hentry_in
        -- Need to show contradiction: htc requires some blockEnv but hlookup = none
        -- The hblocks hypothesis is ∀ blockEnv, lookup = some blockEnv → ...
        -- which is vacuously true when lookup = none
        -- But we need the entry block to have an environment in lenv
        -- This follows from hentry which requires lookup lenv entryLabel = some entryEnv
        have hhead : f.blocks.head? = some ⟨entry.label, entry.body⟩ := by simp [hblocks_eq]
        -- hentry gives us that for the entry, there exists entryEnv in lenv
        -- but hlookup says there's none - contradiction via hentry usage
        sorry -- Requires careful handling of the entry block requirement
      | some entryEnv =>
        simp only [hlookup, Bool.and_eq_true, List.all_eq_true]
        constructor
        · have hequiv := hentry entry.label entry.body entryEnv (by simp [hblocks_eq]) hlookup
          -- hequiv : TypeEnv.equiv entryEnv initEnv
          -- initEnv.siteEnv = empty, initEnv.varEnv = init_fun_varEnv f, initEnv.pathEnv = PathEnv.init
          obtain ⟨h1, h2, h3, h4⟩ := hequiv
          -- Rewrite using the equalities about initEnv
          have hequiv' : TypeEnv.equiv entryEnv
              { siteEnv := AssocMap.empty, varEnv := init_fun_varEnv f,
                pathEnv := PathEnv.init, funEnv := AssocMap.empty } := by
            refine ⟨?_, ?_, ?_, ?_⟩
            · simp only [hsiteEnv] at h1; exact h1
            · simp only [hvarEnv] at h2; exact h2
            · simp only [hpathEnv] at h3; exact h3
            · intro u v hu hv
              simp only [hpathEnv] at h4
              exact h4 u v hu hv
          exact TypeEnv.equiv_implies_equiv_bool _ _ hequiv'
        · intro block hblock
          have hblock_in : block ∈ f.blocks := by
            simp only [hblocks_eq, List.mem_cons] at hblock ⊢
            exact hblock
          simp only [check_block]
          cases hblockLookup : lookup lenv block.label with
          | none =>
            exfalso
            have htc := hblocks block hblock_in
            -- Similar issue - htc is vacuously true when lookup = none
            sorry
          | some blockEnv =>
            have htc := hblocks block hblock_in blockEnv hblockLookup
            -- Statement-level completeness requires per-case induction
            sorry

/-- Main equivalence theorem -/
theorem check_fun_equiv (f : FunDef) (lenv : LabelEnv)
    (hlenv_wf : ∀ l env, lookup lenv l = some env → TypeEnv.WellFormed env) :
    check_fun f lenv = true ↔ typecheck_fun f lenv :=
  ⟨check_fun_sound f lenv hlenv_wf, check_fun_complete f lenv⟩

end LeanMove.Checker
