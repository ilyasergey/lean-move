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

import LeanMove.Checker.TypeChecking

/-!
# Type Checking Proofs for MoveLight

This file contains soundness proofs for the algorithmic type checking functions
defined in `TypeChecking.lean`.

## Contents
- `PathEnv.WellFormed` - Well-formedness predicate for PathEnv
- `PathEnv.init_wellformed` - Proof that initial PathEnv is well-formed
- `not_borrowed_bool_implies_not_borrowed` - Soundness of boolean borrow check
-/

namespace LeanMove.Checker

open Lang
open Lang.MoveLight
open AssocMap
open Regex

/- ---------------------------------------------------- -/
/-       Algorithmic helpers for soundness proofs        -/
/- ---------------------------------------------------- -/

/-- Boolean version of not_borrowed for algorithmic type checking.
    Checks only refs in pathEnv.refs (the live references). -/
def not_borrowed_bool (x: Var) (env: TypeEnv) : Bool :=
  env.pathEnv.refs.all fun r =>
    let regex := env.pathEnv.paths (.root, r)
    -- Check that the regex does not accept the single-element path [root_to_var x]
    -- For common regex forms, we can check this directly
    match regex with
    | .empty => true  -- empty regex accepts nothing
    | .ε => true      -- ε only accepts [], not [root_to_var x]
    | .char c => c != .root_to_var x  -- char c accepts [c], check it's not our path
    | _ => false  -- Conservative: for complex regexes, assume borrowed

/- ---------------------------------------------------- -/
/-       Theorems about freshRef and nextFreshRef        -/
/- ---------------------------------------------------- -/

theorem freshRef_iff_freshRefBool (r : Aref) (pe : PathEnv) :
    freshRef r pe ↔ freshRefBool r pe = true := by
  unfold freshRef freshRefBool
  simp only [Bool.not_eq_true', List.contains_eq_any_beq]
  constructor
  · intro hNotIn
    rw [List.any_eq_false]
    intro x hx hbeq
    have heq : r = x := beq_iff_eq.mp hbeq
    exact hNotIn (heq ▸ hx)
  · intro hAny hIn
    rw [List.any_eq_false] at hAny
    have := hAny r hIn
    have hbeq : (r == r) = true := beq_self_eq_true r
    exact this hbeq

/-- Helper lemma: foldl with max always produces result ≥ init -/
private lemma foldl_max_ge_init (l : List Aref) (init : Nat) :
    l.foldl (fun acc a => max acc (getRefId a)) init ≥ init := by
  induction l generalizing init with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons]
    exact Nat.le_trans (Nat.le_max_left _ _) (ih _)

/-- Helper lemma: foldl max is monotonic -/
private lemma foldl_max_ge_elem (l : List Aref) (init : Nat) (r : Aref) (hr : r ∈ l) :
    l.foldl (fun acc a => max acc (getRefId a)) init ≥ getRefId r := by
  induction l generalizing init with
  | nil => cases hr
  | cons x xs ih =>
    simp only [List.foldl_cons, List.mem_cons] at hr ⊢
    cases hr with
    | inl heq =>
      subst heq
      have h1 : max init (getRefId r) ≥ getRefId r := Nat.le_max_right _ _
      have h2 := foldl_max_ge_init xs (max init (getRefId r))
      exact Nat.le_trans h1 h2
    | inr htail =>
      exact ih (max init (getRefId x)) htail

/-- nextFreshRef always returns a fresh reference -/
theorem nextFreshRef_fresh (pe : PathEnv) : freshRefBool (nextFreshRef pe) pe = true := by
  unfold nextFreshRef freshRefBool
  simp only [Bool.not_eq_true', List.contains_eq_any_beq]
  rw [List.any_eq_false]
  intro r hr
  simp only [beq_iff_eq]
  intro heq
  have hmax := foldl_max_ge_elem pe.refs 0 r hr
  subst heq
  simp only [getRefId] at hmax
  omega

/- ---------------------------------------------------- -/
/-       Lemmas for PathEnv operations                   -/
/- ---------------------------------------------------- -/

/--
  When we delete a reference `r` from a PathEnv,
  the resulting refs list filters out `r`.
-/
lemma delete_ref_node_refs (pe : PathEnv) (r : Aref) :
    (delete_ref_node pe r).refs = List.filter (fun r' => r' ≠ r) pe.refs := by
  rfl

/--
  When we delete a reference `r`, all paths involving `r` become empty.
-/
lemma delete_ref_node_paths_involving_r (pe : PathEnv) (r : Aref) (u v : Aref) :
    u = r ∨ v = r → (delete_ref_node pe r).paths (u, v) = Regex.empty := by
  move=> h
  simp only [delete_ref_node]
  scase: h => hr
  · simp [hr]
  · simp [hr]

/--
  When we delete a reference `r`, paths not involving `r` are unchanged.
-/
lemma delete_ref_node_paths_not_involving_r (pe : PathEnv) (r : Aref) (u v : Aref) :
    u ≠ r → v ≠ r → (delete_ref_node pe r).paths (u, v) = pe.paths (u, v) := by
  move=> hu hv
  simp only [delete_ref_node]
  simp [hu, hv]

/--
  Deleting a reference `r ≠ .root` from a PathEnv with refs = [r, .root]
  gives refs = [.root].
-/
lemma delete_ref_node_restores_init_refs (pe : PathEnv) (r : Aref) (hr : r ≠ .root)
    (hrefs : pe.refs = [r, .root]) :
    (delete_ref_node pe r).refs = [.root] := by
  simp only [delete_ref_node, hrefs, List.filter]
  have h : Aref.root ≠ r := fun h => hr h.symm
  simp [h]

/-!
### PathEnv Equivalence After delete_ref_node

The lemma `delete_ref_node PathEnv.init r = PathEnv.init` is **NOT provable**
for syntactic equality because:

- `PathEnv.init.paths (r, r) = Regex.ε` for ANY `r` (the function returns ε when u = v)
- `(delete_ref_node PathEnv.init r).paths (r, r) = Regex.empty` (paths involving r are emptied)

These differ syntactically even though `r ∉ PathEnv.init.refs`.

**Solution implemented:** We weakened `TypeEnv.equiv` to only compare paths between
references that are in the refs list. This is semantically correct because paths
involving non-live references are irrelevant for borrow checking.

With this weaker equivalence, `delete_ref_node` on a PathEnv that was extended
from `PathEnv.init` correctly produces an equivalent PathEnv.
-/

/--
  For references u, v that are both in PathEnv.init.refs (i.e., both equal .root),
  delete_ref_node preserves the path value when r ≠ .root.
-/
lemma delete_ref_node_init_paths_between_roots (r : Aref) (hr : r ≠ .root) :
    (delete_ref_node PathEnv.init r).paths (.root, .root) = PathEnv.init.paths (.root, .root) := by
  simp only [delete_ref_node, PathEnv.init]
  have h1 : ¬(Aref.root = r) := fun h => hr h.symm
  simp [h1]

/--
  After deleting a fresh reference r ≠ .root from PathEnv.init,
  the refs list is [.root] (same as PathEnv.init.refs).
-/
lemma delete_ref_node_init_refs (r : Aref) (hr : r ≠ .root) :
    (delete_ref_node PathEnv.init r).refs = PathEnv.init.refs := by
  simp only [delete_ref_node, PathEnv.init, List.filter]
  have h : Aref.root ≠ r := fun h => hr h.symm
  simp [h]

/--
  Key lemma: For any PathEnv `pe`, after deleting `r`, the paths between
  remaining refs match the original paths. This is because `delete_ref_node`
  only modifies paths involving `r`, and refs remaining in the list are
  guaranteed to be different from `r`.
-/
lemma delete_ref_node_paths_between_remaining (pe : PathEnv) (r : Aref)
    (u v : Aref) (hu : u ∈ (delete_ref_node pe r).refs) (hv : v ∈ (delete_ref_node pe r).refs) :
    (delete_ref_node pe r).paths (u, v) = pe.paths (u, v) := by
  -- u and v are in the filtered refs, so u ≠ r and v ≠ r
  simp only [delete_ref_node_refs] at hu hv
  simp only [List.mem_filter, decide_eq_true_eq] at hu hv
  have hur : u ≠ r := hu.2
  have hvr : v ≠ r := hv.2
  exact delete_ref_node_paths_not_involving_r pe r u v hur hvr

/- ---------------------------------------------------- -/
/-       Soundness proofs for type checking              -/
/- ---------------------------------------------------- -/

/-- Helper: not_borrowed_bool being true implies not_borrowed for refs in pathEnv.refs
    when the regex has a simple form (empty, ε, or char). -/
lemma not_borrowed_bool_implies_not_borrowed_for_simple_regex (x : Var) (env : TypeEnv) :
    not_borrowed_bool x env = true →
    ∀ r ∈ env.pathEnv.refs,
      let regex := env.pathEnv.paths (.root, r)
      ¬interpret_regex regex [.root_to_var x] := by
  intro hbool r hr
  simp only [not_borrowed_bool, List.all_eq_true] at hbool
  have h := hbool r hr
  simp only at h
  split at h
  · -- regex = .empty
    rename_i heq
    simp only [heq, Regex.interpret_regex]
    exact fun a => a
  · -- regex = .ε
    rename_i heq
    simp only [heq, Regex.interpret_regex]
    intro hcontra
    cases hcontra
  · -- regex = .char c where c ≠ .root_to_var x
    rename_i c heq
    simp only [bne_iff_ne, ne_eq] at h
    simp only [heq, Regex.interpret_regex]
    intro hcontra
    -- hcontra : [.root_to_var x] = [c], so .root_to_var x = c
    have heq' : PathElement.root_to_var x = c := by
      injection hcontra
    exact h heq'.symm
  · -- complex regex - not_borrowed_bool returns false, contradiction
    simp at h

/-- A PathEnv is well-formed if refs not in the refs list have paths that don't accept
    any single-element path from root. This holds for PathEnvs constructed via the
    standard operations (init, update_with_extension, update_with_epsilon, etc.). -/
def PathEnv.WellFormed (pe : PathEnv) : Prop :=
  ∀ r, r ∉ pe.refs → ∀ p : PathElement, ¬interpret_regex (pe.paths (.root, r)) [p]

/-- PathEnv.init is well-formed: the only ref is .root, and paths from root to
    non-root refs are empty (which doesn't accept any path). -/
lemma PathEnv.init_wellformed : PathEnv.WellFormed PathEnv.init := by
  intro r hr p
  simp only [PathEnv.init, List.mem_singleton] at hr
  -- r ≠ .root, so paths (.root, r) = empty
  simp only [PathEnv.init]
  have hne : Aref.root ≠ r := fun h => hr h.symm
  simp only [hne, ↓reduceIte, Regex.interpret_regex]
  exact fun a => a

/-- For well-formed PathEnvs, not_borrowed_bool = true implies not_borrowed. -/
lemma not_borrowed_bool_implies_not_borrowed (x : Var) (env : TypeEnv)
    (hwf : PathEnv.WellFormed env.pathEnv) :
    not_borrowed_bool x env = true → not_borrowed x env := by
  intro hbool r
  by_cases hr : r ∈ env.pathEnv.refs
  · -- r is in refs: use the simple regex lemma
    exact not_borrowed_bool_implies_not_borrowed_for_simple_regex x env hbool r hr
  · -- r not in refs: use well-formedness
    exact hwf r hr (.root_to_var x)

/-- Helper: freshRefBool implies freshRef -/
lemma freshRefBool_implies_freshRef (r : Aref) (pe : PathEnv) :
    freshRefBool r pe = true → freshRef r pe := by
  intro h
  rw [freshRef_iff_freshRefBool]
  exact h

/-- Helper: nextFreshRef produces a fresh reference (propositional version) -/
lemma nextFreshRef_fresh_prop (pe : PathEnv) : freshRef (nextFreshRef pe) pe := by
  rw [freshRef_iff_freshRefBool]
  exact nextFreshRef_fresh pe

/-- Helper lemma for MoveType beq reflexivity -/
lemma MoveType.beq_refl (τ : MoveType) : MoveType.beq τ τ = true := by
  induction τ with
  | basic bt => simp [MoveType.beq, BasicMoveType.beq_refl]
  | ref bt r bk =>
    simp only [MoveType.beq]
    simp only [BasicMoveType.beq_refl, Bool.true_and, beq_self_eq_true, and_self]


end LeanMove.Checker
