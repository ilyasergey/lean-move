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

import LeanMove.Structures.AssocMap

/-!
# Decidable Equality for MoveLight Types

This file contains the core MoveLight types that require custom boolean equality
implementations (due to nested inductive types), along with their soundness/completeness
proofs and DecidableEq instances.

## Contents
- `Field`, `BasicMoveType` - Basic types with custom beq for records
- `Var`, `Aref`, `BorrowingKind`, `MoveType` - Move type system types
- Boolean equality functions with reflexivity, soundness, and completeness proofs
- `DecidableEq` instances derived from these proofs

The remaining language constructs (Site, Expr, Stmt, etc.) are defined in MoveLight.lean.
-/

namespace LeanMove.Lang.MoveLight

open AssocMap

-- Forward declarations of types (defined in MoveLight.lean, but we need to define beq here)
-- These are re-exports to avoid circular imports

-- Field names for structs
structure Field where
  id: String
deriving Repr, DecidableEq, Inhabited, Hashable

inductive BasicMoveType where
  | u64   -- Unsigned 64-bit integer
  | tbool
  | tunit
  | trecord : AssocMap Field BasicMoveType → BasicMoveType

/- ---------------------------------------------------- -/
/-       BasicMoveType Equality                          -/
/- ---------------------------------------------------- -/

-- Records are equal iff they have exactly the same entries list (same order)
def BasicMoveType.beq : BasicMoveType → BasicMoveType → Bool
  | .u64, .u64 => true
  | .tbool, .tbool => true
  | .tunit, .tunit => true
  | .trecord m1, .trecord m2 => beqEntries m1.entries m2.entries
  | _, _ => false
where
  beqEntries : List (Field × BasicMoveType) → List (Field × BasicMoveType) → Bool
    | [], [] => true
    | (f1, t1) :: rest1, (f2, t2) :: rest2 =>
      f1 == f2 && t1.beq t2 && beqEntries rest1 rest2
    | _, _ => false

-- Derive instances after beq is defined
deriving instance Repr, Inhabited, Hashable for BasicMoveType

instance : BEq BasicMoveType := ⟨BasicMoveType.beq⟩

-- Prove reflexivity and soundness together using mutual recursion
mutual
  theorem BasicMoveType.beqEntries_refl : ∀ (es : List (Field × BasicMoveType)),
      BasicMoveType.beq.beqEntries es es = true
    | [] => rfl
    | (f, t) :: rest => by
      simp only [BasicMoveType.beq.beqEntries, beq_self_eq_true, Bool.true_and, Bool.and_eq_true]
      exact And.intro (BasicMoveType.beq_refl t) (BasicMoveType.beqEntries_refl rest)

  theorem BasicMoveType.beq_refl : ∀ (t : BasicMoveType), t.beq t = true
    | .u64 => rfl
    | .tbool => rfl
    | .tunit => rfl
    | .trecord m => BasicMoveType.beqEntries_refl m.entries
end

mutual
  theorem BasicMoveType.eq_of_beqEntries : ∀ (es1 es2 : List (Field × BasicMoveType)),
      BasicMoveType.beq.beqEntries es1 es2 = true → es1 = es2
    | [], [], _ => rfl
    | [], _ :: _, h => by simp [BasicMoveType.beq.beqEntries] at h
    | _ :: _, [], h => by simp [BasicMoveType.beq.beqEntries] at h
    | (f1, t1) :: rest1, (f2, t2) :: rest2, h => by
      simp only [BasicMoveType.beq.beqEntries, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨hf, ht⟩, hrest⟩ := h
      have ht' : t1 = t2 := BasicMoveType.eq_of_beq t1 t2 ht
      have hrest' : rest1 = rest2 := BasicMoveType.eq_of_beqEntries rest1 rest2 hrest
      rw [hf, ht', hrest']

  theorem BasicMoveType.eq_of_beq : ∀ (t1 t2 : BasicMoveType), t1.beq t2 = true → t1 = t2
    | .u64, .u64, _ => rfl
    | .tbool, .tbool, _ => rfl
    | .tunit, .tunit, _ => rfl
    | .trecord m1, .trecord m2, h => by
      simp only [beq] at h
      have heq := BasicMoveType.eq_of_beqEntries m1.entries m2.entries h
      cases m1; cases m2
      simp only at heq
      rw [heq]
    | .u64, .tbool, h | .u64, .tunit, h | .u64, .trecord _, h => by simp [beq] at h
    | .tbool, .u64, h | .tbool, .tunit, h | .tbool, .trecord _, h => by simp [beq] at h
    | .tunit, .u64, h | .tunit, .tbool, h | .tunit, .trecord _, h => by simp [beq] at h
    | .trecord _, .u64, h | .trecord _, .tbool, h | .trecord _, .tunit, h => by simp [beq] at h
end

theorem BasicMoveType.beq_of_eq (t1 t2 : BasicMoveType) : t1 = t2 → t1.beq t2 = true := by
  intro h
  subst h
  exact BasicMoveType.beq_refl t1

instance : DecidableEq BasicMoveType := fun t1 t2 =>
  if h : t1.beq t2 then
    isTrue (BasicMoveType.eq_of_beq t1 t2 h)
  else
    isFalse (fun heq => h (BasicMoveType.beq_of_eq t1 t2 heq))

/- ---------------------------------------------------- -/
/-       MoveType Equality                               -/
/- ---------------------------------------------------- -/

-- Variables are just identifiers
structure Var where
  id: String
deriving Repr, DecidableEq, Inhabited, Hashable

-- Abstract references
inductive Aref where
  | root : Aref
  | refid : Nat → Aref
  | varRef : Var → Aref
deriving Repr, DecidableEq, Inhabited, Hashable

-- Borrowing kind: tracks only mutability, NOT provenance
inductive BorrowingKind where
  | siteBorrowImm : BorrowingKind
  | siteBorrowMut : BorrowingKind
deriving Repr, DecidableEq, Inhabited, Hashable

-- Types
inductive MoveType where
  | basic: BasicMoveType → MoveType
  | ref : BasicMoveType → Aref → BorrowingKind → MoveType
deriving Repr, Inhabited, Hashable

def MoveType.beq : MoveType → MoveType → Bool
  | .basic bt1, .basic bt2 => bt1.beq bt2
  | .ref bt1 r1 bk1, .ref bt2 r2 bk2 => bt1.beq bt2 && r1 == r2 && bk1 == bk2
  | _, _ => false

instance : BEq MoveType := ⟨MoveType.beq⟩

theorem MoveType.beq_refl : ∀ (t : MoveType), t.beq t = true
  | .basic bt => BasicMoveType.beq_refl bt
  | .ref bt r bk => by
    simp only [beq, BasicMoveType.beq_refl, beq_self_eq_true, Bool.and_self]

theorem MoveType.eq_of_beq : ∀ (t1 t2 : MoveType), t1.beq t2 = true → t1 = t2
  | .basic bt1, .basic bt2, h => by
    simp only [beq] at h
    rw [BasicMoveType.eq_of_beq bt1 bt2 h]
  | .ref bt1 r1 bk1, .ref bt2 r2 bk2, h => by
    simp only [beq, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨hbt, hr⟩, hbk⟩ := h
    rw [BasicMoveType.eq_of_beq bt1 bt2 hbt, hr, hbk]
  | .basic _, .ref _ _ _, h => by simp [beq] at h
  | .ref _ _ _, .basic _, h => by simp [beq] at h

theorem MoveType.beq_of_eq (t1 t2 : MoveType) : t1 = t2 → t1.beq t2 = true := by
  intro h
  subst h
  exact MoveType.beq_refl t1

instance : DecidableEq MoveType := fun t1 t2 =>
  if h : t1.beq t2 then
    isTrue (MoveType.eq_of_beq t1 t2 h)
  else
    isFalse (fun heq => h (MoveType.beq_of_eq t1 t2 heq))

end LeanMove.Lang.MoveLight
