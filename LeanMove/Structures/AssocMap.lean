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

import Batteries.Data.HashMap
import Aesop
import Mathlib.Tactic.Convert

/-- Represents an associative map based on lists of pairs -/
structure AssocMap (K V : Type) where
  entries : List (K × V)

namespace AssocMap

/-- Create an empty associative map -/
def empty {K V : Type} : AssocMap K V := {
  entries := []
}

/-- Insert a key-value pair into the map -/
def insert {K V : Type} [DecidableEq K] (self : AssocMap K V) (key : K) (value : V) : AssocMap K V := {
  entries := (key, value) :: (self.entries.filter (fun (k, _) => k != key))
}

/-- Remove a key from the map -/
def delete {K V : Type} [DecidableEq K] (self : AssocMap K V) (key : K) : AssocMap K V := {
  entries := (self.entries.filter (fun (k, _) => k != key))
}

def deleteAll {K V : Type} [DecidableEq K] (self : AssocMap K V) (keys : List K) : AssocMap K V := {
  entries := self.entries.filter (fun (k, _) => k ∉ keys)
}

/-- Update a key-value pair in the map -/
def update {K V : Type} [DecidableEq K] (self : AssocMap K V) (key : K) (value : V) : AssocMap K V := {
  entries := (key, value) :: (self.entries.filter (fun (k, _) => k != key))
}

/-- Search for a value by key -/
def lookup {K V : Type} [DecidableEq K] (self : AssocMap K V) (key : K) : Option V :=
  List.lookup key self.entries

def notIn {K V : Type} [DecidableEq K] (self : AssocMap K V) (key : K) : Bool :=
  match self.entries.find? (fun (k, _) => k == key) with
  | some _ => false
  | none => true

/-- Check if the map is empty -/
def isEmpty {K V : Type} (self : AssocMap K V) : Bool :=
  self.entries.isEmpty

/-- Get the number of entries in the map -/
def size {K V : Type} (self : AssocMap K V) : Nat :=
  self.entries.length

instance {K V : Type} [Repr K] [Repr V] : Repr (AssocMap K V) where
  reprPrec m _ := "{" ++ (String.intercalate ", " (m.entries.map (fun (k, v) => reprStr k ++ " ↦ " ++ reprStr v))) ++ "}"

instance {K V : Type} [Hashable K] [Hashable V] : Hashable (AssocMap K V) where
  hash m := m.entries.foldl (fun acc (k, v) => mixHash acc (mixHash (hash k) (hash v))) 0

instance {K V : Type} [DecidableEq K] [DecidableEq V] : DecidableEq (AssocMap K V) :=
  fun m1 m2 =>
    match decEq m1.entries m2.entries with
    | isTrue h => isTrue (by cases m1; cases m2; congr)
    | isFalse h => isFalse (fun h' => h (by cases h'; rfl))

-- function to check that all keys are unique
def uniqueKeys {K V : Type} [DecidableEq K] (self : AssocMap K V) : Bool :=
  let keys := self.entries.map (fun (k, _) => k)
  keys.all (fun k => keys.countP (fun k' => k' == k) = 1)


theorem lookup_some {K V : Type} [DecidableEq K] (m : AssocMap K V) (k : K) (v : V) :
  lookup m k = some v → (k, v) ∈ m.entries := by
  rcases m with ⟨entries⟩
  simp only [lookup]
  intro h
  induction entries with
  | nil => simp [List.lookup] at h
  | cons hd tl ih =>
    simp only [List.lookup] at h
    obtain ⟨a, b⟩ := hd
    split at h
    · cases h; simp_all [BEq.beq]
    · exact List.Mem.tail _ (ih h)


theorem notIn_uniqueKeys_insert {K V : Type} [DecidableEq K] (m : AssocMap K V) (k : K) (v : V) :
  uniqueKeys m → notIn m k → uniqueKeys (insert m k v) := by
  unfold AssocMap.uniqueKeys;
  unfold AssocMap.notIn at * ; simp;
  unfold AssocMap.insert at * ; aesop (config := { warnOnNonterminal := false })
  rw [ List.countP_cons ] ; simp;
  rw [ List.countP_filter ] ; aesop (config := { warnOnNonterminal := false })
  convert a a_2 b left using 1;
  exact List.countP_congr fun x hx => by aesop;


/-- If a key is not in the map (via `notIn`), then `lookup` returns `none` -/
theorem notIn_implies_lookup_none {K V : Type} [DecidableEq K] (m : AssocMap K V) (k : K) :
    notIn m k = true → lookup m k = none := by
  rcases m with ⟨entries⟩
  simp only [notIn, lookup]
  induction entries with
  | nil => simp [List.find?, List.lookup]
  | cons hd rest ih =>
    intro h
    simp only [List.find?] at h
    by_cases hkk : hd.1 = k
    · subst hkk; simp at h
    · have h1 : (hd.1 == k) = false := by
        cases hb : hd.1 == k
        · rfl
        · exact absurd (beq_iff_eq.mp hb) hkk
      simp only [h1] at h
      have h2 : (k == hd.1) = false := by
        cases hb : k == hd.1
        · rfl
        · exact absurd (beq_iff_eq.mp hb).symm hkk
      show List.lookup k (hd :: rest) = none
      simp only [List.lookup, h2]
      exact ih h

/- ---------------------------------------------------- -/
/-       Lookup-based equivalence (order-independent)    -/
/- ---------------------------------------------------- -/

/-- Two maps are lookup-equivalent if every key maps to the same value in both.
    Unlike structural equality (`=`), this is insensitive to entry ordering. -/
def LookupEquiv {K V : Type} [DecidableEq K] (m1 m2 : AssocMap K V) : Prop :=
  ∀ k, lookup m1 k = lookup m2 k

/-- Boolean check for lookup equivalence: checks all keys from both maps. -/
def lookup_equiv_bool {K V : Type} [DecidableEq K] [DecidableEq V]
    (m1 m2 : AssocMap K V) : Bool :=
  m1.entries.all (fun p => decide (lookup m1 p.1 = lookup m2 p.1)) &&
  m2.entries.all (fun p => decide (lookup m1 p.1 = lookup m2 p.1))

theorem LookupEquiv.refl {K V : Type} [DecidableEq K] (m : AssocMap K V) :
    LookupEquiv m m :=
  fun _ => rfl

/-- If a key does not appear as a first component in the entries list,
    then lookup returns none. -/
theorem lookup_none_of_not_mem_keys {K V : Type} [DecidableEq K]
    (m : AssocMap K V) (k : K)
    (h : ∀ p ∈ m.entries, p.1 ≠ k) : lookup m k = none := by
  rcases m with ⟨entries⟩
  simp only [lookup]
  induction entries with
  | nil => simp [List.lookup]
  | cons hd rest ih =>
    simp only [List.lookup]
    have hne : hd.1 ≠ k := h hd (by simp)
    have hbeq : (k == hd.1) = false := by
      cases hb : k == hd.1
      · rfl
      · exact absurd (beq_iff_eq.mp hb).symm hne
    simp only [hbeq]
    exact ih (fun p hp => h p (by simp [hp]))

/-- Soundness: if the boolean check passes, lookup equivalence holds. -/
theorem lookup_equiv_bool_sound {K V : Type} [DecidableEq K] [DecidableEq V]
    (m1 m2 : AssocMap K V) :
    lookup_equiv_bool m1 m2 = true → LookupEquiv m1 m2 := by
  intro h
  simp only [lookup_equiv_bool, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  intro k
  by_cases hk1 : ∃ v, (k, v) ∈ m1.entries
  · -- k appears in m1: use h1
    obtain ⟨v, hv⟩ := hk1
    have := h1 (k, v) hv
    simp only [decide_eq_true_eq] at this
    exact this
  · by_cases hk2 : ∃ v, (k, v) ∈ m2.entries
    · -- k appears in m2 but not m1: use h2
      obtain ⟨v, hv⟩ := hk2
      have := h2 (k, v) hv
      simp only [decide_eq_true_eq] at this
      exact this
    · -- k in neither: both lookups are none
      have hk1' : ∀ p ∈ m1.entries, p.1 ≠ k := by
        intro ⟨k', v'⟩ hp heq; exact hk1 ⟨v', heq ▸ hp⟩
      have hk2' : ∀ p ∈ m2.entries, p.1 ≠ k := by
        intro ⟨k', v'⟩ hp heq; exact hk2 ⟨v', heq ▸ hp⟩
      rw [lookup_none_of_not_mem_keys m1 k hk1', lookup_none_of_not_mem_keys m2 k hk2']

/-- Completeness: if lookup equivalence holds, the boolean check passes. -/
theorem lookup_equiv_bool_complete {K V : Type} [DecidableEq K] [DecidableEq V]
    (m1 m2 : AssocMap K V) :
    LookupEquiv m1 m2 → lookup_equiv_bool m1 m2 = true := by
  intro h
  simp only [lookup_equiv_bool, Bool.and_eq_true, List.all_eq_true]
  constructor
  · intro p hp
    simp only [decide_eq_true_eq]
    exact h p.1
  · intro p hp
    simp only [decide_eq_true_eq]
    exact h p.1

/-- Helper: Bool.not / bne facts -/
private theorem beq_false_of_ne {K : Type} [DecidableEq K] {a b : K} (h : a ≠ b) :
    (a == b) = false := by
  cases hb : a == b
  · rfl
  · exact absurd (beq_iff_eq.mp hb) h

/-- Helper: filtering out entries with key `k` preserves lookup for key `k'` when `k' ≠ k` -/
private theorem list_lookup_filter_ne {K V : Type} [DecidableEq K]
    (entries : List (K × V)) (k k' : K) (hne : k' ≠ k) :
    List.lookup k' (entries.filter (fun p => p.1 != k)) = List.lookup k' entries := by
  induction entries with
  | nil => rfl
  | cons hd rest ih =>
    rcases hd with ⟨hk, hv⟩
    by_cases h : hk = k
    · -- filter removes (hk, hv) since hk = k and k != k = false
      rw [h]
      have hbne : (k != k) = false := by simp [bne]
      have hfilt : ((k, hv) :: rest).filter (fun p => p.fst != k)
          = rest.filter (fun p => p.fst != k) := by simp [List.filter]
      rw [hfilt, ih]
      simp only [List.lookup, beq_false_of_ne hne]
    · -- filter keeps (hk, hv) since hk ≠ k and hk != k = true
      have hbne : (hk != k) = true := by simp [bne, beq_false_of_ne h]
      have hfilt : ((hk, hv) :: rest).filter (fun p => p.fst != k)
          = (hk, hv) :: rest.filter (fun p => p.fst != k) := by simp [List.filter, hbne]
      rw [hfilt]; simp only [List.lookup]
      split <;> [rfl; exact ih]

/-- Helper: filtering out all entries with key `k` makes lookup `k` return none -/
private theorem list_lookup_filter_self {K V : Type} [DecidableEq K]
    (entries : List (K × V)) (k : K) :
    List.lookup k (entries.filter (fun p => p.1 != k)) = none := by
  induction entries with
  | nil => rfl
  | cons hd rest ih =>
    rcases hd with ⟨hk, hv⟩
    by_cases h : hk = k
    · rw [h]
      have hbne : (k != k) = false := by simp [bne]
      have hfilt : ((k, hv) :: rest).filter (fun p => p.fst != k)
          = rest.filter (fun p => p.fst != k) := by simp [List.filter]
      rw [hfilt]; exact ih
    · have hbne : (hk != k) = true := by simp [bne, beq_false_of_ne h]
      have hfilt : ((hk, hv) :: rest).filter (fun p => p.fst != k)
          = (hk, hv) :: rest.filter (fun p => p.fst != k) := by simp [List.filter, hbne]
      rw [hfilt]; simp only [List.lookup, beq_false_of_ne (Ne.symm h)]
      exact ih

/-- Looking up the inserted key returns the inserted value -/
theorem lookup_insert_same {K V : Type} [DecidableEq K] (m : AssocMap K V) (k : K) (v : V) :
    lookup (insert m k v) k = some v := by
  simp [lookup, insert]

/-- Looking up a different key is unaffected by insert -/
theorem lookup_insert_ne {K V : Type} [DecidableEq K] (m : AssocMap K V) (k k' : K) (v : V)
    (hne : k' ≠ k) : lookup (insert m k v) k' = lookup m k' := by
  simp only [lookup, insert, List.lookup]
  have hbeq : (k' == k) = false := by
    cases hb : k' == k; · rfl
    · exact absurd (beq_iff_eq.mp hb) hne
  simp only [hbeq]
  exact list_lookup_filter_ne m.entries k k' hne

/-- Looking up a deleted key returns none -/
theorem lookup_delete_same {K V : Type} [DecidableEq K] (m : AssocMap K V) (k : K) :
    lookup (delete m k) k = none := by
  simp only [lookup, delete]
  exact list_lookup_filter_self m.entries k

/-- Looking up a different key is unaffected by delete -/
theorem lookup_delete_ne {K V : Type} [DecidableEq K] (m : AssocMap K V) (k k' : K)
    (hne : k' ≠ k) : lookup (delete m k) k' = lookup m k' := by
  simp only [lookup, delete]
  exact list_lookup_filter_ne m.entries k k' hne

/-- Map a function over all values in the map, preserving keys -/
def mapValues {K V W : Type} (self : AssocMap K V) (f : V → W) : AssocMap K W := {
  entries := self.entries.map fun (k, v) => (k, f v)
}

/-- Helper: List.lookup commutes with mapping over values -/
private theorem list_lookup_map_snd {K V W : Type} [DecidableEq K]
    (l : List (K × V)) (f : V → W) (k : K) :
    List.lookup k (l.map fun (kv : K × V) => (kv.1, f kv.2)) = (List.lookup k l).map f := by
  induction l with
  | nil => simp [List.lookup]
  | cons hd tl ih =>
    obtain ⟨k', v⟩ := hd
    simp only [List.map, List.lookup]
    split
    · simp [Option.map]
    · exact ih

/-- Looking up in mapValues gives the mapped result -/
theorem lookup_mapValues {K V W : Type} [DecidableEq K]
    (m : AssocMap K V) (f : V → W) (k : K) :
    lookup (mapValues m f) k = (lookup m k).map f := by
  simp only [lookup, mapValues]
  exact list_lookup_map_snd m.entries f k

end AssocMap
