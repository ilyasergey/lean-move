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
import Ssreflect.Lang
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
    | isTrue h => isTrue (by sby move: m1 m2 h=>[e1][e2])
    | isFalse h => isFalse (fun h' => h (by cases h'; rfl))

-- function to check that all keys are unique
def uniqueKeys {K V : Type} [DecidableEq K] (self : AssocMap K V) : Bool :=
  let keys := self.entries.map (fun (k, _) => k)
  keys.all (fun k => keys.countP (fun k' => k' == k) = 1)


theorem lookup_some {K V : Type} [DecidableEq K] (m : AssocMap K V) (k : K) (v : V) :
  lookup m k = some v → (k, v) ∈ m.entries := by
  move=>H1
  scase: m H1; elim=>//==; unfold lookup =>[|a b//== es Hi H1]
  { sdone }
  move: H1
  unfold lookup=>//==; simp [List.lookup]
  aesop


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

end AssocMap
