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

namespace AssocMap

/-- Represents an associative map based on lists of pairs -/
structure AssocMap (K V : Type) where
  entries : List (K × V)

/-- Create an empty associative map -/
def empty {K V : Type} : AssocMap K V := {
  entries := []
}

/-- Insert a key-value pair into the map -/
def insert {K V : Type} [BEq K] (self : AssocMap K V) (key : K) (value : V) : AssocMap K V := {
  entries := (key, value) :: (self.entries.filter (fun (k, _) => k != key))
}

/-- Remove a key from the map -/
def delete {K V : Type} [BEq K] (self : AssocMap K V) (key : K) : AssocMap K V := {
  entries := (self.entries.filter (fun (k, _) => k != key))
}

/-- Search for a value by key -/
def lookup {K V : Type} [BEq K] (self : AssocMap K V) (key : K) : Option V :=
  match self.entries.find? (fun (k, _) => k == key) with
  | some (_, v) => some v
  | none => none


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

end AssocMap
