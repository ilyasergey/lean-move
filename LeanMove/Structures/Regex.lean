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

import Ssreflect.Lang

namespace Regex

inductive Regex (α : Type) where
  | empty : Regex α
  | ε : Regex α
  | char : α → Regex α
  | dot : Regex α
  | union : Regex α → Regex α → Regex α
  | concat : Regex α → Regex α → Regex α
  | star : Regex α → Regex α
  -- Derivative
  -- TODO: Not sure if this is the right place for this
  | deriv : Regex α → α → Regex α

/-! ## Notation for Regex Constructors -/

-- Union: re₁ ∣ re₂
infixl:30 " ∣ " => Regex.union

-- Concatenation: re₁ ⬝ re₂
infixl:40 " ⬝ " => Regex.concat

-- Star: re★
postfix:max "★" => Regex.star

-- Derivative: ∂[a] re means the derivative of re with respect to a
notation "∂[" a "]" re => Regex.deriv re a

-- Character: ⌜a⌝ for Regex.char a
notation "⌜" a "⌝" => Regex.char a

-- Empty language
notation "∅ᵣ" => Regex.empty

-- Empty string (epsilon)
notation "εᵣ" => Regex.ε

-- Wildcard (dot)
notation "·ᵣ" => Regex.dot

-- extend a regular expression with a new sequence of characters
def extend (re: Regex α) (ax: List α) := List.foldl (fun re a => Regex.concat re (Regex.char a)) re ax
-- Infix syntax for extend using ∘
infixl:65 " ∘ " => extend

-- Take a derivative of a regex by a list of characters
def der (re: Regex α) (ax: List α) := List.foldl (fun re a => Regex.deriv re a) re ax

-- Interpretation
-- Defines the language (set of strings) accepted by a regex

-- Star matching defined inductively to avoid termination issues
inductive star_matches {α} [DecidableEq α] (re_match : List α → Prop) : List α → Prop where
  | nil : star_matches re_match []
  | cons : ∀ ax1 ax2, ax1 ≠ [] → re_match ax1 → star_matches re_match ax2 →
           star_matches re_match (ax1 ++ ax2)

def interpret_regex {α} [DecidableEq α] (re: Regex α) : List α → Prop :=
  match re with
  | .empty => fun _ ↦ False
  | .ε => fun ax ↦ ax = []
  | .char a => fun ax ↦ ax = [a]
  | .dot => fun ax ↦ ax.length = 1  -- matches any single character
  | .union re1 re2 => fun ax ↦ interpret_regex re1 ax ∨ interpret_regex re2 ax
  | .concat re1 re2 => fun ax ↦
      ∃ ax1 ax2, ax = ax1 ++ ax2 ∧
                interpret_regex re1 ax1 ∧
                interpret_regex re2 ax2
  | .star re => fun ax ↦ star_matches (interpret_regex re) ax
  -- Brzozowski derivative: ∂_a(r) matches w iff r matches a::w
  | .deriv re a => fun ax ↦ interpret_regex re (a :: ax)

-- Semantic brackets: ⟦ re ⟧ means interpret_regex re
notation "⟦" re "⟧" => interpret_regex re

/-! ## Test Lemmas

Concrete examples demonstrating the regex interpretation semantics.
We use `Nat` as the alphabet type for simplicity.
-/

section TestLemmas

-- ε matches only the empty string
example : ⟦ (εᵣ : Regex Nat) ⟧ [] := rfl
example : ¬ ⟦ (εᵣ : Regex Nat) ⟧ [1] := by simp [interpret_regex]
example : ¬ ⟦ (εᵣ : Regex Nat) ⟧ [1, 2] := by simp [interpret_regex]

-- empty matches nothing
example : ¬ ⟦ (∅ᵣ : Regex Nat) ⟧ [] := by simp [interpret_regex]
example : ¬ ⟦ (∅ᵣ : Regex Nat) ⟧ [1] := by simp [interpret_regex]

-- char a matches only [a]
example : ⟦ ⌜1⌝ ⟧ [1] := rfl
example : ¬ ⟦ ⌜1⌝ ⟧ [] := by simp [interpret_regex]
example : ¬ ⟦ ⌜1⌝ ⟧ [2] := by simp [interpret_regex]
example : ¬ ⟦ ⌜1⌝ ⟧ [1, 2] := by simp [interpret_regex]

-- dot matches any single character
example : ⟦ (·ᵣ : Regex Nat) ⟧ [1] := rfl
example : ⟦ (·ᵣ : Regex Nat) ⟧ [42] := rfl
example : ¬ ⟦ (·ᵣ : Regex Nat) ⟧ [] := by simp [interpret_regex]
example : ¬ ⟦ (·ᵣ : Regex Nat) ⟧ [1, 2] := by simp [interpret_regex]

-- union: (a | b) matches [a] or [b]
example : ⟦ ⌜1⌝ ∣ ⌜2⌝ ⟧ [1] := Or.inl rfl
example : ⟦ ⌜1⌝ ∣ ⌜2⌝ ⟧ [2] := Or.inr rfl
example : ¬ ⟦ ⌜1⌝ ∣ ⌜2⌝ ⟧ [3] := by simp [interpret_regex]

-- concat: ab matches [a, b]
example : ⟦ ⌜1⌝ ⬝ ⌜2⌝ ⟧ [1, 2] := by
  simp only [interpret_regex]
  exists [1], [2]

example : ¬ ⟦ ⌜1⌝ ⬝ ⌜2⌝ ⟧ [1] := by
  simp only [interpret_regex]
  intro ⟨ax1, ax2, heq, h1, h2⟩
  cases ax1 with
  | nil => simp at h1
  | cons a ax1' =>
    simp at h1
    obtain ⟨rfl, rfl⟩ := h1
    cases ax2 with
    | nil => simp at h2
    | cons b ax2' => simp at h2; simp [h2] at heq

-- star: a★ matches [], [a], [a,a], [a,a,a], ...
example : ⟦ ⌜1⌝★ ⟧ [] := star_matches.nil

example : ⟦ ⌜1⌝★ ⟧ [1] := by
  apply star_matches.cons [1] []
  · simp
  · rfl
  · exact star_matches.nil

example : ⟦ ⌜1⌝★ ⟧ [1, 1] := by
  apply star_matches.cons [1] [1]
  · simp
  · rfl
  · apply star_matches.cons [1] []
    · simp
    · rfl
    · exact star_matches.nil

example : ⟦ ⌜1⌝★ ⟧ [1, 1, 1] := by
  apply star_matches.cons [1] [1, 1]
  · simp
  · rfl
  · apply star_matches.cons [1] [1]
    · simp
    · rfl
    · apply star_matches.cons [1] []
      · simp
      · rfl
      · exact star_matches.nil

-- star doesn't match non-matching elements
example : ¬ ⟦ ⌜1⌝★ ⟧ [2] := by
  intro h
  -- h : star_matches (interpret_regex ⌜1⌝) [2]
  -- star_matches can only produce [2] via cons with ax1 ++ ax2 = [2]
  generalize hlist : [2] = lst at h
  induction h with
  | nil => simp at hlist
  | cons ax1 ax2 hne h1 _ _ =>
    -- ax1 ++ ax2 = [2], and h1 : interpret_regex ⌜1⌝ ax1, i.e., ax1 = [1]
    simp [interpret_regex] at h1
    subst h1
    -- Now ax1 = [1], so [1] ++ ax2 = [2], which is impossible
    simp at hlist

-- Brzozowski derivative: ∂[a] r matches w iff r matches a::w
-- ∂[1] ⌜1⌝ matches [] because ⌜1⌝ matches [1]
example : ⟦ ∂[1] ⌜1⌝ ⟧ [] := by simp only [interpret_regex]

-- ∂[2] ⌜1⌝ doesn't match [] because ⌜1⌝ doesn't match [2]
example : ¬ ⟦ ∂[2] ⌜1⌝ ⟧ [] := by
  simp only [interpret_regex]
  intro h; cases h

-- ∂[1] (⌜1⌝ ⬝ ⌜2⌝) matches [2] because ⌜1⌝ ⬝ ⌜2⌝ matches [1,2]
example : ⟦ ∂[1] (⌜1⌝ ⬝ ⌜2⌝) ⟧ [2] := by
  simp only [interpret_regex]
  exists [1], [2]

-- Multiple derivatives: ∂[2] (∂[1] (⌜1⌝ ⬝ ⌜2⌝)) matches [] because ⌜1⌝ ⬝ ⌜2⌝ matches [1,2]
example : ⟦ ∂[2] (∂[1] (⌜1⌝ ⬝ ⌜2⌝)) ⟧ [] := by
  simp only [interpret_regex]
  exists [1], [2]

-- ∂[1] ⌜1⌝★ matches any number of 1s (because ⌜1⌝★ matches 1 followed by any 1s)
example : ⟦ ∂[1] ⌜1⌝★ ⟧ [] := by
  simp only [interpret_regex]
  apply star_matches.cons [1] []
  · simp
  · rfl
  · exact star_matches.nil

example : ⟦ ∂[1] ⌜1⌝★ ⟧ [1] := by
  simp only [interpret_regex]
  apply star_matches.cons [1] [1]
  · simp
  · rfl
  · apply star_matches.cons [1] []
    · simp
    · rfl
    · exact star_matches.nil

end TestLemmas

end Regex
