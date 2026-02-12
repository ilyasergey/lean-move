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

/-! ## Brzozowski Derivative Simplification -/

/-- Check if a regex is nullable (matches the empty string). -/
def nullable : Regex α → Bool
  | .empty => false
  | .ε => true
  | .char _ => false
  | .dot => false
  | .union r1 r2 => nullable r1 || nullable r2
  | .concat r1 r2 => nullable r1 && nullable r2
  | .star _ => true
  | .deriv _ _ => false  -- conservative

/-- Compute one step of Brzozowski derivative ∂_a(r).
    Assumes no .deriv constructors in input. -/
def brzozowski_step [DecidableEq α] (a : α) : Regex α → Regex α
  | .empty => .empty
  | .ε => .empty
  | .char b => if a == b then .ε else .empty
  | .dot => .ε
  | .union r1 r2 => .union (brzozowski_step a r1) (brzozowski_step a r2)
  | .concat r1 r2 =>
    let d1 := Regex.concat (brzozowski_step a r1) r2
    if nullable r1 then .union d1 (brzozowski_step a r2) else d1
  | .star r => Regex.concat (brzozowski_step a r) (Regex.star r)
  | .deriv _ _ => .empty  -- shouldn't happen after simplification; safe default

/-- Simplify a regex by computing all stored Brzozowski derivatives.
    The result contains no .deriv constructors. -/
def simplify [DecidableEq α] : Regex α → Regex α
  | .empty => .empty
  | .ε => .ε
  | .char a => .char a
  | .dot => .dot
  | .union r1 r2 => .union (simplify r1) (simplify r2)
  | .concat r1 r2 => .concat (simplify r1) (simplify r2)
  | .star r => .star (simplify r)
  | .deriv r a => brzozowski_step a (simplify r)

/-! ## Emptiness and Only-Matches-Empty Checks -/

/-- Check if a regex's language is empty (matches nothing at all).
    Sound: `is_empty r = true → ∀ s, ¬ ⟦ r ⟧ s`.
    Conservative for `deriv` (returns `is_empty` of the inner regex). -/
def is_empty : Regex α → Bool
  | .empty => true
  | .ε => false
  | .char _ => false
  | .dot => false
  | .union r1 r2 => is_empty r1 && is_empty r2
  | .concat r1 r2 => is_empty r1 || is_empty r2
  | .star _ => false
  | .deriv r _ => is_empty r

/-- Check if a regex only matches the empty string (or nothing at all),
    i.e., L(r) ⊆ {[]}.
    Sound: `only_matches_empty r = true → ∀ s, ⟦ r ⟧ s → s = []`.
    Uses `is_empty` in the `concat` case for completeness:
    if either operand has empty language, the concatenation matches nothing. -/
def only_matches_empty : Regex α → Bool
  | .empty => true
  | .ε => true
  | .char _ => false
  | .dot => false
  | .union r1 r2 => only_matches_empty r1 && only_matches_empty r2
  | .concat r1 r2 => is_empty r1 || is_empty r2 ||
      (only_matches_empty r1 && only_matches_empty r2)
  | .star r => only_matches_empty r
  | .deriv r _ => only_matches_empty r

/-- Check if a regex definitely matches at least one string (possibly empty).
    Sound: `is_nonempty r = true → ∃ s, ⟦ r ⟧ s`.
    Conservative for `deriv` (returns false).
    The `dot` case assumes a non-empty alphabet (always true for `PathElement`). -/
def is_nonempty : Regex α → Bool
  | .empty => false
  | .ε => true
  | .char _ => true
  | .dot => true
  | .union r1 r2 => is_nonempty r1 || is_nonempty r2
  | .concat r1 r2 => is_nonempty r1 && is_nonempty r2
  | .star _ => true
  | .deriv _ _ => false

/-- Check if a regex definitely matches at least one non-empty string.
    Sound: `has_nonempty_match r = true → ∃ s, s ≠ [] ∧ ⟦ r ⟧ s`.
    Uses `is_nonempty` in the `concat` case: one operand must have a non-empty match
    while the other must match something (possibly empty).
    Conservative for `deriv` (returns false). -/
def has_nonempty_match : Regex α → Bool
  | .empty => false
  | .ε => false
  | .char _ => true
  | .dot => true
  | .union r1 r2 => has_nonempty_match r1 || has_nonempty_match r2
  | .concat r1 r2 =>
      (has_nonempty_match r1 && is_nonempty r2) ||
      (is_nonempty r1 && has_nonempty_match r2)
  | .star r => has_nonempty_match r
  | .deriv _ _ => false

/-! ## Boolean Regex Matcher -/

/-- All ways to split a list into two parts whose concatenation equals the original list.
    For example, `splits [1,2]` returns `[([],[1,2]), ([1],[2]), ([1,2],[])]`. -/
def List.splits {α : Type} : List α → List (List α × List α)
  | [] => [([], [])]
  | a :: as => ([], a :: as) :: (List.splits as |>.map fun (l, r) => (a :: l, r))

/-- Every pair in `splits s` is a valid split of `s` -/
theorem List.splits_sound {α : Type} (s s1 s2 : List α) :
    (s1, s2) ∈ List.splits s → s = s1 ++ s2 := by
  induction s generalizing s1 s2 with
  | nil =>
    simp only [List.splits, List.mem_singleton, Prod.mk.injEq]
    intro ⟨h1, h2⟩; subst h1; subst h2; rfl
  | cons a as ih =>
    simp only [List.splits, List.mem_cons, Prod.mk.injEq, List.mem_map, Prod.exists]
    intro h
    cases h with
    | inl h =>
      obtain ⟨h1, h2⟩ := h; subst h1; subst h2; rfl
    | inr h =>
      obtain ⟨l, r, hmem, h1, h2⟩ := h
      subst h1; subst h2
      have := ih l r hmem
      simp only [this, List.cons_append]

/-- Every valid split of `s` appears in `splits s` -/
theorem List.splits_complete {α : Type} (s s1 s2 : List α) :
    s = s1 ++ s2 → (s1, s2) ∈ List.splits s := by
  intro h
  induction s1 generalizing s with
  | nil =>
    simp only [List.nil_append] at h; subst h
    -- Goal: ([], s) ∈ List.splits s
    cases s with
    | nil => simp [List.splits]
    | cons b bs => simp [List.splits]
  | cons a s1' ih =>
    simp only [List.cons_append] at h; subst h
    -- Goal: (a :: s1', s2) ∈ List.splits (a :: (s1' ++ s2))
    simp only [List.splits, List.mem_cons, List.mem_map, Prod.exists]
    right
    refine ⟨s1', s2, ih (s1' ++ s2) rfl, ?_⟩
    simp

/-- Boolean regex matcher. Returns `true` if the regex accepts the given string.
    Conservative for `star` and `deriv` (returns `true`), which is safe for completeness. -/
def match_bool [DecidableEq α] : Regex α → List α → Bool
  | .empty, _ => false
  | .ε, s => s == []
  | .char c, s => s == [c]
  | .dot, s => s.length == 1
  | .union re1 re2, s => match_bool re1 s || match_bool re2 s
  | .concat re1 re2, s =>
      (List.splits s).any fun p => match_bool re1 p.1 && match_bool re2 p.2
  | _, _ => true  -- conservative for star, deriv

/-- Completeness: if a regex semantically accepts a string, the boolean matcher returns true.
    This is the direction needed for `not_borrowed_bool_sound`. -/
theorem match_bool_complete [DecidableEq α] (re : Regex α) (s : List α) :
    interpret_regex re s → match_bool re s = true := by
  induction re generalizing s with
  | empty => simp [interpret_regex]
  | ε =>
    simp only [interpret_regex, match_bool]
    intro h; subst h; simp
  | char c =>
    simp only [interpret_regex, match_bool]
    intro h; subst h; simp
  | dot =>
    simp only [interpret_regex, match_bool]
    intro h; simp [h]
  | union re1 re2 ih1 ih2 =>
    simp only [interpret_regex, match_bool, Bool.or_eq_true]
    intro h
    cases h with
    | inl h => exact Or.inl (ih1 s h)
    | inr h => exact Or.inr (ih2 s h)
  | concat re1 re2 ih1 ih2 =>
    simp only [interpret_regex, match_bool]
    intro ⟨s1, s2, heq, h1, h2⟩
    rw [List.any_eq_true]
    refine ⟨(s1, s2), List.splits_complete s s1 s2 heq, ?_⟩
    simp only [Bool.and_eq_true]
    exact ⟨ih1 s1 h1, ih2 s2 h2⟩
  | star => simp [match_bool]
  | deriv => simp [match_bool]

/-! ## Boolean Regex Equality and Subsumption -/

/-- Boolean structural equality for Regex -/
def regexBeq [BEq α] (r s : Regex α) : Bool :=
  match r, s with
  | .empty, .empty => true
  | .ε, .ε => true
  | .char a, .char b => a == b
  | .dot, .dot => true
  | .union r1 r2, .union s1 s2 => regexBeq r1 s1 && regexBeq r2 s2
  | .concat r1 r2, .concat s1 s2 => regexBeq r1 s1 && regexBeq r2 s2
  | .star r, .star s => regexBeq r s
  | .deriv r a, .deriv s b => regexBeq r s && a == b
  | _, _ => false

theorem regexBeq_refl [BEq α] [LawfulBEq α] : ∀ (r : Regex α), regexBeq r r = true
  | .empty => rfl
  | .ε => rfl
  | .char a => beq_self_eq_true a
  | .dot => rfl
  | .union r1 r2 => by simp only [regexBeq, regexBeq_refl r1, regexBeq_refl r2, Bool.and_self]
  | .concat r1 r2 => by simp only [regexBeq, regexBeq_refl r1, regexBeq_refl r2, Bool.and_self]
  | .star r => regexBeq_refl r
  | .deriv r a => by simp only [regexBeq, regexBeq_refl r, beq_self_eq_true, Bool.and_self]

theorem regexBeq_eq [DecidableEq α] : ∀ (r1 r2 : Regex α), regexBeq r1 r2 = true → r1 = r2 := by
  intro r1
  induction r1 with
  | empty =>
    intro r2 h
    cases r2 <;> simp only [regexBeq, Bool.false_eq_true] at h
    rfl
  | ε =>
    intro r2 h
    cases r2 <;> simp only [regexBeq, Bool.false_eq_true] at h
    rfl
  | char a =>
    intro r2 h
    cases r2 <;> simp only [regexBeq, Bool.false_eq_true] at h
    simp only [beq_iff_eq] at h
    subst h
    rfl
  | dot =>
    intro r2 h
    cases r2 <;> simp only [regexBeq, Bool.false_eq_true] at h
    rfl
  | union r1a r1b ih1 ih2 =>
    intro r2 h
    cases r2 <;> simp only [regexBeq, Bool.false_eq_true] at h
    rename_i r2a r2b
    simp only [Bool.and_eq_true] at h
    rw [ih1 r2a h.1, ih2 r2b h.2]
  | concat r1a r1b ih1 ih2 =>
    intro r2 h
    cases r2 <;> simp only [regexBeq, Bool.false_eq_true] at h
    rename_i r2a r2b
    simp only [Bool.and_eq_true] at h
    rw [ih1 r2a h.1, ih2 r2b h.2]
  | star r1 ih =>
    intro r2 h
    cases r2 <;> simp only [regexBeq, Bool.false_eq_true] at h
    rename_i r2
    rw [ih r2 h]
  | deriv r1 a ih =>
    intro r2 h
    cases r2 <;> simp only [regexBeq, Bool.false_eq_true] at h
    rename_i r2 b
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    rw [ih r2 h.1, h.2]

theorem eq_regexBeq [DecidableEq α] : ∀ (r1 r2 : Regex α), r1 = r2 → regexBeq r1 r2 = true := by
  intro r1 r2 h
  subst h
  exact regexBeq_refl r1

/-- Conservative check: is L(r1) ⊆ L(r2)?
    Checks if r1 is syntactically equal to r2, or appears as an arm of r2's union tree,
    or r1 has an empty language. -/
def regexSubsumedBy [BEq α] : Regex α → Regex α → Bool
  | r1, .union s1 s2 => is_empty r1 || regexBeq r1 (.union s1 s2) ||
      regexSubsumedBy r1 s1 || regexSubsumedBy r1 s2
  | r1, r2 => is_empty r1 || regexBeq r1 r2

/-- Soundness of is_empty: if is_empty returns true, the language is empty. -/
theorem is_empty_sound [DecidableEq α] : ∀ (r : Regex α), is_empty r = true → ∀ s, ¬ interpret_regex r s := by
  intro r
  induction r with
  | empty => intro _ s h; exact h
  | ε => intro h; simp [is_empty] at h
  | char _ => intro h; simp [is_empty] at h
  | dot => intro h; simp [is_empty] at h
  | union r1 r2 ih1 ih2 =>
    intro h s hmatch
    simp only [is_empty, Bool.and_eq_true] at h
    simp only [interpret_regex] at hmatch
    cases hmatch with
    | inl h1 => exact ih1 h.1 s h1
    | inr h2 => exact ih2 h.2 s h2
  | concat r1 r2 ih1 ih2 =>
    intro h s hmatch
    simp only [is_empty, Bool.or_eq_true] at h
    simp only [interpret_regex] at hmatch
    obtain ⟨s1, s2, _, h1, h2⟩ := hmatch
    cases h with
    | inl h1e => exact ih1 h1e s1 h1
    | inr h2e => exact ih2 h2e s2 h2
  | star _ => intro h; simp [is_empty] at h
  | deriv r _ ih =>
    intro h s hmatch
    simp only [is_empty] at h
    simp only [interpret_regex] at hmatch
    exact ih h _ hmatch

/-- Soundness of regexSubsumedBy: if it returns true, L(r1) ⊆ L(r2). -/
theorem regexSubsumedBy_sound [DecidableEq α] (r1 : Regex α) :
    ∀ (r2 : Regex α), regexSubsumedBy r1 r2 = true →
    ∀ path, interpret_regex r1 path → interpret_regex r2 path := by
  intro r2
  induction r2 with
  | union s1 s2 ih1 ih2 =>
    intro h path hmatch
    simp only [regexSubsumedBy, Bool.or_eq_true] at h
    rcases h with ((hempty | hbeq) | hsub1) | hsub2
    · exact absurd hmatch (is_empty_sound r1 hempty path)
    · rw [regexBeq_eq r1 _ hbeq] at hmatch; exact hmatch
    · exact Or.inl (ih1 hsub1 path hmatch)
    · exact Or.inr (ih2 hsub2 path hmatch)
  | _ =>
    intro h path hmatch
    simp only [regexSubsumedBy, Bool.or_eq_true] at h
    rcases h with hempty | hbeq
    · exact absurd hmatch (is_empty_sound r1 hempty path)
    · rw [regexBeq_eq r1 _ hbeq] at hmatch; exact hmatch

end Regex
