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


/-!
# List Utility Lemmas

Generic list manipulation lemmas used across the project.

## Contents
- `List.splits` — all ways to split a list into two parts
- `List.lookup_filter_*` — lookup behavior under filtering
- `List.filterMap_all_none` — filterMap when all elements map to none
- `List.eraseDups_length_le` — eraseDups doesn't increase length
- `List.nodup_of_length_eraseDups` — Nodup from length equality
- `List.nodup_snd_pair_absurd` — no duplicate second components
-/

/-! ## List Splits -/

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
    cases s with
    | nil => simp [List.splits]
    | cons b bs => simp [List.splits]
  | cons a s1' ih =>
    simp only [List.cons_append] at h; subst h
    simp only [List.splits, List.mem_cons, List.mem_map, Prod.exists]
    right
    refine ⟨s1', s2, ih (s1' ++ s2) rfl, ?_⟩
    simp

/-! ## List.lookup under filtering -/

/-- Lookup in filtered list implies lookup in original list (for keys not filtered) -/
theorem List.lookup_filter_of_lookup {K V : Type} [DecidableEq K] (entries : List (K × V))
    (k k' : K) (v : V) (hne : k ≠ k') :
    List.lookup k (entries.filter (fun p => p.1 != k')) = some v →
    List.lookup k entries = some v := by
  induction entries with
  | nil => simp [List.lookup]
  | cons hd tl ih =>
    intro h
    simp only [List.filter] at h
    simp only [List.lookup]
    by_cases hfilt : hd.1 != k'
    · simp only [hfilt, List.lookup] at h
      by_cases hhd : k == hd.1
      · simp only [hhd] at h ⊢; exact h
      · simp only [hhd] at h ⊢; exact ih h
    · simp only [bne_iff_ne, ne_eq, Classical.not_not] at hfilt
      simp only [hfilt, bne_self_eq_false] at h
      by_cases hhd : k == hd.1
      · simp only [beq_iff_eq] at hhd
        subst hhd
        exact absurd hfilt hne
      · simp only [hhd]
        exact ih h

/-- Looking up a key in a list filtered to remove that key returns none -/
theorem List.lookup_filter_self_none {K V : Type} [DecidableEq K] (entries : List (K × V)) (k : K) :
    List.lookup k (entries.filter (fun p => p.1 != k)) = none := by
  induction entries with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.filter]
    by_cases hfilt : hd.1 != k
    · simp only [hfilt, List.lookup]
      by_cases hhd : k == hd.1
      · simp only [beq_iff_eq] at hhd
        simp only [bne_iff_ne] at hfilt
        exact absurd hhd.symm hfilt
      · simp only [hhd]
        exact ih
    · simp only [bne_iff_ne, ne_eq, Classical.not_not] at hfilt
      have hfilt' : (hd.1 != k) = false := by simp [hfilt]
      simp only [hfilt']
      exact ih

/-- Looking up a key that's in the filter list returns none -/
theorem List.lookup_filter_mem_none {K V : Type} [DecidableEq K] (entries : List (K × V)) (k : K) (ks : List K) :
    k ∈ ks → List.lookup k (entries.filter (fun p => p.1 ∉ ks)) = none := by
  intro hmem
  induction entries with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.filter]
    by_cases hfilt : hd.1 ∉ ks
    · have hfilt' : decide (hd.1 ∉ ks) = true := decide_eq_true hfilt
      simp only [hfilt', List.lookup]
      by_cases hhd : k == hd.1
      · simp only [beq_iff_eq] at hhd
        exact absurd (hhd ▸ hmem) hfilt
      · simp only [hhd]
        exact ih
    · simp only [Classical.not_not] at hfilt
      have hfilt' : decide (hd.1 ∉ ks) = false := decide_eq_false (Classical.not_not.mpr hfilt)
      simp only [hfilt']
      exact ih

/-- Lookup in filtered list (key not filtered) gives same result as original -/
theorem List.lookup_filter_ne {K V : Type} [DecidableEq K] (entries : List (K × V)) (k k' : K) (hne : k ≠ k') :
    List.lookup k (entries.filter (fun p => p.1 != k')) = List.lookup k entries := by
  induction entries with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.filter, List.lookup]
    by_cases hfilt : hd.1 != k'
    · simp only [hfilt, List.lookup]
      by_cases hhd : k == hd.1
      · simp only [hhd]
      · simp only [hhd]
        exact ih
    · simp only [bne_iff_ne, ne_eq, Classical.not_not] at hfilt
      have hfilt' : (hd.1 != k') = false := by simp [hfilt]
      simp only [hfilt']
      by_cases hhd : k == hd.1
      · simp only [beq_iff_eq] at hhd
        exact absurd (hfilt ▸ hhd) hne
      · simp only [hhd]
        exact ih

/-- Lookup in filtered list (key not in filter list) gives same result as original -/
theorem List.lookup_filter_notin {K V : Type} [DecidableEq K] (entries : List (K × V)) (k : K) (ks : List K) (hnotin : k ∉ ks) :
    List.lookup k (entries.filter (fun p => p.1 ∉ ks)) = List.lookup k entries := by
  induction entries with
  | nil => rfl
  | cons hd tl ih =>
    simp only [List.filter, List.lookup]
    by_cases hfilt : hd.1 ∉ ks
    · have hfilt' : decide (hd.1 ∉ ks) = true := decide_eq_true hfilt
      simp only [hfilt', List.lookup]
      by_cases hhd : k == hd.1
      · simp only [hhd]
      · simp only [hhd]
        exact ih
    · simp only [Classical.not_not] at hfilt
      have hfilt' : decide (hd.1 ∉ ks) = false := decide_eq_false (Classical.not_not.mpr hfilt)
      simp only [hfilt']
      by_cases hhd : k == hd.1
      · simp only [beq_iff_eq] at hhd
        exact absurd (hhd ▸ hfilt) hnotin
      · simp only [hhd]
        exact ih

/-! ## filterMap / eraseDups / Nodup helpers -/

/-- When all elements map to none, filterMap gives [] -/
theorem List.filterMap_all_none {α β : Type} (as : List α) (f : α → Option β)
    (hf : ∀ a ∈ as, f a = none) :
    as.filterMap f = [] := by
  induction as with
  | nil => simp
  | cons a as' ih =>
    have ha := hf a (List.Mem.head as')
    simp only [List.filterMap]
    rw [ha]
    exact ih (fun a' ha' => hf a' (List.mem_cons_of_mem a ha'))

/-- eraseDups.length ≤ length for any list -/
theorem List.eraseDups_length_le {α : Type} [BEq α] [LawfulBEq α] (l : List α) :
    l.eraseDups.length ≤ l.length := by
  suffices ∀ n (l : List α), l.length ≤ n → l.eraseDups.length ≤ l.length from
    this l.length l (Nat.le_refl _)
  intro n
  induction n with
  | zero =>
    intro l hlen
    match l with
    | [] => simp
    | _ :: _ => simp [List.length_cons] at hlen
  | succ n ih =>
    intro l hlen
    match l with
    | [] => simp
    | a :: as =>
      simp only [List.eraseDups_cons, List.length_cons]
      have hfilt_le : (as.filter fun b => !(b == a)).length ≤ n := by
        have h := List.length_filter_le (fun b => !(b == a)) as
        simp only [List.length_cons] at hlen
        omega
      have h1 := ih (as.filter fun b => !(b == a)) hfilt_le
      have h2 := List.length_filter_le (fun b => !(b == a)) as
      omega

/-- If filter p preserves list length, then all elements satisfy p -/
theorem List.filter_length_eq_implies {α : Type} [BEq α] [LawfulBEq α]
    (p : α → Bool) (l : List α) (hlen : (l.filter p).length = l.length)
    (a : α) (hmem : a ∈ l) : p a = true := by
  induction l with
  | nil => nomatch hmem
  | cons b bs ih =>
    simp only [List.filter_cons] at hlen
    split at hlen
    · rename_i hpb
      simp only [List.length_cons] at hlen
      cases hmem with
      | head => exact hpb
      | tail _ hmem' => exact ih (by omega) hmem'
    · simp only [List.length_cons] at hlen
      have := List.length_filter_le p bs
      omega

/-- If length = eraseDups.length, then the list has no duplicates -/
theorem List.nodup_of_length_eraseDups {α : Type} [BEq α] [LawfulBEq α] (l : List α)
    (h : l.length = l.eraseDups.length) : l.Nodup := by
  induction l with
  | nil => exact List.nodup_nil
  | cons a as ih =>
    simp only [List.eraseDups_cons, List.length_cons] at h
    have h1 := List.eraseDups_length_le (as.filter fun b => !(b == a))
    have h2 := List.length_filter_le (fun b => !(b == a)) as
    have hflen : (as.filter fun b => !(b == a)).length = as.length := by omega
    have hnotmem : a ∉ as := by
      intro hmem
      have := List.filter_length_eq_implies (fun b => !(b == a)) as hflen a hmem
      simp at this
    have hfilter_eq : as.filter (fun b => !(b == a)) = as := by
      rw [List.filter_eq_self]
      intro b hmem
      have hne : b ≠ a := fun heq => hnotmem (heq ▸ hmem)
      simp [beq_eq_false_iff_ne.mpr hne]
    rw [hfilter_eq] at h
    exact List.nodup_cons.mpr ⟨hnotmem, ih (by omega)⟩

/-- If map Prod.snd has no duplicates, two pairs with same second component
    but different first components can't both be in the list -/
theorem List.nodup_snd_pair_absurd {α β : Type} (l : List (α × β))
    (hnodup : (l.map Prod.snd).Nodup)
    {a₁ a₂ : α} {b : β}
    (h₁ : (a₁, b) ∈ l) (h₂ : (a₂, b) ∈ l) (hne : a₁ ≠ a₂) : False := by
  induction l with
  | nil => nomatch h₁
  | cons hd tl ih =>
    simp only [List.map_cons, List.nodup_cons] at hnodup
    obtain ⟨hnotmem, htl_nodup⟩ := hnodup
    cases h₁ with
    | head =>
      cases h₂ with
      | head => exact hne rfl
      | tail _ h₂' =>
        exact absurd (List.mem_map_of_mem (f := Prod.snd) h₂') hnotmem
    | tail _ h₁' =>
      cases h₂ with
      | head =>
        exact absurd (List.mem_map_of_mem (f := Prod.snd) h₁') hnotmem
      | tail _ h₂' =>
        exact ih htl_nodup h₁' h₂'

/-- If `(l.map f).Nodup`, then `f` is injective on `l`. -/
theorem List.inj_on_of_nodup_map {α β : Type} {f : α → β} {l : List α}
    (hnd : (l.map f).Nodup) :
    ∀ x, x ∈ l → ∀ y, y ∈ l → f x = f y → x = y := by
  induction l with
  | nil => intros; contradiction
  | cons a as ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨hnotmem, htl_nodup⟩ := hnd
    intro x hx y hy hfxy
    cases hx with
    | head =>
      cases hy with
      | head => rfl
      | tail _ hy' =>
        exact absurd (hfxy ▸ List.mem_map_of_mem (f := f) hy') hnotmem
    | tail _ hx' =>
      cases hy with
      | head =>
        exact absurd (hfxy.symm ▸ List.mem_map_of_mem (f := f) hx') hnotmem
      | tail _ hy' =>
        exact ih htl_nodup x hx' y hy' hfxy

/-! ## Lookup on appended lists -/

/-- Lookup on append: if found in xs, found in xs ++ ys. -/
theorem lookup_append_left {α β : Type} [BEq α] (xs ys : List (α × β)) (k : α) (v : β)
    (h : xs.lookup k = some v) : (xs ++ ys).lookup k = some v := by
  induction xs with
  | nil => contradiction
  | cons hd tl ih =>
    obtain ⟨a, b⟩ := hd
    simp only [List.cons_append, List.lookup] at h ⊢
    cases heq : (k == a) with
    | false => simp only [heq] at h ⊢; exact ih h
    | true => simp only [heq] at h ⊢; exact h

/-- Lookup on append: if not found in xs, delegates to ys. -/
theorem lookup_append_right {α β : Type} [BEq α] (xs ys : List (α × β)) (k : α)
    (h : xs.lookup k = none) : (xs ++ ys).lookup k = ys.lookup k := by
  induction xs with
  | nil => simp
  | cons hd tl ih =>
    obtain ⟨a, b⟩ := hd
    simp only [List.cons_append, List.lookup] at h ⊢
    cases heq : (k == a) with
    | false => simp only [heq] at h ⊢; exact ih h
    | true => simp only [heq] at h; exact absurd h (by simp)

/-! ## Lookup transfer for mapped lists -/

/-- For two maps over the same base list with the same key function,
    if one has a non-none lookup, so does the other. -/
theorem list_map_lookup_transfer {α β : Type} {V1 V2 : Type} [BEq α]
    {base : List (α × β)}
    {key : α → β → α} {val1 : α → β → V1} {val2 : α → β → V2} {k : α}
    (h : (base.map fun (a, b) => (key a b, val1 a b)).lookup k ≠ none) :
    (base.map fun (a, b) => (key a b, val2 a b)).lookup k ≠ none := by
  induction base with
  | nil => simp at h
  | cons hd tl ih =>
    obtain ⟨x, y⟩ := hd
    simp only [List.map, List.lookup] at h ⊢
    cases heq : (k == key x y) with
    | false => simp only [heq] at h ⊢; exact ih h
    | true => simp only [heq] at h ⊢; exact Option.some_ne_none _

/-- For two maps over the same base with the same key function,
    successful lookups correspond to the same base element. -/
theorem list_map_lookup_pair {α β : Type} {V1 V2 : Type} [BEq α] [LawfulBEq α]
    {base : List (α × β)}
    {key : α → β → α} {val1 : α → β → V1} {val2 : α → β → V2} {k : α}
    {v1 : V1} {v2 : V2}
    (h1 : (base.map fun (a, b) => (key a b, val1 a b)).lookup k = some v1)
    (h2 : (base.map fun (a, b) => (key a b, val2 a b)).lookup k = some v2) :
    ∃ a b, (a, b) ∈ base ∧ key a b = k ∧ v1 = val1 a b ∧ v2 = val2 a b := by
  induction base with
  | nil => simp at h1
  | cons hd tl ih =>
    obtain ⟨x, y⟩ := hd
    simp only [List.map, List.lookup] at h1 h2
    cases heq : (k == key x y) with
    | false =>
      simp only [heq] at h1 h2
      obtain ⟨a', b', hmem, hk, hv1, hv2⟩ := ih h1 h2
      exact ⟨a', b', .tail _ hmem, hk, hv1, hv2⟩
    | true =>
      simp only [heq, Option.some.injEq] at h1 h2
      exact ⟨x, y, .head _, (eq_of_beq heq).symm, h1.symm, h2.symm⟩

/-- Domain matching for flatMap of maps with the same key function. -/
theorem flatMap_map_lookup_transfer {α β γ δ : Type} {V1 V2 : Type} [BEq α]
    {outer : List (γ × δ)} {inner : γ → δ → List (α × β)}
    {key : γ → δ → α → β → α}
    {val1 : γ → δ → α → β → V1} {val2 : γ → δ → α → β → V2} {k : α}
    (h : (outer.flatMap fun (c, d) =>
      (inner c d).map fun (a, b) => (key c d a b, val1 c d a b)).lookup k ≠ none) :
    (outer.flatMap fun (c, d) =>
      (inner c d).map fun (a, b) => (key c d a b, val2 c d a b)).lookup k ≠ none := by
  induction outer with
  | nil => simp at h
  | cons hd tl ih =>
    obtain ⟨c, d⟩ := hd
    simp only [List.flatMap_cons] at h ⊢
    cases hleft : ((inner c d).map fun (a, b) => (key c d a b, val1 c d a b)).lookup k with
    | some v =>
      have hne : ((inner c d).map fun (a, b) => (key c d a b, val2 c d a b)).lookup k ≠ none :=
        list_map_lookup_transfer (by rw [hleft]; exact Option.some_ne_none _)
      obtain ⟨v2, hv2⟩ := Option.ne_none_iff_exists'.mp hne
      rw [lookup_append_left _ _ _ _ hv2]; exact Option.some_ne_none _
    | none =>
      rw [lookup_append_right _ _ _ hleft] at h
      cases hleft2 : ((inner c d).map fun (a, b) => (key c d a b, val2 c d a b)).lookup k with
      | none => rw [lookup_append_right _ _ _ hleft2]; exact ih h
      | some v' =>
        exfalso
        have hne2 : ((inner c d).map fun (a, b) => (key c d a b, val2 c d a b)).lookup k ≠ none := by
          rw [hleft2]; exact Option.some_ne_none _
        exact (list_map_lookup_transfer hne2) (by rw [hleft])

/-- Lookup correspondence for flatMap of maps with the same key function. -/
theorem flatMap_map_lookup_pair {α β γ δ : Type} {V1 V2 : Type} [BEq α] [LawfulBEq α]
    {outer : List (γ × δ)} {inner : γ → δ → List (α × β)}
    {key : γ → δ → α → β → α}
    {val1 : γ → δ → α → β → V1} {val2 : γ → δ → α → β → V2} {k : α}
    {v1 : V1} {v2 : V2}
    (h1 : (outer.flatMap fun (c, d) =>
      (inner c d).map fun (a, b) => (key c d a b, val1 c d a b)).lookup k = some v1)
    (h2 : (outer.flatMap fun (c, d) =>
      (inner c d).map fun (a, b) => (key c d a b, val2 c d a b)).lookup k = some v2) :
    ∃ c d a b, (c, d) ∈ outer ∧ (a, b) ∈ inner c d ∧
      key c d a b = k ∧ v1 = val1 c d a b ∧ v2 = val2 c d a b := by
  induction outer with
  | nil => simp at h1
  | cons hd tl ih =>
    obtain ⟨c, d⟩ := hd
    simp only [List.flatMap_cons] at h1 h2
    cases hleft1 : ((inner c d).map fun (a, b) => (key c d a b, val1 c d a b)).lookup k with
    | some v =>
      have h1' : v1 = v := by
        rw [lookup_append_left _ _ _ _ hleft1] at h1; exact Option.some.inj h1.symm
      have hne : ((inner c d).map fun (a, b) => (key c d a b, val2 c d a b)).lookup k ≠ none :=
        list_map_lookup_transfer (by rw [hleft1]; exact Option.some_ne_none _)
      obtain ⟨v2', hv2'⟩ := Option.ne_none_iff_exists'.mp hne
      have h2' : v2 = v2' := by
        rw [lookup_append_left _ _ _ _ hv2'] at h2; exact Option.some.inj h2.symm
      obtain ⟨a, b, hmem, hk, hv1e, hv2e⟩ := list_map_lookup_pair (h1' ▸ hleft1) (h2' ▸ hv2')
      exact ⟨c, d, a, b, .head _, hmem, hk, h1' ▸ hv1e, h2' ▸ hv2e⟩
    | none =>
      cases hleft2 : ((inner c d).map fun (a, b) => (key c d a b, val2 c d a b)).lookup k with
      | some v' =>
        exfalso
        have hne2 : ((inner c d).map fun (a, b) => (key c d a b, val2 c d a b)).lookup k ≠ none := by
          rw [hleft2]; exact Option.some_ne_none _
        exact (list_map_lookup_transfer hne2) (by rw [hleft1])
      | none =>
        rw [lookup_append_right _ _ _ hleft1] at h1
        rw [lookup_append_right _ _ _ hleft2] at h2
        obtain ⟨c', d', a, b, hmem, hinner, hk, hv1, hv2⟩ := ih h1 h2
        exact ⟨c', d', a, b, .tail _ hmem, hinner, hk, hv1, hv2⟩
