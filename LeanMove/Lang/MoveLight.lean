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
import LeanMove.Structures.AssocMap

/- -----------------------------------------------------
 -       Definition of the Move Light language      --
 -----------------------------------------------------/

namespace LeanMove.Lang

open AssocMap

abbrev Id := String
abbrev Label := String

-- Sites: model linear stack slots in A-Normal form
inductive Site where
  | site : Nat → Site -- Temp site
  | root : Site -- Root site
deriving Repr, DecidableEq, Inhabited, Hashable

namespace MoveLight

/- ====================================================== -/
/-       Core MoveLight Types                              -/
/- ====================================================== -/

-- Field names for structs
structure Field where
  id: String
deriving Repr, DecidableEq, Inhabited, Hashable

/-- Qualify a field name with a variant name: "Variant.field" -/
def qualifyField (variantName : Id) (f : Field) : Field :=
  ⟨variantName ++ "." ++ f.id⟩

/-- Qualify all field names in an AssocMap with a variant name. -/
def qualifyFieldMap {α : Type} (variantName : Id) (m : AssocMap Field α) : AssocMap Field α :=
  ⟨m.entries.map fun (f, v) => (qualifyField variantName f, v)⟩

/-- The width of a Move unsigned integer type. Factored out of `BasicMoveType`
    deliberately: `BasicMoveType` is a *nested* inductive (`trecord` recurses
    through `AssocMap`), so it cannot derive `DecidableEq` and needs a
    hand-written `beq` with a full off-diagonal lemma table. Keeping the six
    widths in a separate flat enum means that table has a single `int`
    row/column regardless of how many widths Move grows. -/
inductive IntType where
  | u8 | u16 | u32 | u64 | u128 | u256
deriving Repr, DecidableEq, Inhabited, Hashable

/-- Bit width. `IntType.max w` is the exclusive upper bound of the type. -/
def IntType.bits : IntType → Nat
  | .u8 => 8 | .u16 => 16 | .u32 => 32
  | .u64 => 64 | .u128 => 128 | .u256 => 256

/-- One past the largest value of the type: `n : w` iff `n < IntType.max w`. -/
abbrev IntType.max (w : IntType) : Nat := 2 ^ w.bits

theorem IntType.max_pos (w : IntType) : 0 < w.max := Nat.two_pow_pos w.bits

inductive BasicMoveType where
  | int : IntType → BasicMoveType  -- Unsigned integer of the given width
  | tbool
  | tunit
  | trecord : AssocMap Field BasicMoveType → BasicMoveType
  | tvec : BasicMoveType → BasicMoveType
  | tenum : Id → BasicMoveType  -- Reference to enum name in EnumEnv

/-- `.u64` and `.u8` remain spellable, in both term *and* pattern position.
    `@[match_pattern]` is what makes the second half work: without it every
    `| .u64 => …` arm across the development would have to be rewritten to
    `| .int .u64 => …`. -/
@[match_pattern] abbrev BasicMoveType.u64 : BasicMoveType := .int .u64
@[match_pattern] abbrev BasicMoveType.u8 : BasicMoveType := .int .u8

/- ---------------------------------------------------- -/
/-       BasicMoveType Equality                          -/
/- ---------------------------------------------------- -/

-- Records are equal iff they have exactly the same entries list (same order)
mutual
  def BasicMoveType.beq : BasicMoveType → BasicMoveType → Bool
    | .int w1, .int w2 => w1 == w2
    | .tbool, .tbool => true
    | .tunit, .tunit => true
    | .trecord m1, .trecord m2 => BasicMoveType.beqEntries m1.entries m2.entries
    | .tvec t1, .tvec t2 => t1.beq t2
    | .tenum n1, .tenum n2 => n1 == n2
    | _, _ => false

  def BasicMoveType.beqEntries : List (Field × BasicMoveType) → List (Field × BasicMoveType) → Bool
    | [], [] => true
    | (f1, t1) :: rest1, (f2, t2) :: rest2 =>
      f1 == f2 && t1.beq t2 && BasicMoveType.beqEntries rest1 rest2
    | _, _ => false


end

-- Derive instances after beq is defined
deriving instance Repr, Inhabited, Hashable for BasicMoveType

instance : BEq BasicMoveType := ⟨BasicMoveType.beq⟩

-- Manual simp lemmas for BasicMoveType.beq (equational theorem generation
-- fails for mutual definitions over nested inductives in Lean 4.27)
@[simp] theorem BasicMoveType.beq_int_int (w1 w2 : IntType) :
    BasicMoveType.beq (.int w1) (.int w2) = (w1 == w2) := rfl
@[simp] theorem BasicMoveType.beq_tbool_tbool : BasicMoveType.beq .tbool .tbool = true := rfl
@[simp] theorem BasicMoveType.beq_tunit_tunit : BasicMoveType.beq .tunit .tunit = true := rfl
@[simp] theorem BasicMoveType.beq_trecord (m1 m2 : AssocMap Field BasicMoveType) :
    BasicMoveType.beq (.trecord m1) (.trecord m2) = BasicMoveType.beqEntries m1.entries m2.entries := rfl
@[simp] theorem BasicMoveType.beq_int_tbool (w) : BasicMoveType.beq (.int w) .tbool = false := rfl
@[simp] theorem BasicMoveType.beq_int_tunit (w) : BasicMoveType.beq (.int w) .tunit = false := rfl
@[simp] theorem BasicMoveType.beq_int_trecord (w m) : BasicMoveType.beq (.int w) (.trecord m) = false := rfl
@[simp] theorem BasicMoveType.beq_int_tvec (w t) : BasicMoveType.beq (.int w) (.tvec t) = false := rfl
@[simp] theorem BasicMoveType.beq_int_tenum (w n) : BasicMoveType.beq (.int w) (.tenum n) = false := rfl
@[simp] theorem BasicMoveType.beq_tbool_int (w) : BasicMoveType.beq .tbool (.int w) = false := rfl
@[simp] theorem BasicMoveType.beq_tbool_tunit : BasicMoveType.beq .tbool .tunit = false := rfl
@[simp] theorem BasicMoveType.beq_tbool_trecord (m) : BasicMoveType.beq .tbool (.trecord m) = false := rfl
@[simp] theorem BasicMoveType.beq_tbool_tvec (t) : BasicMoveType.beq .tbool (.tvec t) = false := rfl
@[simp] theorem BasicMoveType.beq_tbool_tenum (n) : BasicMoveType.beq .tbool (.tenum n) = false := rfl
@[simp] theorem BasicMoveType.beq_tunit_int (w) : BasicMoveType.beq .tunit (.int w) = false := rfl
@[simp] theorem BasicMoveType.beq_tunit_tbool : BasicMoveType.beq .tunit .tbool = false := rfl
@[simp] theorem BasicMoveType.beq_tunit_trecord (m) : BasicMoveType.beq .tunit (.trecord m) = false := rfl
@[simp] theorem BasicMoveType.beq_tunit_tvec (t) : BasicMoveType.beq .tunit (.tvec t) = false := rfl
@[simp] theorem BasicMoveType.beq_tunit_tenum (n) : BasicMoveType.beq .tunit (.tenum n) = false := rfl
@[simp] theorem BasicMoveType.beq_trecord_int (m w) : BasicMoveType.beq (.trecord m) (.int w) = false := rfl
@[simp] theorem BasicMoveType.beq_trecord_tbool (m) : BasicMoveType.beq (.trecord m) .tbool = false := rfl
@[simp] theorem BasicMoveType.beq_trecord_tunit (m) : BasicMoveType.beq (.trecord m) .tunit = false := rfl
@[simp] theorem BasicMoveType.beq_trecord_tvec (m t) : BasicMoveType.beq (.trecord m) (.tvec t) = false := rfl
@[simp] theorem BasicMoveType.beq_trecord_tenum (m n) : BasicMoveType.beq (.trecord m) (.tenum n) = false := rfl
@[simp] theorem BasicMoveType.beq_tvec (t1 t2 : BasicMoveType) :
    BasicMoveType.beq (.tvec t1) (.tvec t2) = t1.beq t2 := rfl
@[simp] theorem BasicMoveType.beq_tvec_int (t w) : BasicMoveType.beq (.tvec t) (.int w) = false := rfl
@[simp] theorem BasicMoveType.beq_tvec_tbool (t) : BasicMoveType.beq (.tvec t) .tbool = false := rfl
@[simp] theorem BasicMoveType.beq_tvec_tunit (t) : BasicMoveType.beq (.tvec t) .tunit = false := rfl
@[simp] theorem BasicMoveType.beq_tvec_trecord (t m) : BasicMoveType.beq (.tvec t) (.trecord m) = false := rfl
@[simp] theorem BasicMoveType.beq_tvec_tenum (t n) : BasicMoveType.beq (.tvec t) (.tenum n) = false := rfl
@[simp] theorem BasicMoveType.beq_tenum (n1 n2) :
    BasicMoveType.beq (.tenum n1) (.tenum n2) = (n1 == n2) := rfl
@[simp] theorem BasicMoveType.beq_tenum_int (n w) : BasicMoveType.beq (.tenum n) (.int w) = false := rfl
@[simp] theorem BasicMoveType.beq_tenum_tbool (n) : BasicMoveType.beq (.tenum n) .tbool = false := rfl
@[simp] theorem BasicMoveType.beq_tenum_tunit (n) : BasicMoveType.beq (.tenum n) .tunit = false := rfl
@[simp] theorem BasicMoveType.beq_tenum_trecord (n m) : BasicMoveType.beq (.tenum n) (.trecord m) = false := rfl
@[simp] theorem BasicMoveType.beq_tenum_tvec (n t) : BasicMoveType.beq (.tenum n) (.tvec t) = false := rfl

-- Manual simp lemmas for BasicMoveType.beqEntries
@[simp] theorem BasicMoveType.beqEntries_nil : BasicMoveType.beqEntries [] [] = true := rfl
@[simp] theorem BasicMoveType.beqEntries_nil_cons (hd tl) : BasicMoveType.beqEntries [] (hd :: tl) = false := rfl
@[simp] theorem BasicMoveType.beqEntries_cons_nil (hd tl) : BasicMoveType.beqEntries (hd :: tl) [] = false := rfl
@[simp] theorem BasicMoveType.beqEntries_cons (f1 t1 rest1 f2 t2 rest2) :
    BasicMoveType.beqEntries ((f1, t1) :: rest1) ((f2, t2) :: rest2) =
    (f1 == f2 && t1.beq t2 && BasicMoveType.beqEntries rest1 rest2) := rfl


-- Prove reflexivity and soundness together using mutual recursion
mutual
  theorem BasicMoveType.beqEntries_refl : ∀ (es : List (Field × BasicMoveType)),
      BasicMoveType.beqEntries es es = true
    | [] => rfl
    | (f, t) :: rest => by
      simp only [BasicMoveType.beqEntries_cons, beq_self_eq_true, Bool.true_and, Bool.and_eq_true]
      exact And.intro (BasicMoveType.beq_refl t) (BasicMoveType.beqEntries_refl rest)

  theorem BasicMoveType.beq_refl : ∀ (t : BasicMoveType), t.beq t = true
    | .int w => by simp only [BasicMoveType.beq_int_int, beq_self_eq_true]
    | .tbool => rfl
    | .tunit => rfl
    | .trecord m => BasicMoveType.beqEntries_refl m.entries
    | .tvec t => by simp only [BasicMoveType.beq_tvec]; exact BasicMoveType.beq_refl t
    | .tenum n => by simp only [BasicMoveType.beq_tenum, beq_self_eq_true]
end

mutual
  theorem BasicMoveType.eq_of_beqEntries : ∀ (es1 es2 : List (Field × BasicMoveType)),
        BasicMoveType.beqEntries es1 es2 = true → es1 = es2
      | [], [], _ => rfl
      | [], _ :: _, h => by simp at h
      | _ :: _, [], h => by simp at h
      | (f1, t1) :: rest1, (f2, t2) :: rest2, h => by
        simp only [BasicMoveType.beqEntries_cons, Bool.and_eq_true, beq_iff_eq] at h
        obtain ⟨⟨hf, ht⟩, hrest⟩ := h
        have ht' : t1 = t2 := BasicMoveType.eq_of_beq t1 t2 ht
        have hrest' : rest1 = rest2 := BasicMoveType.eq_of_beqEntries rest1 rest2 hrest
        rw [hf, ht', hrest']

  theorem BasicMoveType.eq_of_beq : ∀ (t1 t2 : BasicMoveType), t1.beq t2 = true → t1 = t2
    | .int w1, .int w2, h => by
      simp only [BasicMoveType.beq_int_int, beq_iff_eq] at h
      rw [h]
    | .tbool, .tbool, _ => rfl
    | .tunit, .tunit, _ => rfl
    | .trecord m1, .trecord m2, h => by
      simp only [BasicMoveType.beq_trecord] at h
      have heq := BasicMoveType.eq_of_beqEntries m1.entries m2.entries h
      cases m1; cases m2
      simp only at heq
      rw [heq]
    | .tvec t1, .tvec t2, h => by
      simp only [BasicMoveType.beq_tvec] at h
      rw [BasicMoveType.eq_of_beq t1 t2 h]
    | .tenum n1, .tenum n2, h => by
      simp only [BasicMoveType.beq_tenum, beq_iff_eq] at h
      rw [h]
    | .int _, .tbool, h | .int _, .tunit, h | .int _, .trecord _, h | .int _, .tvec _, h | .int _, .tenum _, h => by simp at h
    | .tbool, .int _, h | .tbool, .tunit, h | .tbool, .trecord _, h | .tbool, .tvec _, h | .tbool, .tenum _, h => by simp at h
    | .tunit, .int _, h | .tunit, .tbool, h | .tunit, .trecord _, h | .tunit, .tvec _, h | .tunit, .tenum _, h => by simp at h
    | .trecord _, .int _, h | .trecord _, .tbool, h | .trecord _, .tunit, h | .trecord _, .tvec _, h | .trecord _, .tenum _, h => by simp at h
    | .tvec _, .int _, h | .tvec _, .tbool, h | .tvec _, .tunit, h | .tvec _, .trecord _, h | .tvec _, .tenum _, h => by simp at h
    | .tenum _, .int _, h | .tenum _, .tbool, h | .tenum _, .tunit, h | .tenum _, .trecord _, h | .tenum _, .tvec _, h => by simp at h
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
/-       containsEnum: type transitively contains enum   -/
/- ---------------------------------------------------- -/

mutual
  def BasicMoveType.containsEnum : BasicMoveType → Bool
    | .tenum _ => true
    | .trecord fentries => BasicMoveType.containsEnumEntries fentries.entries
    | .tvec bt => BasicMoveType.containsEnum bt
    | _ => false

  def BasicMoveType.containsEnumEntries : List (Field × BasicMoveType) → Bool
    | [] => false
    | (_, bt) :: rest => BasicMoveType.containsEnum bt || BasicMoveType.containsEnumEntries rest
end

@[simp] theorem BasicMoveType.containsEnum_int (w : IntType) :
    BasicMoveType.containsEnum (.int w) = false := rfl
@[simp] theorem BasicMoveType.containsEnum_tbool : BasicMoveType.containsEnum .tbool = false := rfl
@[simp] theorem BasicMoveType.containsEnum_tunit : BasicMoveType.containsEnum .tunit = false := rfl
@[simp] theorem BasicMoveType.containsEnum_trecord (m : AssocMap Field BasicMoveType) :
    BasicMoveType.containsEnum (.trecord m) = BasicMoveType.containsEnumEntries m.entries := rfl
@[simp] theorem BasicMoveType.containsEnum_tvec (bt : BasicMoveType) :
    BasicMoveType.containsEnum (.tvec bt) = BasicMoveType.containsEnum bt := rfl
@[simp] theorem BasicMoveType.containsEnum_tenum (n : Id) :
    BasicMoveType.containsEnum (.tenum n) = true := rfl

/- ---------------------------------------------------- -/
/-       MoveType and Related Types                      -/
/- ---------------------------------------------------- -/

-- Variables are just identifiers
structure Var where
  id: String
deriving Repr, DecidableEq, Inhabited, Hashable

-- Abstract references
inductive Aref where
  | root : Aref
  | refid : Nat → Aref
  | paramRef : Var → Aref
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

/-- Two Arefs are compatible if neither is root, or both are root.
    All non-root arefs (.refid, .paramRef) are mutually compatible.
    This allows the checker to be agnostic to the exact aref values in declared types. -/
def Aref.compatible : Aref → Aref → Bool
  | .root, .root => true
  | .root, _ => false
  | _, .root => false
  | _, _ => true

def Aref.Compatible : Aref → Aref → Prop
  | .root, .root => True
  | .root, _ => False
  | _, .root => False
  | _, _ => True

theorem Aref.compatible_sound (a1 a2 : Aref) : a1.compatible a2 = true → a1.Compatible a2 := by
  cases a1 <;> cases a2 <;> simp [compatible, Compatible]

/-- Compatible MoveTypes: same structure but Arefs need only be kind-compatible.
    For basic types, requires equal BasicMoveType.
    For ref types, requires equal BasicMoveType, kind-compatible Arefs, and equal BorrowingKind. -/
def MoveType.compatible : MoveType → MoveType → Prop
  | .basic bt1, .basic bt2 => bt1 = bt2
  | .ref bt1 r1 bk1, .ref bt2 r2 bk2 => bt1 = bt2 ∧ Aref.Compatible r1 r2 ∧ bk1 = bk2
  | _, _ => False

def MoveType.compatible_bool : MoveType → MoveType → Bool
  | .basic bt1, .basic bt2 => bt1.beq bt2
  | .ref bt1 r1 bk1, .ref bt2 r2 bk2 => bt1.beq bt2 && Aref.compatible r1 r2 && bk1 == bk2
  | _, _ => false

theorem MoveType.compatible_bool_sound (t1 t2 : MoveType) :
    t1.compatible_bool t2 = true → t1.compatible t2 := by
  cases t1 with
  | basic bt1 =>
    cases t2 with
    | basic bt2 =>
      simp only [compatible_bool, compatible]
      exact BasicMoveType.eq_of_beq bt1 bt2
    | ref _ _ _ => simp [compatible_bool]
  | ref bt1 r1 bk1 =>
    cases t2 with
    | basic _ => simp [compatible_bool]
    | ref bt2 r2 bk2 =>
      simp only [compatible_bool, Bool.and_eq_true, beq_iff_eq, compatible]
      intro ⟨⟨hbt, hcompat⟩, hbk⟩
      exact ⟨BasicMoveType.eq_of_beq bt1 bt2 hbt, Aref.compatible_sound r1 r2 hcompat, hbk⟩

theorem MoveType.compatible_of_beq (t1 t2 : MoveType) :
    t1.beq t2 = true → t1.compatible t2 := by
  intro h
  have heq := MoveType.eq_of_beq t1 t2 h
  subst heq
  cases t1 with
  | basic bt => exact rfl
  | ref bt r bk =>
    refine ⟨rfl, ?_, rfl⟩
    cases r with
    | root => exact trivial
    | refid n => exact trivial
    | paramRef x => exact trivial

/- ====================================================== -/
/-       Language Constructs                               -/
/- ====================================================== -/

-- Variable Usage
inductive Usage where
  | copy : Var → Usage
  | move : Var → Usage
  | borrowImm : Var → Usage
  | borrowMut : Var → Usage
deriving Repr, DecidableEq, Inhabited, Hashable

-- Abstract locations (single-assign variables)
abbrev ALoc := Site

inductive Binop where
  | add
  | sub
  | mul
  | div
  | mod
  | eq
  | neq   -- Move bytecode `Neq`; like `Eq`, defined at every comparable type
  | lt
  | gt
  | le
  | ge
  | and   -- Move bytecode `And` (boolean conjunction, not `BitAnd`)
  | or    -- Move bytecode `Or` (boolean disjunction, not `BitOr`)
deriving Repr, DecidableEq, Inhabited, Hashable

/-- Unary operators. Currently only boolean negation, matching the Move
    bytecode `Not` instruction; the `Cast*` opcodes would slot in here. -/
inductive Unop where
  | not   -- Move bytecode `Not` (boolean negation)
deriving Repr, DecidableEq, Inhabited, Hashable

-- Expressions
inductive Expr where
  | usage : Usage → Expr
  | intLit : Nat → IntType → Expr  -- Integer literal; the Move `LdU8`…`LdU256` opcodes
  | borrowField : Site → BasicMoveType → Field → Expr  -- &a.T::f
  | borrowMutField : Site → BasicMoveType → Field → Expr  -- &mut a.T::f
  | binop : Binop → Site → Site → Expr  -- a + b
  | unop : Unop → Site → Expr  -- !a
  | readRef : Site → Expr  -- *a
  | pack : Id → List (Field × Site) → Expr  -- T { f: a1, ..., f: an }
  | freeze : Site → Expr
  -- Vector operations (expressions that produce a value)
  | vecPack : BasicMoveType → List Site → Expr           -- vec_pack<T>(e1,...,eN)
  | vecLen : Site → Expr                                  -- vec_len<T>(ref)
  | vecImmBorrow : Site → Site → Expr                     -- vec_imm_borrow<T>(ref, idx)
  | vecMutBorrow : Site → Site → Expr                     -- vec_mut_borrow<T>(ref, idx)
  | vecPopBack : Site → Expr                              -- vec_pop_back<T>(ref)
  -- Enum operations
  | packVariant : Id → Id → List (Field × Site) → Expr    -- Enum.Variant { f: s, ... }
deriving Repr, Inhabited, Hashable

-- Statements in a-normal form with continuation-passing style
-- Terminal statements (skip, jump, branch, ret, abort) have no continuation
-- Non-terminal statements take their continuation as the last argument
inductive Stmt where
  -- Terminal statements (no continuation)
  | skip : Stmt                                    -- no-op (terminal)
  | jump : Label → Stmt                            -- goto L
  | branch : Site → Label → Label → Stmt           -- if (a) goto L1 else goto L2
  | ret : List Site → Stmt                         -- return (a1, ..., an)
  | abort : Site → Stmt                            -- abort a
  -- Non-terminal statements (take continuation)
  | letBind : Site → Expr → Stmt → Stmt            -- let a = e; cont
  | unpack : List (Field × Site) → Site → Stmt → Stmt  -- T { fi: ai, ...} = b; cont
  | call : List Site → Id → List Site → Stmt → Stmt    -- let (a1, ..., an) = f(b1, ..., bm); cont
  | assign : Var → Site → Stmt → Stmt              -- x = a; cont
  | writeRef : Site → Site → Stmt → Stmt           -- *a = b; cont
  | release : Site → Stmt → Stmt                   -- release(a); cont
  -- Vector operations (statements with no return value)
  | vecUnpack : BasicMoveType → List Site → Site → Stmt → Stmt  -- vec_unpack<T>(results, src); cont
  | vecPushBack : Site → Site → Stmt → Stmt                     -- vec_push_back(ref, val); cont
  | vecSwap : Site → Site → Site → Stmt → Stmt                  -- vec_swap(ref, idx1, idx2); cont
  -- Enum operations
  | unpackVariant : Id → List (Field × Site) → Site → Stmt → Stmt  -- Variant { f: s, ...} = src; cont
  | variantSwitch : Site → List (Id × Label) → Stmt                -- variant_switch src { V1: l1, ... }
deriving Repr, Inhabited

-- Local variable declaration
structure LocalVar where
  name : Var
  type : MoveType
deriving Repr, Inhabited, Hashable

-- A labeled block: label and body (which ends with a terminal statement)
structure Block where
  label : Label
  body : Stmt
deriving Repr, Inhabited

-- Parameter type: basic type + optional reference mutability
structure ParamType where
  -- inner type
  basicType : BasicMoveType
  -- mutable    = some true
  -- immmutable = some false
  -- not a reference = none
  isRefMut : Option Bool
deriving Repr, Inhabited, Hashable, DecidableEq

/-- Convert a MoveType to ParamType (for bridging FunDef.params with FunSig.params) -/
def MoveType.toParamType : MoveType → ParamType
  | .basic bt => ⟨bt, none⟩
  | .ref bt _ .siteBorrowMut => ⟨bt, some true⟩
  | .ref bt _ .siteBorrowImm => ⟨bt, some false⟩

-- Enum variant definition
structure EnumVariantDef where
  name : Id                                    -- Variant name
  fields : AssocMap Field BasicMoveType       -- Field types
deriving Repr, Hashable, DecidableEq

instance : Inhabited EnumVariantDef := ⟨⟨"", AssocMap.empty⟩⟩

-- Enum definition
structure EnumDef where
  name : Id                                    -- Enum name
  variants : AssocMap Id EnumVariantDef       -- Variant name → variant definition
deriving Repr, DecidableEq

instance : Inhabited EnumDef := ⟨⟨"", AssocMap.empty⟩⟩

-- Global enum environment
abbrev EnumEnv := AssocMap Id EnumDef

/-- Look up the field types for a specific enum variant in the EnumEnv.
    Two-step lookup: first find the EnumDef, then find the variant's fields. -/
def enumVariantFields (enumEnv : EnumEnv) (ename vname : Id) : Option (AssocMap Field BasicMoveType) :=
  match enumEnv.lookup ename with
  | some enumDef => match enumDef.variants.lookup vname with
    | some variantDef => some variantDef.fields
    | none => none
  | none => none

/- ---------------------------------------------------- -/
/-       Flat Enum Encoding: Field Qualification         -/
/- ---------------------------------------------------- -/

/-- Collect all qualified field names and types for an enum definition.
    Each field becomes "VariantName.fieldName". -/
def allEnumFieldTypes (enumDef : EnumDef) : List (Field × BasicMoveType) :=
  enumDef.variants.entries.flatMap fun (vname, vdef) =>
    vdef.fields.entries.map fun (f, bt) =>
      (qualifyField vname f, bt)

/-- Look up all qualified field types for an enum by name.
    Returns an AssocMap with all variants' fields using qualified names. -/
def allEnumQualifiedFieldTypes (enumEnv : EnumEnv) (ename : Id) : Option (AssocMap Field BasicMoveType) :=
  match enumEnv.lookup ename with
  | some enumDef => some ⟨allEnumFieldTypes enumDef⟩
  | none => none

-- Function definition
structure FunDef where
  params : List (Var × MoveType)  -- (x : T)*
  returnType : List ParamType  -- Return type specifications
  locals : List LocalVar  -- (let v : T)*
  blocks : List Block  -- List of labeled blocks; first block is entry point
deriving Repr, Inhabited


end MoveLight

end LeanMove.Lang
