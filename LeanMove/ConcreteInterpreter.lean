import Ssreflect.Lang
-- import Mathlib.Data.Finset.Basic
-- import Mathlib.Data.Finset.Card

/-
Small-step semantics for Move bytecode interpreter
-/

/- --------------------------------------------------------- -/
/- Addresses, locations, program counters -/
/- --------------------------------------------------------- -/

@[reducible] def Addr := Nat
@[reducible] def Loc := Nat
@[reducible] def PC := Nat

/- --------------------------------------------------------- -/
/- Types and Values -/
/- --------------------------------------------------------- -/

inductive PrimType : Type where
  | bool    : PrimType
  | nat     : PrimType
  | address : PrimType

-- Can't be used used in the inductive definition, leaving here just in case
def defined {T S: Type} [BEq T]  (dom : List T) (f : T -> Option S) : Prop :=
  forall e : T, List.contains dom e ↔ f e ≠ none

inductive ValType : Type where
  | primtype : PrimType → ValType
  -- For simplicity, use list indices to represent field names
  | record : List ValType → ValType

inductive RefType : Type where
  | mutreftype : ValType → RefType
  | immreftype : ValType → RefType

inductive MType : Type where
  | valtype : ValType → MType
  | reftype : RefType → MType

/- --------------------------------------------------------- -/
/- Procedures and programs -/
/- --------------------------------------------------------- -/
def PName := String

inductive Bytecode : Type where
  | skip : Bytecode
  -- TODO: add other constructors

structure Procedure where
  code : Array Bytecode
  ins : List MType
  outs : List MType
  locals : List MType

def Program := PName → Procedure

/- --------------------------------------------------------- -/
/- Execution state -/
/- --------------------------------------------------------- -/

@[reducible] def Value := Nat

structure ConcreteState where
  callstack : List (PName × PC)
  memory : Loc → Value
