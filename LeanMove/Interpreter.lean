import Ssreflect.Lang

/-
Small-step semantics for Move bytecode interpreter
-/

/- Addresses, locations, program counters -/
@[reducible] def Addr := Nat
@[reducible] def Loc := Nat
@[reducible] def PC := Nat

/- Types and Values -/

inductive PrimType : Type where
  | bool    : Bool -> PrimType
  | nat     : Nat -> PrimType
  | address : Addr -> PrimType

inductive ValType : Type where
  | primtype : PrimType → ValType
  | record : (n : Nat) → (pf : n <= 4) → ValType


/- Procedures and programs -/
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

/- Execution state -/
@[reducible] def Value := Nat

structure ConcreteState where
  callstack : List (PName × PC)
  memory : Loc → Value
