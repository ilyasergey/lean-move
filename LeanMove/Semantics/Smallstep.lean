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

import LeanMove.Lang.MoveLight
import LeanMove.Structures.AssocMap

/-!
# Small-Step Operational Semantics for MoveLight

An executable interpreter for MoveLight programs using a small-step semantics
with a global heap and call stack. References are modeled as heap locations
with field access paths, enabling correct cross-frame reference semantics.
-/

namespace LeanMove.Semantics

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open AssocMap

-- ============================================================
-- Runtime Values
-- ============================================================

/-- Heap location identifier -/
abbrev Loc := Nat

/-- Runtime values -/
inductive Value where
  | int : Nat → Value
  | bool : Bool → Value
  | unit : Value
  | record : List (Field × Value) → Value
  | ref : Loc → List Field → Value    -- heap location + field access path
deriving Repr, Inhabited

/-- Boolean equality for Values -/
def Value.beq : Value → Value → Bool
  | .int n1, .int n2 => n1 == n2
  | .bool b1, .bool b2 => b1 == b2
  | .unit, .unit => true
  | .record fs1, .record fs2 => beqFields fs1 fs2
  | .ref l1 p1, .ref l2 p2 => l1 == l2 && p1 == p2
  | _, _ => false
where
  beqFields : List (Field × Value) → List (Field × Value) → Bool
    | [], [] => true
    | (f1, v1) :: rest1, (f2, v2) :: rest2 =>
      f1 == f2 && v1.beq v2 && beqFields rest1 rest2
    | _, _ => false

instance : BEq Value := ⟨Value.beq⟩

-- ============================================================
-- Heap (Global Memory)
-- ============================================================

/-- Global heap: maps locations to values -/
structure Heap where
  store : AssocMap Loc Value
  nextLoc : Nat
deriving Repr

namespace Heap

def empty : Heap := { store := AssocMap.empty, nextLoc := 0 }

/-- Allocate a value on the heap, returning updated heap and new location -/
def alloc (h : Heap) (v : Value) : Heap × Loc :=
  let loc := h.nextLoc
  ({ store := AssocMap.insert h.store loc v, nextLoc := loc + 1 }, loc)

/-- Read a value from the heap -/
def read (h : Heap) (loc : Loc) : Option Value :=
  AssocMap.lookup h.store loc

/-- Write a value to an existing heap location -/
def write (h : Heap) (loc : Loc) (v : Value) : Heap :=
  { h with store := AssocMap.insert h.store loc v }

end Heap

-- ============================================================
-- Field Path Navigation
-- ============================================================

/-- Read a value at a field path through nested records -/
def readPath : Value → List Field → Option Value
  | v, [] => some v
  | .record fields, f :: rest =>
    match fields.lookup f with
    | some v' => readPath v' rest
    | none => none
  | _, _ :: _ => none

/-- Write a value at a field path through nested records -/
def writePath : Value → List Field → Value → Option Value
  | _, [], newVal => some newVal
  | .record fields, f :: rest, newVal =>
    match fields.lookup f with
    | some oldFieldVal =>
      match writePath oldFieldVal rest newVal with
      | some updatedFieldVal =>
        some (.record (fields.map fun (k, v) => if k == f then (k, updatedFieldVal) else (k, v)))
      | none => none
    | none => none
  | _, _ :: _, _ => none

/-- Read through a heap reference (location + field path) -/
def Heap.readRef (h : Heap) (loc : Loc) (path : List Field) : Option Value := do
  let v ← h.read loc
  readPath v path

/-- Write through a heap reference (location + field path) -/
def Heap.writeRef (h : Heap) (loc : Loc) (path : List Field) (newVal : Value) : Option Heap := do
  let v ← h.read loc
  let v' ← writePath v path newVal
  return h.write loc v'

-- ============================================================
-- Frame and Call Stack
-- ============================================================

/-- Variable store: maps variables to optional heap locations (None = consumed/uninit) -/
abbrev VarStore := AssocMap Var (Option Loc)

/-- Site store: maps sites to values -/
abbrev SiteStore := AssocMap Site Value

/-- Information needed to return from a call -/
structure ReturnInfo where
  resultSites : List Site    -- caller sites to receive return values
  callerStmt  : Stmt         -- caller continuation after call
deriving Repr

/-- A stack frame for function execution -/
structure Frame where
  varStore   : VarStore
  siteStore  : SiteStore
  stmt       : Stmt          -- current statement to execute
  blocks     : List Block    -- function blocks (for jumps)
  funEnv     : AssocMap Id FunDef
  returnInfo : Option ReturnInfo   -- None for top-level
deriving Repr

-- ============================================================
-- Machine State and Error Model
-- ============================================================

/-- Runtime errors -/
inductive RuntimeError where
  | uninitializedVar   : Var → RuntimeError
  | uninitializedSite  : Site → RuntimeError
  | typeMismatch       : String → RuntimeError
  | unknownFunction    : Id → RuntimeError
  | unknownLabel       : Label → RuntimeError
  | danglingRef        : Loc → RuntimeError
  | invalidFieldAccess : Field → RuntimeError
  | divisionByZero     : RuntimeError
  | outOfFuel          : RuntimeError
  | arityMismatch      : String → RuntimeError
deriving Repr

/-- Running machine state -/
structure Machine where
  frame : Frame
  stack : List Frame
  heap  : Heap
deriving Repr

/-- Overall execution state -/
inductive ExecState where
  | running : Machine → ExecState
  | halted  : List Value → ExecState
  | error   : RuntimeError → ExecState
deriving Repr

-- ============================================================
-- Helper: Look up variable's heap location
-- ============================================================

/-- Read a variable's value from the heap -/
def readVar (m : Machine) (x : Var) : Option Value := do
  let optLoc ← AssocMap.lookup m.frame.varStore x
  let loc ← optLoc
  m.heap.read loc

/-- Get a variable's heap location -/
def getVarLoc (m : Machine) (x : Var) : Option Loc := do
  let optLoc ← AssocMap.lookup m.frame.varStore x
  optLoc

/-- Read a site's value -/
def readSite (m : Machine) (s : Site) : Option Value :=
  AssocMap.lookup m.frame.siteStore s

-- ============================================================
-- Helper: Collect values from a list of sites
-- ============================================================

/-- Collect values from a list of sites -/
def collectSiteValues (siteStore : SiteStore) : List Site → Option (List Value)
  | [] => some []
  | s :: rest => do
    let v ← AssocMap.lookup siteStore s
    let vs ← collectSiteValues siteStore rest
    return v :: vs

-- ============================================================
-- Helper: Find block by label
-- ============================================================

/-- Find a block by label in the block list -/
def findBlock (blocks : List Block) (label : Label) : Option Block :=
  blocks.find? (fun b => b.label == label)

-- ============================================================
-- Helper: Binary operations
-- ============================================================

/-- Evaluate a binary operation -/
def evalBinop : Binop → Nat → Nat → Option Value
  | .add, a, b => some (.int (a + b))
  | .sub, a, b => some (.int (a - b))
  | .mul, a, b => some (.int (a * b))
  | .div, _, 0 => none  -- division by zero
  | .div, a, b => some (.int (a / b))
  | .mod, _, 0 => none
  | .mod, a, b => some (.int (a % b))
  | .eq, a, b => some (.bool (a == b))
  | .lt, a, b => some (.bool (a < b))
  | .nand, a, b =>
    -- Bitwise NAND on naturals (treating 0 as false, nonzero as true)
    some (.bool (!(a != 0 && b != 0)))

-- ============================================================
-- Helper: Allocate arguments for function call
-- ============================================================

/-- Allocate values on the heap and create var store entries -/
def allocArgs (heap : Heap) (params : List (Var × MoveType)) (args : List Value)
    : Option (Heap × VarStore) :=
  match params, args with
  | [], [] => some (heap, AssocMap.empty)
  | (v, _) :: ps, a :: as' => do
    let (heap', loc) := heap.alloc a
    let (heap'', vs) ← allocArgs heap' ps as'
    return (heap'', AssocMap.insert vs v (some loc))
  | _, _ => none  -- arity mismatch

/-- Add uninitialized locals to var store -/
def addLocals (vs : VarStore) : List LocalVar → VarStore
  | [] => vs
  | lv :: rest => addLocals (AssocMap.insert vs lv.name none) rest

-- ============================================================
-- Helper: Bind return values to caller sites
-- ============================================================

/-- Bind a list of values to a list of sites in a site store -/
def bindReturnValues (siteStore : SiteStore) : List Site → List Value → Option SiteStore
  | [], [] => some siteStore
  | s :: ss, v :: vs => bindReturnValues (AssocMap.insert siteStore s v) ss vs
  | _, _ => none  -- arity mismatch

-- ============================================================
-- Helper: Collect field values for pack
-- ============================================================

/-- Collect values for pack fields from site store -/
def collectPackFields (siteStore : SiteStore) : List (Field × Site) → Option (List (Field × Value))
  | [] => some []
  | (f, s) :: rest => do
    let v ← AssocMap.lookup siteStore s
    let vs ← collectPackFields siteStore rest
    return (f, v) :: vs

-- ============================================================
-- Small-Step Function
-- ============================================================

/-- Execute one step of the machine -/
def step (state : ExecState) : ExecState :=
  match state with
  | .halted vs => .halted vs
  | .error e => .error e
  | .running m =>
    let f := m.frame
    match f.stmt with

    -- --------------------------------------------------------
    -- Terminal: skip
    -- --------------------------------------------------------
    | .skip =>
      match m.stack with
      | [] => .halted []
      | _ => .error (.typeMismatch "skip in non-top-level frame")

    -- --------------------------------------------------------
    -- Terminal: ret sites
    -- --------------------------------------------------------
    | .ret sites =>
      match collectSiteValues f.siteStore sites with
      | none => .error (.uninitializedSite (.site 0))  -- generic site error
      | some vals =>
        match m.stack with
        | [] =>
          -- Top-level return: halt with values
          .halted vals
        | callerFrame :: rest =>
          -- Return to caller
          match f.returnInfo with
          | none => .error (.typeMismatch "no return info for non-top-level frame")
          | some ri =>
            match bindReturnValues callerFrame.siteStore ri.resultSites vals with
            | none => .error (.arityMismatch "return value count mismatch")
            | some newSiteStore =>
              .running {
                frame := { callerFrame with siteStore := newSiteStore, stmt := ri.callerStmt }
                stack := rest
                heap := m.heap
              }

    -- --------------------------------------------------------
    -- Terminal: jump label
    -- --------------------------------------------------------
    | .jump label =>
      match findBlock f.blocks label with
      | none => .error (.unknownLabel label)
      | some block =>
        .running {
          frame := { f with stmt := block.body, siteStore := AssocMap.empty }
          stack := m.stack
          heap := m.heap
        }

    -- --------------------------------------------------------
    -- Terminal: branch cond l1 l2
    -- --------------------------------------------------------
    | .branch condSite l1 l2 =>
      match readSite m condSite with
      | none => .error (.uninitializedSite condSite)
      | some (.bool true) =>
        match findBlock f.blocks l1 with
        | none => .error (.unknownLabel l1)
        | some block =>
          .running {
            frame := { f with stmt := block.body, siteStore := AssocMap.empty }
            stack := m.stack
            heap := m.heap
          }
      | some (.bool false) =>
        match findBlock f.blocks l2 with
        | none => .error (.unknownLabel l2)
        | some block =>
          .running {
            frame := { f with stmt := block.body, siteStore := AssocMap.empty }
            stack := m.stack
            heap := m.heap
          }
      | some _ => .error (.typeMismatch "branch condition is not a bool")

    -- --------------------------------------------------------
    -- Terminal: abort
    -- --------------------------------------------------------
    | .abort _ => .error (.typeMismatch "abort")

    -- --------------------------------------------------------
    -- Non-terminal: letBind s expr cont
    -- --------------------------------------------------------
    | .letBind s expr cont =>
      match expr with

      -- Integer literal
      | .intLit n =>
        .running {
          frame := { f with
            siteStore := AssocMap.insert f.siteStore s (.int n)
            stmt := cont
          }
          stack := m.stack
          heap := m.heap
        }

      -- Variable usage (copy/move/borrowImm/borrowMut)
      | .usage u =>
        match u with
        | .copy x =>
          match readVar m x with
          | none => .error (.uninitializedVar x)
          | some v =>
            .running {
              frame := { f with
                siteStore := AssocMap.insert f.siteStore s v
                stmt := cont
              }
              stack := m.stack
              heap := m.heap
            }

        | .move x =>
          match readVar m x with
          | none => .error (.uninitializedVar x)
          | some v =>
            .running {
              frame := { f with
                varStore := AssocMap.insert f.varStore x none
                siteStore := AssocMap.insert f.siteStore s v
                stmt := cont
              }
              stack := m.stack
              heap := m.heap
            }

        | .borrowImm x =>
          match getVarLoc m x with
          | none => .error (.uninitializedVar x)
          | some loc =>
            .running {
              frame := { f with
                siteStore := AssocMap.insert f.siteStore s (.ref loc [])
                stmt := cont
              }
              stack := m.stack
              heap := m.heap
            }

        | .borrowMut x =>
          match getVarLoc m x with
          | none => .error (.uninitializedVar x)
          | some loc =>
            .running {
              frame := { f with
                siteStore := AssocMap.insert f.siteStore s (.ref loc [])
                stmt := cont
              }
              stack := m.stack
              heap := m.heap
            }

      -- Borrow field (immutable): extend reference with field
      | .borrowField src _bt field =>
        match readSite m src with
        | none => .error (.uninitializedSite src)
        | some (.ref loc path) =>
          .running {
            frame := { f with
              siteStore := AssocMap.insert f.siteStore s (.ref loc (path ++ [field]))
              stmt := cont
            }
            stack := m.stack
            heap := m.heap
          }
        | some _ => .error (.typeMismatch "borrowField on non-ref")

      -- Borrow mutable field: same as borrowField at runtime
      | .borrowMutField src _bt field =>
        match readSite m src with
        | none => .error (.uninitializedSite src)
        | some (.ref loc path) =>
          .running {
            frame := { f with
              siteStore := AssocMap.insert f.siteStore s (.ref loc (path ++ [field]))
              stmt := cont
            }
            stack := m.stack
            heap := m.heap
          }
        | some _ => .error (.typeMismatch "borrowMutField on non-ref")

      -- Read reference (dereference)
      | .readRef src =>
        match readSite m src with
        | none => .error (.uninitializedSite src)
        | some (.ref loc path) =>
          match m.heap.readRef loc path with
          | none => .error (.danglingRef loc)
          | some v =>
            .running {
              frame := { f with
                siteStore := AssocMap.insert f.siteStore s v
                stmt := cont
              }
              stack := m.stack
              heap := m.heap
            }
        | some _ => .error (.typeMismatch "readRef on non-ref")

      -- Freeze: no-op at runtime (converts mut ref to imm ref)
      | .freeze src =>
        match readSite m src with
        | none => .error (.uninitializedSite src)
        | some v =>
          .running {
            frame := { f with
              siteStore := AssocMap.insert f.siteStore s v
              stmt := cont
            }
            stack := m.stack
            heap := m.heap
          }

      -- Pack: create a record value from field sites
      | .pack _name fieldSites =>
        match collectPackFields f.siteStore fieldSites with
        | none => .error (.uninitializedSite (.site 0))
        | some fieldVals =>
          .running {
            frame := { f with
              siteStore := AssocMap.insert f.siteStore s (.record fieldVals)
              stmt := cont
            }
            stack := m.stack
            heap := m.heap
          }

      -- Binary operation
      | .binop op a b =>
        match readSite m a, readSite m b with
        | some (.int na), some (.int nb) =>
          match evalBinop op na nb with
          | none => .error .divisionByZero
          | some v =>
            .running {
              frame := { f with
                siteStore := AssocMap.insert f.siteStore s v
                stmt := cont
              }
              stack := m.stack
              heap := m.heap
            }
        | some _, some _ => .error (.typeMismatch "binop on non-integers")
        | _, _ => .error (.uninitializedSite (.site 0))

    -- --------------------------------------------------------
    -- Non-terminal: unpack fieldSites src cont
    -- --------------------------------------------------------
    | .unpack fieldSites src cont =>
      match readSite m src with
      | none => .error (.uninitializedSite src)
      | some (.record recFields) =>
        -- Bind each field to its site
        let newSiteStore := fieldSites.foldl (fun ss (field, site) =>
          match recFields.lookup field with
          | some v => AssocMap.insert ss site v
          | none => ss  -- field not found; could error but we keep going
        ) f.siteStore
        .running {
          frame := { f with siteStore := newSiteStore, stmt := cont }
          stack := m.stack
          heap := m.heap
        }
      | some _ => .error (.typeMismatch "unpack on non-record")

    -- --------------------------------------------------------
    -- Non-terminal: assign var site cont
    -- --------------------------------------------------------
    | .assign x site cont =>
      match readSite m site with
      | none => .error (.uninitializedSite site)
      | some v =>
        let (heap', loc) := m.heap.alloc v
        .running {
          frame := { f with
            varStore := AssocMap.insert f.varStore x (some loc)
            stmt := cont
          }
          stack := m.stack
          heap := heap'
        }

    -- --------------------------------------------------------
    -- Non-terminal: writeRef dst val cont
    -- --------------------------------------------------------
    | .writeRef dst val cont =>
      match readSite m dst, readSite m val with
      | some (.ref loc path), some v =>
        match m.heap.writeRef loc path v with
        | none => .error (.danglingRef loc)
        | some heap' =>
          .running {
            frame := { f with stmt := cont }
            stack := m.stack
            heap := heap'
          }
      | some _, _ => .error (.typeMismatch "writeRef dst is not a ref")
      | none, _ => .error (.uninitializedSite dst)

    -- --------------------------------------------------------
    -- Non-terminal: release site cont
    -- --------------------------------------------------------
    | .release _site cont =>
      -- Release is a no-op at runtime (borrow tracking is static)
      .running {
        frame := { f with stmt := cont }
        stack := m.stack
        heap := m.heap
      }

    -- --------------------------------------------------------
    -- Non-terminal: call resultSites fname argSites cont
    -- --------------------------------------------------------
    | .call resultSites fname argSites cont =>
      match AssocMap.lookup f.funEnv fname with
      | none => .error (.unknownFunction fname)
      | some funDef =>
        -- Collect argument values
        match collectSiteValues f.siteStore argSites with
        | none => .error (.uninitializedSite (.site 0))
        | some argVals =>
          -- Allocate parameters on heap
          match allocArgs m.heap funDef.params argVals with
          | none => .error (.arityMismatch s!"call to {fname}")
          | some (heap', paramVarStore) =>
            -- Add locals (uninitialized)
            let calleeVarStore := addLocals paramVarStore funDef.locals
            -- Entry block
            match funDef.blocks.head? with
            | none => .error (.unknownFunction s!"{fname} has no blocks")
            | some entryBlock =>
              -- Push current frame (with return info) onto stack
              let callerFrame := { f with stmt := .skip }  -- stmt doesn't matter, saved in ReturnInfo
              let calleeFrame : Frame := {
                varStore := calleeVarStore
                siteStore := AssocMap.empty
                stmt := entryBlock.body
                blocks := funDef.blocks
                funEnv := f.funEnv
                returnInfo := some { resultSites, callerStmt := cont }
              }
              .running {
                frame := calleeFrame
                stack := callerFrame :: m.stack
                heap := heap'
              }

-- ============================================================
-- Driver Function
-- ============================================================

/-- Run the machine for at most `fuel` steps -/
def run (fuel : Nat) (state : ExecState) : ExecState :=
  match fuel with
  | 0 => .error .outOfFuel
  | n + 1 =>
    match state with
    | .running _ => run n (step state)
    | other => other

-- ============================================================
-- Initialization
-- ============================================================

/-- Create the initial execution state for running a function -/
def initState (funDef : FunDef) (funEnv : AssocMap Id FunDef)
              (args : List Value) (heap : Heap := Heap.empty) : ExecState :=
  -- Allocate parameters on heap
  match allocArgs heap funDef.params args with
  | none => .error (.arityMismatch "initState: argument count mismatch")
  | some (heap', paramVarStore) =>
    -- Add locals (uninitialized)
    let varStore := addLocals paramVarStore funDef.locals
    -- Entry block
    match funDef.blocks.head? with
    | none => .error (.unknownFunction "no blocks in function")
    | some entryBlock =>
      .running {
        frame := {
          varStore := varStore
          siteStore := AssocMap.empty
          stmt := entryBlock.body
          blocks := funDef.blocks
          funEnv := funEnv
          returnInfo := none
        }
        stack := []
        heap := heap'
      }

-- ============================================================
-- Convenience: check if a state is running
-- ============================================================

def ExecState.isRunning : ExecState → Bool
  | .running _ => true
  | _ => false

def ExecState.isHalted : ExecState → Bool
  | .halted _ => true
  | _ => false

def ExecState.isError : ExecState → Bool
  | .error _ => true
  | _ => false

def ExecState.getHaltedValues : ExecState → Option (List Value)
  | .halted vs => some vs
  | _ => none

end LeanMove.Semantics
