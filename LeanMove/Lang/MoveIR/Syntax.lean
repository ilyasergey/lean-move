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

/-! ## Intermediate MVIR AST

This module defines an intermediate AST that mirrors the Move IR (.mvir) syntax.
It is used as the target for parsing, before being translated to MoveLight's
A-normal form representation.
-/

namespace LeanMove.Lang.MoveIR

/-- MVIR types as they appear in source text -/
inductive MvirType where
  | u64
  | u8
  | bool
  | unit
  | vector : MvirType → MvirType
  | struct : String → MvirType              -- struct name (e.g., "Self.S" or "S")
  | ref : Bool → MvirType → MvirType        -- is_mutable × inner type
deriving Repr, Inhabited, BEq

/-- MVIR expressions (nested, NOT A-normal form) -/
inductive MvirExpr where
  | copy : String → MvirExpr                                  -- copy(x)
  | move : String → MvirExpr                                  -- move(x)
  | borrowLocal : Bool → String → MvirExpr                    -- &x / &mut x
  | intLit : Nat → MvirExpr                                   -- N
  | boolLit : Bool → MvirExpr                                 -- true / false
  | fieldBorrow : Bool → MvirExpr → String → String → MvirExpr
      -- is_mut × source_expr × struct_name × field_name
  | deref : MvirExpr → MvirExpr                               -- *e
  | binop : String → MvirExpr → MvirExpr → MvirExpr           -- e1 op e2
  | pack : String → List (String × MvirExpr) → MvirExpr       -- T { f: e, ... }
  | packVariant : String → String → List (String × MvirExpr) → MvirExpr
      -- enum_name × variant_name × [(field, expr)]            -- Enum.Variant { f: e, ... }
  | freeze : MvirExpr → MvirExpr                               -- freeze(e)
  | call : String → List MvirExpr → MvirExpr                   -- fname(args)
  | vecOp : String → MvirType → List MvirExpr → MvirExpr      -- op<T>(args)
deriving Repr, Inhabited

/-- MVIR statements -/
inductive MvirStmt where
  | assign : List String → MvirExpr → MvirStmt                -- x = e; or x, y = e;
  | writeRef : MvirExpr → MvirExpr → MvirStmt                 -- *e1 = e2;
  | unpack : String → List (String × String) → MvirExpr → MvirStmt
      -- struct_name × [(field, var)] × source
  | jump : String → MvirStmt                                   -- jump L;
  | jumpIf : MvirExpr → String → MvirStmt                     -- jump_if (e) L;
  | jumpIfFalse : MvirExpr → String → MvirStmt                -- jump_if_false (e) L;
  | ret : List MvirExpr → MvirStmt                            -- return; or return e1, e2;
  | abort : MvirExpr → MvirStmt                               -- abort e;
  | unpackVariant : (isMut : Option Bool) → String → String → List (String × String) → MvirExpr → MvirStmt
      -- isMut (none=owned, some false=&, some true=&mut) × enum_name × variant_name × [(field, var)] × source
  | variantSwitch : String → MvirExpr → List (String × String) → MvirStmt
      -- enum_name × source_expr × [(variant_name, label)]
deriving Repr, Inhabited

/-- A labeled block with a sequence of statements -/
structure MvirBlock where
  label : String
  stmts : List MvirStmt
deriving Repr, Inhabited

/-- A function parameter or local variable declaration -/
structure MvirParam where
  name : String
  type : MvirType
deriving Repr, Inhabited

/-- A function definition in MVIR -/
structure MvirFunDef where
  name : String
  params : List MvirParam
  returnTypes : List MvirType
  locals : List MvirParam
  blocks : List MvirBlock
deriving Repr, Inhabited

/-- A struct field declaration -/
structure MvirStructField where
  name : String
  type : MvirType
deriving Repr, Inhabited

/-- A struct definition with abilities -/
structure MvirStructDef where
  name : String
  abilities : List String           -- "copy", "drop", "key", "store"
  fields : List MvirStructField
deriving Repr, Inhabited

/-- An enum definition with abilities and variants -/
structure MvirEnumDef where
  name : String
  abilities : List String
  variants : List (String × List MvirStructField)  -- [(variant_name, fields)]
deriving Repr, Inhabited

/-- A module containing struct, enum, and function definitions -/
structure MvirModule where
  address : String                   -- e.g., "0x2"
  name : String                      -- e.g., "field"
  structs : List MvirStructDef
  enums : List MvirEnumDef
  functions : List MvirFunDef
deriving Repr, Inhabited

/-- A complete MVIR file with one or more modules -/
structure MvirFile where
  modules : List MvirModule
deriving Repr, Inhabited

end LeanMove.Lang.MoveIR
