# MoveIR Parser — Unsupported Features

This document lists Move IR features not currently supported by the parser/translator,
organized by category. Each entry notes: (a) whether it appears in any current `.mvir`
example, (b) what MoveLight AST extension would be needed, and (c) rough effort estimate.

## 1. Type System

| Feature | In examples? | MoveLight extension needed | Effort |
|---------|-------------|---------------------------|--------|
| **Vector types** (`vector<T>`) | Yes (`simple_dangling.mvir`) | Add `BasicMoveType.vector : BasicMoveType → BasicMoveType` | Medium |
| **Type parameters / generics** | No | Add type variables to `MoveType`, polymorphic `FunDef` | Large |
| **Address type** | No | Add `BasicMoveType.address` | Small |
| **Signer type** | No | Add `BasicMoveType.signer` | Small |
| **u8, u16, u32, u128, u256** | No | Add width variants to `BasicMoveType` or parameterize `.u` | Small |

## 2. Expressions

| Feature | In examples? | MoveLight extension needed | Effort |
|---------|-------------|---------------------------|--------|
| **Vector operations** (`vec_pack_0`, `vec_mut_borrow`, `vec_len`, `vec_push_back`, etc.) | Yes (`simple_dangling.mvir`) | Add `Expr.vecOp` or encode as built-in calls | Medium |
| **Unary operators** (`!`, `not`) | No | Add `Expr.unop : Unop → Site → Expr` | Small |
| **Bitwise binary ops** (`&`, `\|`, `^`, `<<`, `>>`) | No | Add variants to `Binop` | Small |
| **Logical operators** (`&&`, `\|\|`) | No | Add `Binop.and`, `Binop.or` | Small |
| **Comparison operators** (`>`, `<=`, `>=`, `!=`) | No | Add variants to `Binop` | Small |
| **Boolean literals** (`true`, `false`) | No (used as type, not value in examples) | Add `Expr.boolLit : Bool → Expr` | Small |

## 3. Statements

| Feature | In examples? | MoveLight extension needed | Effort |
|---------|-------------|---------------------------|--------|
| **`assert(cond, code)`** | No | Add `Stmt.assert : Site → Site → Stmt` | Small |
| **`jump_if_false(cond) L`** | No | Already supported via `branch` with swapped labels | Small |
| **`variant_switch`** | No | Add `Stmt.variantSwitch` (requires enum support) | Large |

## 4. Definitions

| Feature | In examples? | MoveLight extension needed | Effort |
|---------|-------------|---------------------------|--------|
| **Constants** | No | Add `ConstDef` and constant expression evaluation | Medium |
| **Enums / variants** | No | Add `BasicMoveType.enum`, variant pack/unpack, switch | Large |
| **Native functions** | No | Add `FunBody.native` marker | Small |
| **Native structs** | No | Add `StructDef.native` marker | Small |

## 5. Module System

| Feature | In examples? | MoveLight extension needed | Effort |
|---------|-------------|---------------------------|--------|
| **Cross-module imports** | No | Add import resolution and qualified name lookup | Medium |
| **Friend declarations** | No | Add visibility tracking to module structure | Small |
| **Module dependencies** | No | Add dependency graph and topological resolution | Medium |
| **Explicit versioning** | No | Add version field to module structure | Small |
| **Fully qualified calls** (`0x2.M.f(...)`) | No | Add module-qualified function name resolution | Medium |

## 6. Abilities

| Feature | In examples? | MoveLight extension needed | Effort |
|---------|-------------|---------------------------|--------|
| **Ability validation** (copy, drop, key, store) | Yes (parsed but ignored) | Add ability checking to type system; validate pack/move/copy against declared abilities | Medium |

## 7. Other

| Feature | In examples? | MoveLight extension needed | Effort |
|---------|-------------|---------------------------|--------|
| **Bytecode representation** | No | Separate bytecode AST and translation | Large |
| **Entry functions** (`is_entry`) | No | Add entry flag to `FunDef` | Small |
| **Function visibility** (public/friend/internal) | No | Add visibility field to `FunDef` | Small |
| **`//# publish` directive** | Yes (parsed and ignored) | Add publishability flag to `MvirModule` | Small |
| **Multi-module struct references** (`0x2.M.S`) | No | Add qualified struct type resolution | Medium |
