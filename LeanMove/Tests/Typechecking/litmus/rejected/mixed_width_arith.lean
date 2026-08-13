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
import LeanMove.Typing.TypeChecking
import LeanMove.Typing.Algorithmic.AlgorithmicTypeChecking
import LeanMove.Typing.Algorithmic.DecidableTypeEnv
import LeanMove.Lang.Macros

/-!
# Mixed-Width Arithmetic and Out-of-Range Literals — Rejected

Move has no implicit integer coercion: every arithmetic and comparison opcode
requires both operands to have the *same* width, and a widening must be written
as an explicit `CastU*`. Each integer row of `binop_type` therefore guards on
`w1 == w2`:

- `binop_type .add (.int .u8) (.int .u64) = none`
- `binop_type .lt  (.int .u8) (.int .u64) = none`

A literal too large for its declared width is likewise rejected, by the
`n < w.max` premise of `let_bind_intLit`. In Move this case is unrepresentable
(the `LdU8` opcode carries a `u8`), but our AST admits `Expr.intLit 256 .u8`,
so the typing rule has to rule it out.

```
fn_add_mixed(a: u8, b: u64): u64 {
label b0:
    s0 = copy(a); s1 = copy(b);
    s2 = s0 + s1;          // REJECTED: binop_type .add u8 u64 = none
    return s2;
}

fn_u8_literal_too_big(): u8 {
label b0:
    s0 = 256u8;            // REJECTED: 256 is not < 2^8
    return s0;
}
```
-/

open LeanMove.Lang
open LeanMove.Lang.MoveLight
open LeanMove.Typing
open AssocMap

namespace LeanMove.Tests.Litmus.MixedWidthArith

-- Variables
def var_a : Var := ⟨"a"⟩
def var_b : Var := ⟨"b"⟩

-- Sites
def s0 : Site := .site 0
def s1 : Site := .site 1
def s2 : Site := .site 2

/-
  `Add` on a u8 and a u64 — should be rejected.
-/
def fn_add_mixed : FunDef := {
  params := [(var_a, .basic .u8), (var_b, .basic .u64)]
  returnType := [⟨.u64, none⟩]
  locals := []
  blocks := [
    { label := "b0"
      body :=
        (letsite s0 ← copy var_a) ;;
        (letsite s1 ← copy var_b) ;;
        (letsite s2 ← binop(.add, s0, s1)) ;;   -- REJECTED
        ret [s2]
    }
  ]
}

def fn_add_mixed_lenv := mkLabelEnv fn_add_mixed

#guard !check_fun fn_add_mixed fn_add_mixed_lenv AssocMap.empty

/-
  Comparison across widths is rejected for the same reason: `Lt` is only
  defined at equal operand widths, even though its result is `bool` either way.
-/
def fn_lt_mixed : FunDef := {
  params := [(var_a, .basic .u8), (var_b, .basic .u64)]
  returnType := [⟨.tbool, none⟩]
  locals := []
  blocks := [
    { label := "b0"
      body :=
        (letsite s0 ← copy var_a) ;;
        (letsite s1 ← copy var_b) ;;
        (letsite s2 ← binop(.lt, s0, s1)) ;;    -- REJECTED
        ret [s2]
    }
  ]
}

def fn_lt_mixed_lenv := mkLabelEnv fn_lt_mixed

#guard !check_fun fn_lt_mixed fn_lt_mixed_lenv AssocMap.empty

/-
  A `u8` literal of 256 — one past the largest `u8`.
-/
def fn_u8_literal_too_big : FunDef := {
  params := []
  returnType := [⟨.u8, none⟩]
  locals := []
  blocks := [
    { label := "b0"
      body :=
        (letsite s0 ← #256 IntType.u8) ;;       -- REJECTED
        ret [s0]
    }
  ]
}

def fn_u8_literal_too_big_lenv := mkLabelEnv fn_u8_literal_too_big

#guard !check_fun fn_u8_literal_too_big fn_u8_literal_too_big_lenv AssocMap.empty

/-
  The boundary case: 255 *is* a `u8`, so the same shape is accepted. This pins
  the bound as exclusive rather than off by one.
-/
def fn_u8_literal_max : FunDef := {
  params := []
  returnType := [⟨.u8, none⟩]
  locals := []
  blocks := [
    { label := "b0"
      body :=
        (letsite s0 ← #255 IntType.u8) ;;
        ret [s0]
    }
  ]
}

def fn_u8_literal_max_lenv := mkLabelEnv fn_u8_literal_max

#guard check_fun fn_u8_literal_max fn_u8_literal_max_lenv AssocMap.empty

/-
  A cast accepts any *integer* width, but is not defined on `bool`:
  `unop_type (.cast .u64) .tbool = none`. Move has no bool-to-integer cast.
-/
def fn_cast_bool : FunDef := {
  params := [(var_a, .basic .tbool)]
  returnType := [⟨.u64, none⟩]
  locals := []
  blocks := [
    { label := "b0"
      body :=
        (letsite s0 ← copy var_a) ;;
        (letsite s1 ← unop(.cast .u64, s0)) ;;   -- REJECTED
        ret [s1]
    }
  ]
}

def fn_cast_bool_lenv := mkLabelEnv fn_cast_bool

#guard !check_fun fn_cast_bool fn_cast_bool_lenv AssocMap.empty

/-
  Conversely, a cast is what *makes* mixed-width arithmetic legal: the same
  `a + b` that `fn_add_mixed` was rejected for is accepted once `a` is widened.
  This is the positive control for the rejection above.
-/
def fn_add_after_cast : FunDef := {
  params := [(var_a, .basic .u8), (var_b, .basic .u64)]
  returnType := [⟨.u64, none⟩]
  locals := []
  blocks := [
    { label := "b0"
      body :=
        (letsite s0 ← copy var_a) ;;
        (letsite s1 ← unop(.cast .u64, s0)) ;;
        (letsite s2 ← copy var_b) ;;
        (letsite (Site.site 3) ← binop(.add, s1, s2)) ;;
        ret [Site.site 3]
    }
  ]
}

def fn_add_after_cast_lenv := mkLabelEnv fn_add_after_cast

#guard check_fun fn_add_after_cast fn_add_after_cast_lenv AssocMap.empty

/-
  The bitwise operators are the integer counterparts of `And`/`Or`, so they are
  *not* defined at `tbool`: `binop_type .bitand .tbool .tbool = none`. Together
  with `boolean_ops_on_int.lean`, which rejects `And` on integers, this pins the
  two families apart in both directions.
-/
def fn_bitand_on_bool : FunDef := {
  params := [(var_a, .basic .tbool), (var_b, .basic .tbool)]
  returnType := [⟨.tbool, none⟩]
  locals := []
  blocks := [
    { label := "b0"
      body :=
        (letsite s0 ← copy var_a) ;;
        (letsite s1 ← copy var_b) ;;
        (letsite s2 ← binop(.bitand, s0, s1)) ;;   -- REJECTED
        ret [s2]
    }
  ]
}

def fn_bitand_on_bool_lenv := mkLabelEnv fn_bitand_on_bool

#guard !check_fun fn_bitand_on_bool fn_bitand_on_bool_lenv AssocMap.empty

/-
  And, like arithmetic, they require equal widths.
-/
def fn_bitor_mixed : FunDef := {
  params := [(var_a, .basic .u8), (var_b, .basic .u64)]
  returnType := [⟨.u64, none⟩]
  locals := []
  blocks := [
    { label := "b0"
      body :=
        (letsite s0 ← copy var_a) ;;
        (letsite s1 ← copy var_b) ;;
        (letsite s2 ← binop(.bitor, s0, s1)) ;;    -- REJECTED
        ret [s2]
    }
  ]
}

def fn_bitor_mixed_lenv := mkLabelEnv fn_bitor_mixed

#guard !check_fun fn_bitor_mixed fn_bitor_mixed_lenv AssocMap.empty

/-
  The shifts are the exception to the same-width rule, but only in one
  direction: the *amount* must be a `u8`. A `u64` shift amount is rejected even
  though both operands agree in width — `binop_type .shl` guards on
  `w2 == .u8`, not on `w1 == w2`.
-/
def fn_shl_u64_amount : FunDef := {
  params := [(var_a, .basic .u64), (var_b, .basic .u64)]
  returnType := [⟨.u64, none⟩]
  locals := []
  blocks := [
    { label := "b0"
      body :=
        (letsite s0 ← copy var_a) ;;
        (letsite s1 ← copy var_b) ;;
        (letsite s2 ← binop(.shl, s0, s1)) ;;      -- REJECTED
        ret [s2]
    }
  ]
}

def fn_shl_u64_amount_lenv := mkLabelEnv fn_shl_u64_amount

#guard !check_fun fn_shl_u64_amount fn_shl_u64_amount_lenv AssocMap.empty

/-
  The positive control: the same shift with a `u8` amount is accepted, and the
  result keeps the *left* operand's width rather than the amount's.
-/
def fn_shl_ok : FunDef := {
  params := [(var_a, .basic .u64), (var_b, .basic .u8)]
  returnType := [⟨.u64, none⟩]
  locals := []
  blocks := [
    { label := "b0"
      body :=
        (letsite s0 ← copy var_a) ;;
        (letsite s1 ← copy var_b) ;;
        (letsite s2 ← binop(.shl, s0, s1)) ;;
        ret [s2]
    }
  ]
}

def fn_shl_ok_lenv := mkLabelEnv fn_shl_ok

#guard check_fun fn_shl_ok fn_shl_ok_lenv AssocMap.empty

end LeanMove.Tests.Litmus.MixedWidthArith
