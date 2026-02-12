import Lake
open Lake DSL

package «lean-move» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  -- add any additional package configuration options here

require batteries from
    git "https://github.com/leanprover-community/batteries" @ "v4.24.0"
require mathlib from
    git "https://github.com/leanprover-community/mathlib4.git" @ "v4.24.0"
-- require loogle from git "https://github.com/nomeata/loogle.git" @ "master"
require ssreflect from
    git "https://github.com/verse-lab/lean-ssr.git" @ "v4.24.0"

@[default_target]
lean_lib «LeanMove» where
  -- add any library configuration options here

-- Build target for initial examples
-- Build with: lake build initial
lean_lib «initial» where
  srcDir := "LeanMove/Examples/Typechecking/initial"
  roots := #[`accepted.borrow_in_loop_fixed_ok, `accepted.deref_borrow_field_ok,
             `rejected.borrow_in_loop]

-- Build target for expressivity examples
-- Build with: lake build expressivity
lean_lib «expressivity» where
  srcDir := "LeanMove/Examples/Typechecking/expressivity"
  roots := #[`accepted.alias_write_after_join, `accepted.alias_writes,
             `accepted.extension_after_call, `accepted.extension_writes_after_join,
             `accepted.imm_borrow_after_mut, `accepted.multible_mutable_return_values,
             `accepted.mutable_borrows_are_not_unique, `accepted.subtree_writes_release,
             `rejected.simple_dangling, `rejected.imm_borrow_after_mut_call_invalid,
             `rejected.imm_borrow_after_mut_fields_invalid,
             `rejected.mutable_borrows_are_not_unique_calls_invalid]

-- Build all examples
-- Build with: lake build examples
lean_lib «examples» where
  srcDir := "LeanMove/Examples/Typechecking"
  roots := #[`initial.accepted.borrow_in_loop_fixed_ok, `initial.accepted.deref_borrow_field_ok,
             `initial.rejected.borrow_in_loop,
             `expressivity.accepted.alias_write_after_join, `expressivity.accepted.alias_writes,
             `expressivity.accepted.extension_after_call, `expressivity.accepted.extension_writes_after_join,
             `expressivity.accepted.imm_borrow_after_mut, `expressivity.accepted.multible_mutable_return_values,
             `expressivity.accepted.mutable_borrows_are_not_unique, `expressivity.accepted.subtree_writes_release,
             `expressivity.rejected.simple_dangling, `expressivity.rejected.imm_borrow_after_mut_call_invalid,
             `expressivity.rejected.imm_borrow_after_mut_fields_invalid,
             `expressivity.rejected.mutable_borrows_are_not_unique_calls_invalid]
