import Lake
open Lake DSL

package «lean-move» where
  -- Settings applied to both builds and interactive editing
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
  ]
  -- add any additional package configuration options here

require batteries from
    git "https://github.com/leanprover-community/batteries" @ "v4.27.0"
require mathlib from
    git "https://github.com/leanprover-community/mathlib4.git" @ "v4.27.0"

@[default_target]
lean_lib «LeanMove» where
  -- add any library configuration options here

-- Build target for litmus examples
-- Build with: lake build litmus
lean_lib «litmus» where
  srcDir := "LeanMove/Examples/Typechecking/litmus"
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
  roots := #[`litmus.accepted.borrow_in_loop_fixed_ok, `litmus.accepted.deref_borrow_field_ok,
             `litmus.rejected.borrow_in_loop,
             `expressivity.accepted.alias_write_after_join, `expressivity.accepted.alias_writes,
             `expressivity.accepted.extension_after_call, `expressivity.accepted.extension_writes_after_join,
             `expressivity.accepted.imm_borrow_after_mut, `expressivity.accepted.multible_mutable_return_values,
             `expressivity.accepted.mutable_borrows_are_not_unique, `expressivity.accepted.subtree_writes_release,
             `expressivity.rejected.simple_dangling, `expressivity.rejected.imm_borrow_after_mut_call_invalid,
             `expressivity.rejected.imm_borrow_after_mut_fields_invalid,
             `expressivity.rejected.mutable_borrows_are_not_unique_calls_invalid]

-- Build target for runtime tests (small-step interpreter)
-- Build with: lake build runtime
lean_lib «runtime» where
  srcDir := "LeanMove/Examples/Runtime"
  roots := #[`AllTests]

-- Build everything: core libraries, examples, and runtime tests
-- Build with: lake build all
lean_lib «all» where
  roots := #[`LeanMove, `LeanMove.Examples.Runtime.AllTests]
