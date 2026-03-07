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

-- Default target: everything (core + examples + runtime tests + parsing tests)
-- Build with: lake build
@[default_target]
lean_lib «all» where
  roots := #[`LeanMove, `LeanMove.Tests.Runtime.AllTests,
             `LeanMove.Tests.Parsing.AllParseTests,
             `LeanMove.Tests.Typechecking.AllTypecheckingTests]

-- Core library only (no examples or tests)
-- Build with: lake build core
lean_lib «core» where
  roots := #[`LeanMove]

-- Build target for litmus examples
-- Build with: lake build litmus
lean_lib «litmus» where
  srcDir := "LeanMove/Tests/Typechecking/litmus"
  roots := #[`accepted.borrow_in_loop_fixed_ok, `accepted.deref_borrow_field_ok,
             `accepted.call_rule_ok, `accepted.return_param_ref_ok,
             `rejected.borrow_in_loop, `rejected.return_local_borrow,
             `rejected.return_aliased_mut, `rejected.return_mut_with_outstanding_borrow]

-- Build target for expressivity examples
-- Build with: lake build expressivity
lean_lib «expressivity» where
  srcDir := "LeanMove/Tests/Typechecking/expressivity"
  roots := #[`accepted.alias_write_after_join, `accepted.alias_writes,
             `accepted.extension_after_call, `accepted.extension_writes_after_join,
             `accepted.imm_borrow_after_mut, `accepted.multible_mutable_return_values,
             `accepted.mutable_borrows_are_not_unique, `accepted.subtree_writes_release,
             `accepted.vec_basic_ops, `accepted.vec_borrow_sequential,
             `accepted.vec_mut_then_imm_borrow,
             `accepted.enum_two_mutable_unpacks, `accepted.enum_double_unpack,
             `accepted.enum_valid_ref_unpack, `accepted.enum_variant_factor,
             `accepted.enum_match,
             `accepted.enum_borrow_field_mutable, `accepted.enum_valid_unpack_loop,
             `accepted.enum_factor_invalid, `accepted.enum_imm_borrow_on_mut_invalid,
             `accepted.enum_imm_borrow_on_mut_trivial_invalid,
             `rejected.simple_dangling, `rejected.imm_borrow_after_mut_call_invalid,
             `rejected.imm_borrow_after_mut_fields_invalid,
             `rejected.mutable_borrows_are_not_unique_calls_invalid,
             `rejected.vec_dangling_borrow,
             `rejected.vec_double_borrow, `rejected.vec_mixed_borrow,
             `rejected.vec_move_after_borrow, `rejected.vec_pop_after_borrow,
             `rejected.enum_invalid_ref_unpack,
             `rejected.enum_invalid_ref_unpack_loop, `rejected.enum_borrow_owned]

-- Build all examples
-- Build with: lake build examples
lean_lib «examples» where
  srcDir := "LeanMove/Tests/Typechecking"
  roots := #[`litmus.accepted.borrow_in_loop_fixed_ok, `litmus.accepted.deref_borrow_field_ok,
             `litmus.accepted.call_rule_ok, `litmus.accepted.return_param_ref_ok,
             `litmus.rejected.borrow_in_loop, `litmus.rejected.return_local_borrow,
             `litmus.rejected.return_aliased_mut,
             `litmus.rejected.return_mut_with_outstanding_borrow,
             `expressivity.accepted.alias_write_after_join, `expressivity.accepted.alias_writes,
             `expressivity.accepted.extension_after_call, `expressivity.accepted.extension_writes_after_join,
             `expressivity.accepted.imm_borrow_after_mut, `expressivity.accepted.multible_mutable_return_values,
             `expressivity.accepted.mutable_borrows_are_not_unique, `expressivity.accepted.subtree_writes_release,
             `expressivity.accepted.vec_basic_ops, `expressivity.accepted.vec_borrow_sequential,
             `expressivity.accepted.vec_mut_then_imm_borrow,
             `expressivity.accepted.enum_two_mutable_unpacks, `expressivity.accepted.enum_double_unpack,
             `expressivity.accepted.enum_valid_ref_unpack, `expressivity.accepted.enum_variant_factor,
             `expressivity.accepted.enum_match,
             `expressivity.accepted.enum_borrow_field_mutable, `expressivity.accepted.enum_valid_unpack_loop,
             `expressivity.accepted.enum_factor_invalid, `expressivity.accepted.enum_imm_borrow_on_mut_invalid,
             `expressivity.accepted.enum_imm_borrow_on_mut_trivial_invalid,
             `expressivity.rejected.simple_dangling, `expressivity.rejected.imm_borrow_after_mut_call_invalid,
             `expressivity.rejected.imm_borrow_after_mut_fields_invalid,
             `expressivity.rejected.mutable_borrows_are_not_unique_calls_invalid,
             `expressivity.rejected.vec_dangling_borrow,
             `expressivity.rejected.vec_double_borrow, `expressivity.rejected.vec_mixed_borrow,
             `expressivity.rejected.vec_move_after_borrow, `expressivity.rejected.vec_pop_after_borrow,
             `expressivity.rejected.enum_invalid_ref_unpack,
             `expressivity.rejected.enum_invalid_ref_unpack_loop, `expressivity.rejected.enum_borrow_owned]

-- Build target for runtime tests (small-step interpreter)
-- Build with: lake build runtime
lean_lib «runtime» where
  srcDir := "LeanMove/Tests/Runtime"
  roots := #[`AllTests]

-- Build target for parsing tests (MVIR parser)
-- Build with: lake build parsing
lean_lib «parsing» where
  srcDir := "LeanMove/Tests/Parsing"
  roots := #[`AllParseTests]

