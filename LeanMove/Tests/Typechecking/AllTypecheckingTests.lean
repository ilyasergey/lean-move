/-
 Copyright Ilya Sergey
 Licensed under the Apache License, Version 2.0
-/

-- Litmus tests (accepted)
import LeanMove.Tests.Typechecking.litmus.accepted.borrow_in_loop_fixed_ok
import LeanMove.Tests.Typechecking.litmus.accepted.deref_borrow_field_ok
import LeanMove.Tests.Typechecking.litmus.accepted.call_rule_ok
import LeanMove.Tests.Typechecking.litmus.accepted.return_param_ref_ok

-- Litmus tests (rejected)
import LeanMove.Tests.Typechecking.litmus.rejected.borrow_in_loop
import LeanMove.Tests.Typechecking.litmus.rejected.return_local_borrow
import LeanMove.Tests.Typechecking.litmus.rejected.return_aliased_mut
import LeanMove.Tests.Typechecking.litmus.rejected.return_mut_with_outstanding_borrow

-- Expressivity tests (accepted)
import LeanMove.Tests.Typechecking.expressivity.accepted.alias_write_after_join
import LeanMove.Tests.Typechecking.expressivity.accepted.alias_writes
import LeanMove.Tests.Typechecking.expressivity.accepted.extension_after_call
import LeanMove.Tests.Typechecking.expressivity.accepted.extension_writes_after_join
import LeanMove.Tests.Typechecking.expressivity.accepted.imm_borrow_after_mut
import LeanMove.Tests.Typechecking.expressivity.accepted.multible_mutable_return_values
import LeanMove.Tests.Typechecking.expressivity.accepted.mutable_borrows_are_not_unique
import LeanMove.Tests.Typechecking.expressivity.accepted.subtree_writes_release
import LeanMove.Tests.Typechecking.expressivity.accepted.vec_basic_ops
import LeanMove.Tests.Typechecking.expressivity.accepted.vec_borrow_sequential
import LeanMove.Tests.Typechecking.expressivity.accepted.vec_mut_then_imm_borrow
import LeanMove.Tests.Typechecking.expressivity.accepted.enum_two_mutable_unpacks
import LeanMove.Tests.Typechecking.expressivity.accepted.enum_double_unpack
import LeanMove.Tests.Typechecking.expressivity.accepted.enum_valid_ref_unpack
import LeanMove.Tests.Typechecking.expressivity.accepted.enum_variant_factor
import LeanMove.Tests.Typechecking.expressivity.accepted.enum_match
import LeanMove.Tests.Typechecking.expressivity.accepted.enum_borrow_field_mutable
import LeanMove.Tests.Typechecking.expressivity.accepted.enum_valid_unpack_loop
import LeanMove.Tests.Typechecking.expressivity.accepted.enum_factor_invalid
import LeanMove.Tests.Typechecking.expressivity.accepted.enum_imm_borrow_on_mut_invalid
import LeanMove.Tests.Typechecking.expressivity.accepted.enum_imm_borrow_on_mut_trivial_invalid

-- Expressivity tests (rejected)
import LeanMove.Tests.Typechecking.expressivity.rejected.simple_dangling
import LeanMove.Tests.Typechecking.expressivity.rejected.imm_borrow_after_mut_call_invalid
import LeanMove.Tests.Typechecking.expressivity.rejected.imm_borrow_after_mut_fields_invalid
import LeanMove.Tests.Typechecking.expressivity.rejected.mutable_borrows_are_not_unique_calls_invalid
import LeanMove.Tests.Typechecking.expressivity.rejected.vec_dangling_borrow
import LeanMove.Tests.Typechecking.expressivity.rejected.vec_double_borrow
import LeanMove.Tests.Typechecking.expressivity.rejected.vec_mixed_borrow
import LeanMove.Tests.Typechecking.expressivity.rejected.vec_move_after_borrow
import LeanMove.Tests.Typechecking.expressivity.rejected.vec_pop_after_borrow
import LeanMove.Tests.Typechecking.expressivity.rejected.enum_invalid_ref_unpack
import LeanMove.Tests.Typechecking.expressivity.rejected.enum_invalid_ref_unpack_loop
import LeanMove.Tests.Typechecking.expressivity.rejected.enum_borrow_owned

-- Divergences from the Move bytecode verifier that the suite above does not catch.
-- The `#guard`s in this file pin down *wrong* behaviour on purpose; see its header.
import LeanMove.Tests.Typechecking.KnownGaps

/-! ## All Typechecking Tests

Imports all litmus and expressivity typechecking test files.
Build with: `lake build`
-/
