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

/-! ## All Typechecking Tests

Imports all litmus and expressivity typechecking test files.
Build with: `lake build`
-/
