/-
 Copyright Ilya Sergey
 Licensed under the Apache License, Version 2.0
-/

import LeanMove.Tests.Parsing.Test_alias_writes
import LeanMove.Tests.Parsing.Test_alias_write_after_join
import LeanMove.Tests.Parsing.Test_extension_after_call
import LeanMove.Tests.Parsing.Test_extension_writes_after_join
import LeanMove.Tests.Parsing.Test_imm_borrow_after_mut
import LeanMove.Tests.Parsing.Test_multible_mutable_return_values
import LeanMove.Tests.Parsing.Test_mutable_borrows_are_not_unique
import LeanMove.Tests.Parsing.Test_subtree_writes_release
import LeanMove.Tests.Parsing.Test_imm_borrow_after_mut_call
import LeanMove.Tests.Parsing.Test_imm_borrow_after_mut_fields
import LeanMove.Tests.Parsing.Test_mutable_borrows_are_not_unique_calls
import LeanMove.Tests.Parsing.Test_simple_dangling
import LeanMove.Tests.Parsing.Test_PrettyPrint
import LeanMove.Tests.Parsing.Test_vec_basic_ops
import LeanMove.Tests.Parsing.Test_vec_borrow_sequential
import LeanMove.Tests.Parsing.Test_vec_double_borrow
import LeanMove.Tests.Parsing.Test_vec_mixed_borrow
import LeanMove.Tests.Parsing.Test_vec_move_after_borrow
import LeanMove.Tests.Parsing.Test_vec_pop_after_borrow
import LeanMove.Tests.Parsing.Test_vec_dangling_borrow
import LeanMove.Tests.Parsing.Test_vec_mut_then_imm_borrow
import LeanMove.Tests.Parsing.Test_enum_match
import LeanMove.Tests.Parsing.Test_enum_all_parse
import LeanMove.Tests.Parsing.Test_enum_two_mutable_unpacks
import LeanMove.Tests.Parsing.Test_enum_double_unpack
import LeanMove.Tests.Parsing.Test_enum_valid_ref_unpack
import LeanMove.Tests.Parsing.Test_enum_invalid_ref_unpack
import LeanMove.Tests.Parsing.Test_enum_imm_borrow_on_mut_trivial_invalid
import LeanMove.Tests.Parsing.Test_enum_variant_factor
import LeanMove.Tests.Parsing.Test_enum_factor_invalid
import LeanMove.Tests.Parsing.Test_enum_borrow_field_mutable
import LeanMove.Tests.Parsing.Test_enum_valid_unpack_loop
import LeanMove.Tests.Parsing.Test_enum_imm_borrow_on_mut_invalid
import LeanMove.Tests.Parsing.Test_enum_invalid_ref_unpack_loop
import LeanMove.Tests.Parsing.Test_enum_borrow_owned
import LeanMove.Tests.Parsing.Test_comparison_ops
import LeanMove.Tests.Parsing.Test_casts
import LeanMove.Tests.Parsing.Test_bitwise
import LeanMove.Tests.Parsing.Test_arith_ops

/-! ## All Parse Tests

Imports all MVIR parse test files. Build with: `lake build parsing`
-/
