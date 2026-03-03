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

/-! ## All Parse Tests

Imports all MVIR parse test files. Build with: `lake build parsing`
-/
