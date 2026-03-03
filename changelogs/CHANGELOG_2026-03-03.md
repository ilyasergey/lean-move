# Changelog — 2026-03-03

## Add alpha-equivalence parsing tests for all vector MVIR files

### Summary

Created alpha-equivalence parsing tests for all 8 vector-related MVIR
files, verifying that the parser+translator pipeline produces the
expected MoveLight FunDefs.

### New test files

- `Test_vec_basic_ops.lean` — 7 modules: pack_empty, pack_elems, len,
  push, pop, swap, unpack
- `Test_vec_borrow_sequential.lean` — 3 modules: imm_borrow_read,
  multi_imm_borrow, mut_borrow_write
- `Test_vec_double_borrow.lean` — 3 modules: imm_then_mut,
  mut_then_imm, mut_then_mut
- `Test_vec_mixed_borrow.lean` — 2 functions: foo, test (with
  Self.foo() call)
- `Test_vec_move_after_borrow.lean` — 2 modules: move after imm/mut
- `Test_vec_pop_after_borrow.lean` — 2 modules: pop after imm/mut
- `Test_vec_dangling_borrow.lean` — 3 modules: push/pop/write while
  borrow
- `Test_vec_mut_then_imm_borrow.lean` — 1 module (accepted case from
  double_borrow)

### Other changes

- Moved mut-then-imm double borrow case from rejected to accepted tests
  (it correctly type-checks)
- Added `findFunAt` helper to TestUtils for indexed function access
  (needed for MVIR files with duplicate module names)
- Extended parser to handle bare `Self.method()` and `vec_op<T>()`
  statements without assignment targets
- Updated AllParseTests.lean, AllTypecheckingTests.lean, AllTests.lean,
  and lakefile.lean with new imports

### Build

366 jobs, all passing.
