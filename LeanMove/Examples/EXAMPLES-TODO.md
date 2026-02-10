# Examples TODO

## Accepted examples needing work (4 files, 8 sorrys)

### expressivity/accepted/imm_borrow_after_mut.lean
- 4 sorrys: `direct_check`, `copy_and_freeze_check`, `direct_welltyped`, `copy_and_freeze_welltyped`
- `copy_and_freeze` algorithmic check returns `false` (likely refid mismatch in `var_rimm` type — declared `.refid 3` but freeze probably generates `.refid 2`)

### expressivity/accepted/multible_mutable_return_values.lean
- No algorithmic check theorem at all
- `write_welltyped` uses sorry

### expressivity/accepted/mutable_borrows_are_not_unique.lean
- No algorithmic check theorems
- `fields_welltyped` and `fields_write_welltyped` use sorry

### expressivity/accepted/subtree_writes_release.lean
- No algorithmic check theorem
- `t_welltyped` uses sorry

## Rejected examples needing work (5 files, 8 sorrys)

### expressivity/rejected/imm_borrow_after_mut_call_invalid.lean
- No check-fails theorem
- `invalid_illtyped` uses sorry

### expressivity/rejected/imm_borrow_after_mut_fields_invalid.lean
- No check-fails theorem
- `invalid_write_illtyped` uses sorry

### expressivity/rejected/mutable_borrows_not_unique_calls_invalid.lean
- No check-fails theorem
- `call_and_write_invalid_illtyped` uses sorry

### expressivity/rejected/simple_dangling.lean
- No check-fails theorems
- 4 `_illtyped` sorrys: `field_dangling_illtyped`, `nested_field_dangling_illtyped`, `simple_call_dangling_illtyped`, `field_call_dangling_illtyped`

### initial/rejected/borrow_in_loop.lean
- No check-fails theorem
- `foo_illtyped` uses sorry

## Complete (no work needed)

- expressivity/accepted/alias_writes.lean
- expressivity/accepted/extension_after_call.lean
- expressivity/accepted/alias_write_after_join.lean
- expressivity/accepted/extension_writes_after_join.lean
- initial/accepted/deref_borrow_field_ok.lean
- initial/accepted/borrow_in_loop_fixed_ok.lean
