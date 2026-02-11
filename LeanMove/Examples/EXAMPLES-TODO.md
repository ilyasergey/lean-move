# Examples TODO

## Accepted examples — Complete

All accepted examples have:
- Algorithmic check theorems (`check_fun f lenv = true := by rfl`)
- Relational well-typedness proofs (`∃ lenv, typecheck_fun f lenv` via `check_fun_sound`)

- expressivity/accepted/alias_writes.lean
- expressivity/accepted/alias_write_after_join.lean
- expressivity/accepted/extension_after_call.lean
- expressivity/accepted/extension_writes_after_join.lean
- expressivity/accepted/imm_borrow_after_mut.lean
- expressivity/accepted/multible_mutable_return_values.lean
- expressivity/accepted/mutable_borrows_are_not_unique.lean
- expressivity/accepted/subtree_writes_release.lean
- initial/accepted/borrow_in_loop_fixed_ok.lean
- initial/accepted/deref_borrow_field_ok.lean

## Rejected examples — Algorithmic rejection proven, relational proofs pending

All rejected examples have:
- Algorithmic check-fails theorems (`check_fun f lenv = false := by native_decide`)
- `_illtyped` theorems still use `sorry` (require `check_fun_complete` which is not yet proven)

- expressivity/rejected/imm_borrow_after_mut_call_invalid.lean
- expressivity/rejected/imm_borrow_after_mut_fields_invalid.lean
- expressivity/rejected/mutable_borrows_not_unique_calls_invalid.lean
- expressivity/rejected/simple_dangling.lean (4 functions)
- initial/rejected/borrow_in_loop.lean

## Remaining work

The `_illtyped` proofs (`¬ ∃ lenv, typecheck_fun f lenv`) for rejected examples
depend on the completeness theorem `check_fun_complete` in
`AlgorithmicTypingCompleteness.lean`, which currently has `sorry`.
Once completeness is proven, these can be closed via the contrapositive:
if `typecheck_fun f lenv` held, then `check_fun f lenv = true` by completeness,
contradicting `check_fun f lenv = false`.
