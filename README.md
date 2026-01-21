## Lean-Move

An experimental formalisation of Move borrow checker in Lean

## Dependencies

* `mathlib4-v4.24.0`
* `batteries-v4.24.0`
* `ssreflect-v4.24.0`

## Building

### Build all
```bash
lake build
```

### Build expressivity examples only
```bash
lake build expressivity
```

The expressivity examples are transpiled from the Move bytecode verifier transactional tests:
- `LeanMove/Examples/expressivity/accepted/` - Examples that pass the type checker
- `LeanMove/Examples/expressivity/rejected/` - Examples that fail the type checker

Source: https://github.com/tnowacki/sui/tree/example-tests/external-crates/move/crates/bytecode-verifier-transactional-tests/tests/reference_safety/expressivity
