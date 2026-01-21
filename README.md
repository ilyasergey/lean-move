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

### Build all examples
```bash
lake build examples
```

### Build initial examples only
```bash
lake build initial
```

Initial examples demonstrate basic MoveLight type checking:
- `LeanMove/Examples/initial/accepted/` - Well-typed examples with complete proofs
- `LeanMove/Examples/initial/rejected/` - Ill-typed examples that fail type checking

### Build expressivity examples only
```bash
lake build expressivity
```

The expressivity examples are transpiled from the Move bytecode verifier transactional tests:
- `LeanMove/Examples/expressivity/accepted/` - Examples that pass the type checker
- `LeanMove/Examples/expressivity/rejected/` - Examples that fail the type checker

Source: https://github.com/tnowacki/sui/tree/example-tests/external-crates/move/crates/bytecode-verifier-transactional-tests/tests/reference_safety/expressivity
