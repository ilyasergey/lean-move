## Lean-Move

An experimental formalisation of Move borrow checker in Lean.

See **[metatheory.md](metatheory.md)** for a detailed overview of the
type system, soundness statement, proof architecture, and key invariants.

## Dependencies

* `mathlib4-v4.24.0`
* `batteries-v4.24.0`
* `ssreflect-v4.24.0`

## Building

### Build everything (default)
```bash
lake build
```
Builds the core library, all type-checking examples, and runtime tests
(including type-soundness certificates).

### Build core library only
```bash
lake build core
```

### Build type-checking examples
```bash
lake build examples    # all examples
lake build litmus       # basic litmus tests only
lake build expressivity # expressivity tests only
```

- `LeanMove/Examples/Typechecking/litmus/` — basic accepted / rejected examples
- `LeanMove/Examples/Typechecking/expressivity/` — transpiled from the
  [Move bytecode verifier tests](https://github.com/tnowacki/sui/tree/example-tests/external-crates/move/crates/bytecode-verifier-transactional-tests/tests/reference_safety/expressivity)

### Build runtime tests only
```bash
lake build runtime
```
