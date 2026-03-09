## Lean-Move

An experimental formalisation of Move borrow checker in Lean.

See **[metatheory.md](metatheory.md)** for a detailed overview of the
type system, soundness statement, proof architecture, and key invariants.

## Dependencies

* `mathlib4-v4.27.0`
* `batteries-v4.27.0`

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

- `LeanMove/Tests/Typechecking/litmus/` — basic accepted / rejected examples
- `LeanMove/Tests/Typechecking/expressivity/` — transpiled from the
  [Move bytecode verifier tests](https://github.com/tnowacki/sui/tree/example-tests/external-crates/move/crates/bytecode-verifier-transactional-tests/tests/reference_safety/expressivity)
- `LeanMove/Tests/MVIR/` — Move IR source files (`.mvir`) shared across
  parsing and type-checking tests

### Build runtime tests only
```bash
lake build runtime
```
