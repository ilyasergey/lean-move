# MoveLight: Metatheory Overview

This document describes the formalisation of the MoveLight type system and its
soundness proof. MoveLight is a simplified model of the
[Move](https://move-language.github.io/move/) borrow checker, formalised in
Lean 4 with machine-checked proofs.

## TL;DR

We built a **regex-based reference-safety type checker** for MoveLight — a
core calculus of the Move intermediate representation — and proved it
**sound** with respect to a runnable small-step semantics, all in Lean 4.

- The type checker is **executable**: it runs as a boolean function inside
  Lean and can verify programs by kernel reduction (`by rfl`).
- The soundness theorem guarantees that well-typed programs **never produce
  non-acceptable errors** at runtime. The type system rules out **8 of 13**
  runtime error constructors — including dangling references,
  uninitialized variables, type mismatches, unknown labels/functions,
  arity mismatches, and invalid field accesses. Only 5 *acceptable*
  errors remain: `divisionByZero` (runtime arithmetic), `outOfFuel`
  (bounded interpreter), `aborted` (well-typed `abort` statement),
  `vectorError` (out-of-bounds access, empty pop, length mismatch),
  and `variantMismatch` (unpacking with wrong variant name).
- The language supports **vectors** (Part III) and **enums** (Part IV) as
  extensions to the core calculus, each fully integrated into the type
  system and soundness proof.
- We demonstrate this end-to-end on programs drawn from the **Move bytecode
  verifier's own test suite**: each program is type-checked, executed on a
  concrete heap, and certified free of all preventable errors — all within
  a single `lake build`.

### Limitations and scope

MoveLight is a deliberately simplified model of the Move borrow checker.
The formalisation does **not** cover:

- **Generics and type parameters.** MoveLight has no polymorphism;
  all types are monomorphic (`u64`, `bool`, records with fixed fields).
- **Abilities beyond copy/drop.** Move's `store` and `key` abilities
  are parsed but not enforced. Resource linearity (must-use semantics)
  is not modelled.
- **Global storage operations.** `move_to`, `move_from`, `borrow_global`,
  `exists` are not modelled.
- **Multi-signer and script functions.** The formalisation focuses on
  single-module, intra-procedural borrow checking.
- **Loops with complex invariants.** Back edges are supported via label
  environments, but the formalisation does not synthesise loop invariants;
  they must be provided as part of the label environment.
These restrictions keep the core calculus small enough for complete
machine-checked soundness proofs while still capturing the essence of
Move's reference-safety discipline — aliased mutable borrows, field
borrows, freeze, release, cross-function borrow propagation,
control-flow joins, vector operations (see Part III), and enum variant
packing/unpacking with pattern matching (see Part IV).

---

## Part I — Definitions and Statements

### Project layout

```
LeanMove/
├── Lang/MoveLight.lean            Language syntax and core types
├── Lang/Macros.lean               CPS macros for writing MoveLight programs
├── Semantics/Smallstep.lean       Small-step interpreter
│
├── Typing/
│   ├── Types.lean                 Type environments, subsumption, well-formedness
│   ├── TypesUtils.lean            Freshness, path operations, environment helpers
│   ├── TypeChecking.lean          Relational typing rules
│   │
│   ├── Algorithmic/
│   │   ├── AlgorithmicTypeChecking.lean       Executable type checker
│   │   ├── AlgorithmicTypingSoundness.lean    Algorithmic ⇒ relational
│   │   └── DecidableTypeEnv.lean              Decidable environment checks
│   │
│   ├── Soundness/
│   │   ├── Defs.lean              WellTypedState, StackSafe, FunTypeSafe
│   │   ├── InitState.lean         Initial state safety, SoundnessAssumptions
│   │   ├── Preservation.lean      Preservation theorem (per-rule case proofs)
│   │   ├── Weakening.lean         Weakening / subsumption lemmas
│   │   ├── StackSafeUtils.lean    Stack frame safety utilities
│   │   ├── Progress.lean          step_error_is_acceptable (all 8 error types)
│   │   └── SafeExec.lean          SafeExecState, iterated safety
│   │
│   └── TypeSoundness.lean         Main theorems (general + backward-compatible corollaries)
│
├── Structures/                    AssocMap, Regex, ListUtils, PathMap
│
└── Tests/
    ├── MVIR/                      Move IR source files (.mvir) shared by tests
    ├── Parsing/                   Parser and translator tests
    ├── Typechecking/
    │   ├── litmus/                Basic accepted / rejected examples
    │   └── expressivity/          Transpiled Move bytecode verifier tests
    └── Runtime/
        └── AllTests.lean          Runtime tests + type-soundness certificates
```

### Language (`Lang/MoveLight.lean`)

MoveLight programs are sequences of *blocks*, each containing a *statement*
that ends with a terminal (`skip`, `jump`, `branch`, `ret`, `abort`).
Non-terminal statements have the form `letBind site expr cont`, `writeRef`,
`assign`, `release`, `unpack`, `call`, `vecUnpack`, `vecPushBack`,
`vecSwap`, or `unpackVariant`, where `cont` is the continuation statement
within the same block. Terminal statements include `variantSwitch` (enum
pattern matching) in addition to `skip`, `jump`, `branch`, `ret`, and
`abort`.

Types are either *basic* (`u64`, `bool`, `unit`, records, vectors, enums) or
*references* `ref τ r bk`, carrying a basic content type `τ`, an abstract
reference `r : Aref`, and a borrowing kind `bk` (immutable or mutable).
Vector types have the form `tvec T` where `T` is the element type (itself a
`BasicMoveType`). Enum types have the form `tenum name` where `name`
identifies the enum definition in an `EnumEnv`. Abstract references (`Aref`) are either `.root` (the local
variable root), `.refid n` (a placeholder used during type checking), or
`.paramRef v` (tied to parameter `v`).

### Operational semantics (`Semantics/Smallstep.lean`)

The interpreter defines:

| Definition | Purpose |
|---|---|
| `Machine` | Running state: current frame, call stack, heap |
| `ExecState` | `.running Machine \| .halted vals \| .error err` |
| `step : ExecState → ExecState` | One evaluation step |
| `run (fuel : Nat) : ExecState → ExecState` | Bounded evaluation |
| `initState` | Build initial machine from function, arguments, heap |

Runtime errors are classified into **preventable** (ruled out by the type
system) and **acceptable** (not preventable):

| Error | Preventable? | Reason |
|---|---|---|
| `danglingRef` | Yes | Borrow tracking ensures valid references |
| `uninitializedVar` | Yes | Type system tracks valid/invalid var status |
| `uninitializedSite` | Yes | Sites always initialized by letBind before use |
| `unknownLabel` | Yes | Label env covers all jump/branch targets |
| `unknownFunction` | Yes | FunEnv consistency checked |
| `arityMismatch` | Yes | Parameter/return counts checked |
| `invalidFieldAccess` | Yes | Not produced by current step (0 sites) |
| `typeMismatch` | Yes | All production sites preventable |
| `divisionByZero` | No | Runtime arithmetic |
| `outOfFuel` | No | Bounded interpreter limitation |
| `aborted` | No | Well-typed `abort` statement or `skip` in callee |
| `vectorError` | No | Index out of bounds, empty pop, length mismatch |
| `variantMismatch` | No | Unpacking enum with wrong variant name |

The predicate `RuntimeError.isAcceptable` marks the last five as acceptable.
Type soundness rules out all non-acceptable errors.

### Relational typing (`Typing/TypeChecking.lean`)

The central judgment is:

```
typecheck_stmt : LabelEnv → TypeEnv → Stmt → List ParamType → Prop
```

It relates a label environment (mapping labels to expected type environments),
a current type environment, a statement, and expected return types. A
`TypeEnv` bundles four components:

| Component | Type | Tracks |
|---|---|---|
| `varEnv` | `Var → (IsValid × MoveType × Mut)` | Variable validity, type, mutability |
| `siteEnv` | `Site → MoveType` | Temporary value types |
| `pathEnv` | `PathEnv` (refs + path graph) | Abstract reference relationships |
| `funEnv` | `Id → FunSig` | Available function signatures |

The `pathEnv` is the key novelty: it maintains a graph of *abstract
references* (`Aref`) with edges labelled by *path elements* (field names or
root-to-variable links). Edges are represented as regular expressions over
path elements, enabling finite representation of unbounded loop iterations.

**Typing rules — highlights:**

- **`jump L`** / **`branch a L1 L2`**: the label environment entry must
  *subsume* the current environment (see below).
- **`borrowImm x`** / **`borrowMut x`**: allocate a fresh abstract ref `r`,
  add it to `pathEnv.refs`, and record the path `root →[root_to_var x] r`.
- **`readRef a`** / **`writeRef a b`**: consume the reference site; for
  writes, `check_outbound` verifies that all outbound paths from the mutable
  ref are trivial (empty), ensuring no aliases are invalidated.
- **`call`**: output sites get fresh refs; `populate_call_outputs` builds the
  post-call environment; `call_connect_inputs_outputs` links input and output
  path graphs.
- **`ret as`**: checks (1) types conform, (2) no local borrowing, (3)
  mutable returns have only trivial outbound paths, (4) no aliasing between
  mutable returns and other returns.

**Subsumption** (`TypeEnv.subsumes`) mediates control-flow joins. It asserts
the existence of a substitution `σ : Aref → Aref` (identity on non-`.refid`
refs) such that variable/site environments agree modulo `σ`, refs are a
permutation, `σ` is injective, and path inclusion holds (every path in the
target environment is also a path in the source, modulo `σ`).

**Function typing** (`typecheck_fun`) checks that every block type-checks
against its label-environment entry, the entry block matches the initialised
environment, and every pair of consecutive label entries is consistent
(equivalence at join points).

### Type soundness statement (`Typing/TypeSoundness.lean`)

```lean
theorem type_soundness (f : FunDef) (lenv : LabelEnv) (enumEnv : EnumEnv)
    (funEnv : AssocMap Id FunDef)
    (args : List Value) (heap : Heap)
    (htyped : typecheck_fun f lenv enumEnv)
    (hfunEnv : ∀ fname fdef, lookup funEnv fname = some fdef
                             → FunTypeSafe fdef funEnv enumEnv)
    (ha : SoundnessAssumptions f lenv enumEnv funEnv heap args)
    (e : RuntimeError) (hna : ¬e.isAcceptable) :
    ∀ n, run n (initState f funEnv args (enumEnv := enumEnv) (heap := heap)) ≠ .error e
```

In words: if a function is well-typed (`typecheck_fun`), every callee is
safely typed (`FunTypeSafe`), and the runtime configuration satisfies the
soundness assumptions (including enum environment well-formedness), then
execution never produces a non-acceptable error regardless of how many
steps are taken. This rules out all 8 preventable error constructors.
A backward-compatible corollary `type_soundness_no_danglingRef`
specialises to `danglingRef`.

### Algorithmic type checker (`Typing/Algorithmic/`)

The executable checker mirrors the relational rules:

| File | Role |
|---|---|
| `AlgorithmicTypeChecking.lean` | `check_stmt_dec`, `check_fun_dec`, `subsumes_bool` |
| `AlgorithmicTypingSoundness.lean` | `check_fun_dec_sound : check_fun_dec f lenvDec = true → typecheck_fun f lenvDec.toLabelEnv` |
| `DecidableTypeEnv.lean` | Decidable `PathEnvDec`, `TypeEnvDec`, `LabelEnvDec`; `checkFunEnv`; `allVarRefsTracked_bool` |

The algorithmic checker uses decidable data structures (`AssocMap`-based
`PathEnvDec` with explicit ref lists and path maps) and boolean checks. Its
soundness theorem `check_fun_dec_sound` bridges to the relational system.

### Decidable soundness (`type_soundness_dec`)

```lean
theorem type_soundness_dec (f : FunDef) (lenvDec : LabelEnvDec)
    (enumEnv : EnumEnv) (funEnv : AssocMap Id FunDef) (fte : FunTypingEnv)
    (args : List Value) (heap : Heap)
    (hdec : SoundnessAssumptions.checkDecidable f lenvDec enumEnv funEnv fte heap args = true)
    (e : RuntimeError) (hna : ¬e.isAcceptable) :
    ∀ n, run n (initState f funEnv args (enumEnv := enumEnv) (heap := heap)) ≠ .error e
```

The single boolean `checkDecidable` combines:
1. `check_fun_dec` — algorithmic type checking of the function
2. `checkFunEnv` — all callees are well-typed (12 checks per function,
   including label-environment-to-blocks consistency)
3. Argument/heap/parameter well-formedness (decidable by construction)

Because `checkDecidable` returns `Bool`, the proof obligation `(by rfl)`
reduces entirely at the Lean kernel level — no proof term is needed.

A backward-compatible corollary `type_soundness_dec_no_danglingRef`
specialises to `danglingRef`, matching the original signature used in
runtime tests.

### Tests and practical meaning (`Tests/Runtime/AllTests.lean`)

Each test section in `AllTests.lean` follows the same pattern:

1. **Define a heap** with allocated values
2. **`#guard` execution halts**: `(run N (initState f funEnv args heap)).isHalted`
3. **Prove no preventable errors**: `type_soundness_dec_no_danglingRef f lenvDec funEnv fte args heap (by rfl)`

For example:

```lean
-- Execution succeeds
#guard (run 200 (initState t empty args twoStructsHeap.1)).isHalted

-- Type soundness certificate
theorem ext_writes_join_t_true_no_danglingRef :
    ∀ n loc, run n (initState t empty args twoStructsHeap.1)
             ≠ .error (.danglingRef loc) :=
  type_soundness_dec_no_danglingRef t t_lenvDec empty empty args twoStructsHeap.1 (by rfl)
```

The `#guard` confirms the program actually runs and terminates (the soundness
theorem does not guarantee termination). The `type_soundness_dec_no_danglingRef`
certificate uses the backward-compatible corollary to prove that *for any
fuel bound*, the program never encounters a dangling reference. The general
`type_soundness_dec` theorem actually rules out all 8 non-acceptable error types — the `danglingRef`-specific corollary is used in tests for
readability. Together, these demonstrate that the soundness statement is
practically meaningful: it applies to concrete programs with concrete heaps
and produces a machine-checked safety guarantee.

The test suite covers programs with borrowing, mutable references, field
access, function calls, control-flow joins, loops, packing/unpacking records,
and aliasing patterns — all drawn from the Move bytecode verifier's own test
suite.

### Test environment construction (`DecidableTypeEnv.lean`)

Writing type-checking tests requires constructing `LabelEnvDec` values that
the algorithmic checker can verify by `rfl` reduction. For single-block
functions this is straightforward — `mkLabelEnvDec f` derives the initial
decidable environment from the function's parameters and locals. For
multi-block programs with control-flow joins (branches, loops), the label
environment must include entries for each block with the correct path graph,
which involves abstract references (`Aref`) that the checker assigns
dynamically.

To decouple test environments from the checker's internal numbering, we
provide two mechanisms:

1. **`freshenBlockEnv f env`** (`DecidableTypeEnv.lean`): replaces template
   `.refid N` values in a `TypeEnvDec` with fresh refids that don't collide
   with the function's parameter/local declarations. It uses
   `collectFreshenableRefIds`, which only collects refids from *valid*
   (initialized) variable entries, siteEnv, and pathEnv — skipping invalid
   or uninitialized variable entries whose refids come from the FunDef
   signature and must not be altered. This makes `freshenBlockEnv` safe to
   apply uniformly to *all* block entries: for environments derived directly
   from the function signature (entry blocks, branch targets with only
   parameter refs), no valid-var refids are found and the function is a
   no-op; for join-point templates with hand-crafted valid vars, it shifts
   their template refids to a safe range. Multi-block tests use the idiom
   `let f := freshenBlockEnv parsed_t` and apply `f` to every block entry.

2. **`extendRefSubst`** (`AlgorithmicTypeChecking.lean`): during subsumption
   checking, after the initial substitution σ is computed from valid
   variables, `extendRefSubst` uses backtracking search (`findRefExtension`)
   to pair remaining unmapped label-environment refids with unmatched checker
   refids. The pairing is validated by `regexSubsumedBy` path checks, making
   it order-independent — the test environment's refid ordering need not match
   the checker's.

Together, these let multi-block test environments (e.g.,
`subtree_writes_release.lean` with 5 intermediate abstract references and a
7-node path graph) be written with simple, readable template values rather
than reverse-engineered checker constants. The soundness of this extension is
proved in `AlgorithmicTypingSoundness.lean` (`findRefExtension_keys_refid`,
`findRefExtension_values_not_root`).

---

## Part II — Proof Architecture

### Why soundness assumptions are reasonable

`SoundnessAssumptions` captures properties of the *runtime configuration*
that the type system does not enforce syntactically but that hold for any
well-formed program entry point:

- **`args_compatible`**: each argument value matches its declared parameter type
  (e.g., an integer argument for a `u64` parameter). This is the caller's
  obligation when invoking a function.
- **`params_nodup`**: parameter names are distinct. This is a syntactic
  property of the function definition.
- **`param_refs_distinct`** / **`param_refs_not_root`**: abstract references
  in ref-typed parameters are pairwise distinct and none is `.root`. This
  reflects the Move convention that each parameter gets its own abstract
  identity.
- **`heap_wf`**: all readable heap locations are within bounds. This holds
  trivially for a freshly allocated heap.
- **Label-environment properties** (`lenv_wf`, `lenv_var_tracked`,
  `lenv_var_unique`, etc.): well-formedness of the label environment provided
  by the type checker. These are established by `check_fun_dec` and verified
  by `checkFunEnv`.

All assumptions are *decidable*: `checkDecidable` evaluates them as a
conjunction of boolean checks. The `(by rfl)` proof in test theorems confirms
that the Lean kernel can verify every assumption by computation.

### Proof structure: preservation and progress

The soundness proof follows the standard preservation-and-progress pattern,
adapted for a small-step interpreter with explicit fuel:

```
type_soundness
  └── safe_run_no_unacceptable_error   (fuel induction)
      └── safe_step                    (one-step safety preservation)
          ├── preservation             (WellTypedState preserved by step)
          └── step_error_is_acceptable (errors from well-typed state are acceptable)
```

**`SafeExecState`** defines safety: running states have a `WellTypedState`
and `StackSafe` witness; halted states are safe; error states must satisfy
`e.isAcceptable` (only `divisionByZero`, `outOfFuel`, `aborted`,
`vectorError`, `variantMismatch`). Any
non-acceptable error contradicts safety.

**Progress** (`Progress.lean`) proves `step_error_is_acceptable`: if a
well-typed state steps to an error, that error is acceptable. This covers
all 8 preventable error types (including vector and enum operations):
- `danglingRef`: contradicted by `rmap_live` (references map to valid heap locations)
- `uninitializedVar`: contradicted by `var_consistent` (valid variables have values)
- `uninitializedSite`: contradicted by `site_consistent` (typed sites have values)
- `unknownLabel`: contradicted by `lenv_labels_in_blocks` (label env entries have blocks)
- `unknownFunction`: contradicted by `funEnv_typed` and `FunTypeSafe`
- `arityMismatch`: contradicted by `types_conform` length chains
- `typeMismatch`: contradicted by type-directed value matching (e.g., bool-typed
  values are `.bool`, ref-typed values are `.ref`, record-typed values are `.record`)
- `invalidFieldAccess`: not produced by the current step function

**Preservation** (`Preservation.lean`) is the heart of the proof: for each
typing rule, when the interpreter takes a step, the resulting machine state
admits a new `WellTypedState` (and `StackSafe` is maintained). The file
contains one case proof per typing rule (~41 cases, including 8 for vector
and 4 for enum operations), plus inversion lemmas that extract hypotheses from each
`typecheck_stmt` constructor.

### Regex-based path tracking (`Structures/Regex.lean`, `Types.lean`)

The central technical device in MoveLight is representing the *borrow graph*
— the set of reachability relationships between abstract references — as a
map from pairs of references to **regular expressions** over path elements:

```
pathEnv.paths : (Aref × Aref) → Regex PathElement
```

A path element is `.field f` (a record field access), `.root_to_var x` (a
link from the local root to variable `x`), or `.vecElem` (a vector element
access, used by the vector extension). The regex
`pathEnv.paths (u, v)` describes *all* concrete field paths by which `v` is
reachable from `u` in the current borrow structure. The regex language
(`Structures/Regex.lean`) supports the standard constructors — `empty`, `ε`
(empty word), `char a`, `dot` (wildcard), `union`, `concat`, `star` — plus
**Brzozowski derivatives** (`deriv re a`), whose semantics is:

```
interpret_regex (deriv re a) w  ⟺  interpret_regex re (a :: w)
```

Derivatives arise naturally when a new reference is created by extending an
existing one with a field path. If `s` is an existing reference and we
create `z = &s.f`, the paths *from* `z` to any reference `v` are exactly the
derivative of `s`'s paths to `v` with respect to the field `f`:

```lean
-- update_with_extension z s [.field f] pe:
paths' (z, v) := der (G (s, v)) [.field f]   -- = ∂[field f] G(s, v)
paths' (u, z) := G (u, s) ∘ [.field f]       -- = G(u,s) ⬝ ⌜field f⌝
```

This is the key insight: Brzozowski derivatives let us compute the path
graph of a sub-reference *symbolically*, without enumerating concrete paths.

**Path graph operations.** Each typing rule transforms the path environment
via one of several operations:

| Operation | Used by | Effect on `pathEnv` |
|---|---|---|
| `update_with_extension z s p` | `borrowField`, `borrowMut`, `borrowImm`, `vecImmBorrow`, `vecMutBorrow` | Add ref `z`; paths to `z` extend through `p`, paths from `z` are derivatives by `p` |
| `update_with_epsilon z s` | `copy` (ref type) | Shorthand for `update_with_extension z s []` — `z` is an alias of `s` with identity paths |
| `delete_ref_node r` | `readRef`, `release` | Remove `r` from tracked refs; clear all its edges (also used as garbage collection by other rules) |
| `delete_ref_node r` (as gc) | `writeRef`, `assign` (valid), `vecLen`, `vecPopBack`, `vecPushBack`, `vecSwap` | Remove `r` from tracked refs after the reference is consumed |
| `consume_ref_transfer r r'` | `freeze` | Remove `r`, transfer incoming edges to `r'` (union of old `r'` and `r` edges) |
| `extend_with_star t s` | `call` (path connection) | Add `t →[·★] s` and `s →[·★] t` paths — the callee may have created arbitrary relationships |

**Decidable path checks.** The typing rules query the path graph via
`check_outbound` and `not_borrowed`, both of which ask whether certain
regexes accept only the empty word (or nothing at all). The decidable
checker (`AlgorithmicTypeChecking.lean`) answers these queries by:

1. **Simplifying** the regex (`simplify`): eliminates derivatives and nested
   constructs, producing a derivative-free regex.
2. **Testing emptiness** (`only_matches_empty`): a structural boolean check
   on the simplified regex.

Both steps are proved sound (`simplify_preserves_semantics`,
`only_matches_empty_sound`), establishing that the boolean check is a
conservative approximation of the semantic question. In practice, `simplify`
is precise enough that no false positives arise for the Move test suite.

**Role in preservation.** The regex representation is what makes the
invariant `rmap_paths` (`PathReflectedInHeap`) maintainable across
preservation steps. When a new reference is created (e.g., by borrowing a
field), the derivative-based path update exactly mirrors how the concrete
heap location of the new reference relates to the parent's location. The
preservation proof for each rule must show that the regex transformation
faithfully reflects the heap transformation — for instance, that
`der (G(s, v)) [.field f]` accepts a path `p` iff following `[.field f] ++
p` from `s` reaches `v` in the heap, which is exactly the semantics of
Brzozowski derivatives.

### Weakening and subsumption (`Weakening.lean`)

At control-flow joins (`jump`, `branch`), the current environment `env` may
differ from the label environment `envL` — for instance, different branches
may have allocated different abstract references. The typing rules require
`TypeEnv.subsumes envL env`, meaning `envL` is *at least as restrictive* as
`env` (it may track more paths).

The **weakening theorem** (`typecheck_stmt_weaken`) proves:

> If `typecheck_stmt lenv envL s retTypes` and `TypeEnv.subsumes envL env`,
> then `typecheck_stmt lenv env s retTypes`.

The proof proceeds by induction on the typing derivation, threading the
substitution `σ` through each rule. This is the largest single proof in the
development (~5800 lines), because every rule that allocates fresh references
must show that the extended substitution preserves all subsumption invariants
(injectivity, path inclusion, reference tracking, freshness).

Key helper lemmas include:
- `subsumes_trans`: transitivity of subsumption (compose substitutions, use
  `Perm.map` and `Perm.trans` for reference lists)
- `check_outbound_weaken`: outbound-path checks transfer through subsumption
- `not_borrowed_weaken`: not-borrowed checks transfer via path inclusion
- `populate_call_outputs_subsumes`: subsumption is preserved through the
  sequence of output-site allocations in function calls

### How call and return typing work

**Call** is the most complex typing rule. It performs several steps:

1. **Input checking**: argument sites must conform to the callee's parameter
   types, and mutable inputs must be *isolated* (no aliasing paths between
   mutable arguments and other arguments).
2. **Output allocation**: `populate_call_outputs` iterates over the declared
   return types, allocating fresh abstract references for reference-typed
   outputs and inserting them into the path environment.
3. **Path connection**: `call_connect_inputs_outputs` links the caller's
   input references to the callee's output references using
   `extend_with_star` (adding `r →[★] s` paths), reflecting that the callee
   may have created arbitrary borrowing relationships.

At the preservation level, `preservation_call` must:
- Look up the callee's `FunTypeSafe` witness (from `funEnv_typed`)
- Allocate arguments on a fresh heap region (`allocArgs`)
- Construct a `WellTypedState` for the callee's entry block
- Push the current frame onto the stack with a `StackSafe` witness

**Return** restores the caller's frame from the stack. The `ret` typing rule
ensures returned references don't borrow locals (condition 2), mutable
returns have trivial outbound paths (condition 3), and no two returns alias a
mutable reference (condition 4). At preservation time, `preservation_ret`
must show that the caller's `WellTypedState` can be reconstructed from
`StackSafe`, with the return values populating the caller's result sites.

### Other typing rules: pragmatics

| Rule | Key invariant maintained |
|---|---|
| `borrowImm` / `borrowMut` | Fresh ref `r` added to `pathEnv`; path from root through variable recorded. Mutable borrows require the variable to be mutable. |
| `readRef` | Consumes the reference site and its abstract ref (`delete_ref_node`). The value is read from the heap via `rmap`; `rmap_live` ensures the location is valid. |
| `writeRef` | `check_outbound` ensures no live alias observes the write. The ref is garbage-collected (`garbage_collect` removes it from `pathEnv`). Preservation must show the written value matches the expected type at the target location. |
| `freeze` | Converts a mutable borrow to immutable via `consume_ref_transfer`: the old ref is removed, a fresh ref takes its paths. This models downgrading write access. |
| `move` / `copy` | Move invalidates the source variable. Copy of a reference type allocates a fresh ref with `update_with_epsilon` (parallel identity). Both require `not_borrowed` for moves. |
| `borrowField` / `borrowMutField` | Creates a sub-reference at a field offset via `update_with_extension r s [.field f]`, recording that `r` reaches into `s` through field `f`. |
| `assign` (valid) | Compound operation: borrows the variable mutably, writes the new value, then garbage-collects the temporary borrow. |
| `assign` (invalid) | Re-initialises a moved-from variable. The new type must be *compatible* with the original declaration. |

### Key preservation invariants (`WellTypedState`)

The `WellTypedState` structure (35 fields) ties the abstract type world to
the concrete machine state. The most important invariants are:

**Value–type correspondence:**
- `var_consistent`: every valid variable in `varEnv` has a value in the
  variable store, and that value matches its type via the reference map
  (`rmap`).
- `site_consistent`: similarly for sites in `siteEnv` and the site store.
- `rmap_has_type`: every mapped abstract reference points to a heap location
  whose value has the expected basic type.

**Reference map coherence:**
- `rmap_live`: every mapped reference points to a readable heap location (no
  dangling pointers).
- `rmap_paths` (`PathReflectedInHeap`): if the path graph records a path
  from `r1` to `r2`, then `rmap` maps them to heap locations where `r2`'s
  location is reachable from `r1` by following the corresponding field path.
  This is the central semantic invariant that connects the abstract path
  graph to the concrete heap.
- `rmap_root_none`: the root reference is never mapped (it is purely a
  static anchor for the path graph).

**Reference tracking:**
- `varEnv_refs_in_pathEnv` / `siteEnv_refs_in_pathEnv`: every abstract
  reference mentioned in a valid variable or site entry appears in
  `pathEnv.refs`.
- `live_refs_unique`: no two distinct valid entries share the same abstract
  reference. This is critical for proving that operations on one reference
  don't corrupt another.

**Path graph well-formedness:**
- `paths_from_non_member_empty` / `paths_to_non_member_empty`: references not
  in `pathEnv.refs` (and not `.root`) have no paths to or from any other
  reference. This ensures that garbage-collected references are truly dead.
- `no_paths_to_root`: only `.root` itself has a path to `.root` (and that
  path is empty). This prevents circular borrowing from the root.
- `root_path_coherence`: a path `root →[root_to_var x] r` exists iff
  variable `x` is valid with a reference whose abstract location matches `r`.
- `self_loop_only_empty`: self-loops in the path graph only accept the empty
  path. This ensures reflexive paths don't spuriously satisfy non-trivial
  path queries.

**Stack and environment:**
- `blocks_typed`: every block in the current function type-checks against its
  label-environment entry.
- `lenv_var_tracked` / `lenv_var_unique`: label-environment entries maintain
  the same reference-tracking invariants as the current environment. This is
  necessary for `typecheck_stmt_weaken` to fire at jump/branch sites.
- `funEnv_typed`: every function in the function environment satisfies
  `FunTypeSafe`, ensuring that calls can construct callee `WellTypedState`
  witnesses.
- `lenv_labels_in_blocks`: every label in the label environment has a
  corresponding block in the current frame. This ensures `jump`/`branch`
  targets are always resolvable (rules out `unknownLabel`).
- `has_return_info`: non-top-level frames always have return info. This
  ensures the `ret` handler can always find the caller's return
  configuration (rules out `typeMismatch "no return info"`).

**Enum well-formedness:**
- `enumEnv_consistent`: the machine's `enumEnv` matches the type
  environment's `enumEnv` (invariant: `enumEnv` never changes during
  execution).
- `enum_qualified_nodup`: qualified field names produced by
  `allEnumFieldTypes` are unique per enum definition. This ensures the
  flat encoding produces well-formed field type maps.
- `enum_names_nodup` / `enum_variant_nodup` / `enum_fields_nodup`:
  syntactic uniqueness of enum names, variant names within each enum,
  and field names within each variant. These support the flat encoding's
  field map construction.
- `defaultValues_typed`: `defaultValue` produces well-typed fill values
  for all field types in the enum environment. This is needed by
  `packVariant` preservation, where `buildFlatVariantFields` fills
  inactive variants' fields with default values.

These invariants are established once by `initState_safe` and then maintained
inductively by each preservation case. The interplay between reference
tracking, path graph well-formedness, and the reference map is what makes the
Move borrow-checking discipline sound: the type system's abstract graph
faithfully reflects the concrete heap's reference structure at every step.

---

## Part III — Vector Extension

MoveLight includes a **vector extension** that models Move's built-in
`vector<T>` type and its 8 bytecode operations. Vectors interact with the
borrow checker: elements can be borrowed immutably or mutably through a
vector reference, and mutations (push, pop, swap) require exclusive access.
The extension is fully integrated into the type system and the soundness
proof — all 8 vector operations have preservation, progress, and weakening
cases with no `sorry` placeholders.

### Syntax

Vector types use the `BasicMoveType` constructor `tvec T`, where `T` is the
element type. At runtime, vector values have the form `Value.vec T elems`,
where `elems : List Value`.

**Expressions** (used in `letBind s expr cont`):

| Constructor | Parameters | Result type |
|---|---|---|
| `vecPack T elems` | element sites of type `T` | `.basic (.tvec T)` |
| `vecLen src` | vector reference site | `.basic .u64` |
| `vecImmBorrow src idx` | vector ref + `u64` index | `.ref T rf .siteBorrowImm` |
| `vecMutBorrow src idx` | mutable vector ref + `u64` index | `.ref T rf .siteBorrowMut` |
| `vecPopBack src` | mutable vector reference | `.basic T` |

**Statements** (standalone, with continuation):

| Constructor | Parameters | Effect |
|---|---|---|
| `vecUnpack T results src cont` | vector value site → result sites | distribute elements |
| `vecPushBack ref val cont` | mutable vector ref + value | append element |
| `vecSwap ref idx1 idx2 cont` | mutable vector ref + two `u64` indices | swap elements |

### Typing rules

All vector typing rules follow the core MoveLight discipline: sites are
consumed after use, fresh abstract references are allocated for borrows, and
`check_outbound` ensures exclusive access for mutations.

**`let_bind_vecPack`** — Pack values into a vector:
```
siteEnv(e_i) = .basic T    for each element site e_i
notIn(siteEnv, s)           List.Nodup(elems)
siteEnv' = deleteAll(siteEnv, elems) + {s ↦ .basic (.tvec T)}
────────────────────────────────────────────────────────────────
typecheck_stmt lenv env (letBind s (vecPack T elems) cont) retTypes
```
No path environment changes — vectors are values, not references.

**`vecUnpack_rule`** — Distribute vector elements to sites:
```
siteEnv(src) = .basic (.tvec T)
notIn(siteEnv, r_i)    for each result site r_i
List.Nodup(results)
siteEnv' = addVecSites T (delete siteEnv src) results
────────────────────────────────────────────────────────────────
typecheck_stmt lenv env (vecUnpack T results src cont) retTypes
```
`addVecSites T se [r₁, ..., rₙ]` inserts `{r_i ↦ .basic T}` for each
result site. No path environment changes.

**`let_bind_vecLen`** — Read vector length through a reference:
```
siteEnv(src) = .ref (.tvec T) r isBor
siteEnv' = delete(siteEnv, src) + {s ↦ .basic .u64}
pathEnv' = delete_ref_node(pathEnv, r)
────────────────────────────────────────────────────────────────
typecheck_stmt lenv env (letBind s (vecLen src) cont) retTypes
```
The vector reference `r` is consumed (`delete_ref_node`) after the length is read.

**`let_bind_vecImmBorrow`** — Borrow an element immutably:
```
siteEnv(src) = .ref (.tvec T) s_ref isBor
siteEnv(idx) = .basic .u64
freshRefInEnv(rf, env)
[if isBor = .siteBorrowMut: check_outbound(pathEnv, s_ref)]
siteEnv' = delete(delete(siteEnv, src), idx) + {s ↦ .ref T rf .siteBorrowImm}
pathEnv' = update_with_extension(rf, s_ref, [.vecElem], pathEnv)
────────────────────────────────────────────────────────────────
typecheck_stmt lenv env (letBind s (vecImmBorrow src idx) cont) retTypes
```
A fresh abstract reference `rf` is allocated for the borrowed element. The
path `s_ref →[vecElem] rf` records that `rf` is reachable from the vector
reference through a vector element access. This uses the same
`update_with_extension` mechanism as `borrowField`, but with `.vecElem`
instead of `.field f`.

**`let_bind_vecMutBorrow`** — Borrow an element mutably:
```
siteEnv(src) = .ref (.tvec T) s_ref .siteBorrowMut
siteEnv(idx) = .basic .u64
freshRefInEnv(rf, env)
check_outbound(pathEnv, s_ref)
siteEnv' = delete(delete(siteEnv, src), idx) + {s ↦ .ref T rf .siteBorrowMut}
pathEnv' = update_with_extension(rf, s_ref, [.vecElem], pathEnv)
────────────────────────────────────────────────────────────────
typecheck_stmt lenv env (letBind s (vecMutBorrow src idx) cont) retTypes
```
Requires a *mutable* vector reference. The `check_outbound` condition
ensures the vector is not aliased — the same exclusivity requirement as
`writeRef` and `borrowMutField`.

**`let_bind_vecPopBack`** — Remove and return the last element:
```
siteEnv(src) = .ref (.tvec T) r .siteBorrowMut
check_outbound(pathEnv, r)
siteEnv' = delete(siteEnv, src) + {s ↦ .basic T}
pathEnv' = delete_ref_node(pathEnv, r)
────────────────────────────────────────────────────────────────
typecheck_stmt lenv env (letBind s (vecPopBack src) cont) retTypes
```
Mutates the vector through the heap, so requires exclusive access.
The reference is consumed after the operation.

**`vecPushBack_rule`** — Append an element:
```
siteEnv(refSite) = .ref (.tvec T) r .siteBorrowMut
siteEnv(valSite) = .basic T
check_outbound(pathEnv, r)
siteEnv' = delete(delete(siteEnv, valSite), refSite)
pathEnv' = delete_ref_node(pathEnv, r)
────────────────────────────────────────────────────────────────
typecheck_stmt lenv env (vecPushBack refSite valSite cont) retTypes
```
Both the reference and value sites are consumed. The vector reference is
garbage-collected because the mutation completes.

**`vecSwap_rule`** — Swap two elements:
```
siteEnv(refSite) = .ref (.tvec T) r .siteBorrowMut
siteEnv(idx1) = .basic .u64
siteEnv(idx2) = .basic .u64
check_outbound(pathEnv, r)
siteEnv' = delete(delete(delete(siteEnv, idx2), idx1), refSite)
pathEnv' = delete_ref_node(pathEnv, r)
────────────────────────────────────────────────────────────────
typecheck_stmt lenv env (vecSwap refSite idx1 idx2 cont) retTypes
```
Consumes all three sites; the reference is garbage-collected.

### Operational semantics

At runtime, vector operations interact with both the site store and the heap:

| Operation | Reads | Writes | Error conditions |
|---|---|---|---|
| `vecPack` | element sites | site store (new vector value) | uninitialized element |
| `vecUnpack` | src site | site store (element values) | length mismatch |
| `vecLen` | heap (vector via ref) | site store (length as `u64`) | dangling ref, type mismatch |
| `vecImmBorrow` | heap (vector via ref) | heap (alloc element), site store (new ref) | dangling ref, index out of bounds |
| `vecMutBorrow` | heap (vector via ref) | heap (alloc element), site store (new ref) | dangling ref, index out of bounds |
| `vecPopBack` | heap (vector via ref) | heap (shortened vector), site store (last element) | dangling ref, empty vector |
| `vecPushBack` | heap (vector via ref), val site | heap (extended vector) | dangling ref |
| `vecSwap` | heap (vector via ref), two index sites | heap (swapped vector) | dangling ref, index out of bounds |

**Heap allocation for borrows.** `vecImmBorrow` and `vecMutBorrow` *allocate*
the borrowed element on the heap (`m.heap.alloc elem`), producing a fresh
location. The result site receives a reference to this new location. This
matches Move's semantics where borrowing a vector element creates a pointer
to a heap-allocated copy of that element.

**The `vectorError` runtime error.** Index out-of-bounds, popping from an
empty vector, and length mismatches during unpack all produce `vectorError`.
This error is *acceptable* — the type system does not track vector lengths
statically, so these errors cannot be prevented by typing alone.

### Value typing

The `HasType` relation includes a vector case:
```
HasType.vec : ∀ (elems : List Value) (elemTy : BasicMoveType),
    (∀ v, v ∈ elems → HasType v elemTy) →
    HasType (.vec elemTy elems) (.tvec elemTy)
```

A vector value has type `tvec T` if every element has type `T`.

### Path environment: the `.vecElem` path element

The `PathElement` type is extended with `.vecElem`:
```
inductive PathElement where
  | field : Field → PathElement
  | root_to_var : Var → PathElement
  | vecElem : PathElement
```

When `vecImmBorrow` or `vecMutBorrow` creates a new element reference `rf`
from a vector reference `s_ref`, the path graph is updated via
`update_with_extension rf s_ref [.vecElem]`. This records:
- **Paths to `rf`**: `G'(u, rf) = G(u, s_ref) · ⌜vecElem⌝` — reachable
  by extending any path to the vector with `vecElem`.
- **Paths from `rf`**: `G'(rf, v) = ∂[vecElem] G(s_ref, v)` — the
  Brzozowski derivative of the vector's outgoing paths by `vecElem`.

The `fieldPathOf` function maps `.vecElem` to the empty list (vector element
access is not a structural field traversal in the heap), allowing the
preservation proof to connect the abstract path graph to the concrete heap
location produced by `heap.alloc`.

### Soundness proof structure

The vector extension adds 8 cases to each of the three main proof files:

**Preservation** (`Preservation.lean`): 8 helper theorems, one per operation.
Each reconstructs all 35 `WellTypedState` fields for the post-step machine.
The borrow operations (`vecImmBorrow`, `vecMutBorrow`) are the most complex
— they mirror `preservation_borrowField` / `preservation_borrowMutField`,
using `update_with_extension` with `[.vecElem]` and proving freshness of the
allocated heap location. The heap-modifying operations (`vecPopBack`,
`vecPushBack`, `vecSwap`) follow the pattern of `preservation_writeRef`,
showing that heap writes preserve `rmap_live`, `rmap_paths`, and
`rmap_has_type`.

**Progress** (`Progress.lean`): 8 cases in `step_error_is_acceptable` (each
error from a well-typed vector operation is acceptable) and 8 cases in
`step_danglingRef_source` (vector operations that access the heap can
produce dangling-ref errors, but `WellTypedState` invariants — specifically
`site_consistent`, `rmap_live`, and `rmap_has_type` — prevent them).

**Weakening** (`Weakening.lean`): 8 cases in `typecheck_stmt_weaken`. Each
shows that if a vector typing rule holds under a more restrictive
environment `envL`, it also holds under a less restrictive `env` related by
`TypeEnv.subsumes`. The `vecUnpack` case required new helper lemmas
(`SiteEnvSubstEquiv_addVecSites`, `site_tracked_addVecSites`,
`RefsUnique_addVecSites`) mirroring the existing `addFieldSites` lemmas for
record unpacking.

### Design decisions

1. **`vectorError` is acceptable.** Unlike dangling references or type
   mismatches, vector index bounds cannot be tracked statically in MoveLight's
   type system (it has no dependent types or refinement types). The design
   follows Move's own approach: the bytecode verifier does not prevent
   out-of-bounds vector access.

2. **Element borrows allocate on the heap.** `vecImmBorrow` and
   `vecMutBorrow` allocate the borrowed element at a fresh heap location
   rather than returning a pointer into the vector's storage. This
   simplifies the preservation proof (the fresh location is guaranteed not to
   alias any existing reference) and matches the Move VM's semantics.

3. **`.vecElem` vs `.field f`.** Vector element access uses a dedicated
   path element `.vecElem` rather than reusing `.field`. This avoids
   conflating vector indexing (which is uniform — all elements have the same
   type) with record field access (which is heterogeneous). In `fieldPathOf`,
   `.vecElem` maps to `[]` (empty), reflecting that the heap allocation for
   a borrowed element does not involve structural field traversal.

4. **Same `update_with_extension` machinery.** The borrow operations reuse
   the existing regex-based path tracking infrastructure. No new path
   operations were needed — `update_with_extension rf s [.vecElem]` works
   identically to `update_with_extension rf s [.field f]`, inheriting all
   existing soundness lemmas for derivatives and path graph updates.

---

## Part IV — Enum Extension

MoveLight includes an **enum extension** that models Move's `enum` types —
tagged variants with named fields. Enums interact with the borrow checker:
variant fields can be borrowed through references (both immutably and
mutably), and `variant_switch` dispatches on the runtime variant tag.
The extension is fully integrated into the type system and the soundness
proof — all 4 enum operations have preservation, progress, and weakening
cases with no `sorry` placeholders. Multi-variant enums are fully supported.

### Syntax

Enum types use the `BasicMoveType` constructor `tenum name`, where `name`
identifies the enum definition in an `EnumEnv`. At runtime, enum values have
the form `Value.variant vname ename fields`, where `vname` is the variant
name, `ename` is the enum type name, and `fields : List (Field × Value)`.

**Enum definitions:**

```lean
structure EnumVariantDef where
  fields : AssocMap Field BasicMoveType

structure EnumDef where
  name : Id
  variants : AssocMap Id EnumVariantDef

abbrev EnumEnv := AssocMap Id EnumDef
```

The `EnumEnv` maps enum type names to their definitions. Each `EnumDef`
contains a map from variant names to `EnumVariantDef` (field type maps).

**Expressions** (used in `letBind s expr cont`):

| Constructor | Parameters | Result type |
|---|---|---|
| `packVariant enumName variantName fields` | field sites with matching types | `.basic (.tenum enumName)` |

**Statements** (non-terminal, with continuation):

| Constructor | Parameters | Effect |
|---|---|---|
| `unpackVariant variantName fields src cont` | enum value or reference site → field sites / borrows | distribute fields |

**Statements** (terminal):

| Constructor | Parameters | Effect |
|---|---|---|
| `variantSwitch src cases` | reference to enum → label per variant | branch to variant-specific handler |

### Typing rules

Enum typing rules follow the core MoveLight discipline: sites are consumed
after use, `EnumEnv` is consulted to resolve field types, and fresh abstract
references are allocated for reference-based unpacking.

**`let_bind_packVariant`** — Pack field values into an enum variant:
```
enumEnv(enumName) = enumDef
enumDef.variants(variantName) = variantDef
siteEnv(a_i) = .basic T_i      for each (f_i, a_i) in fields
variantDef.fields(f_i) = T_i    (field types match)
all fields covered              (completeness)
notIn(siteEnv, s)
siteEnv' = deleteAll(siteEnv, map snd fields) + {s ↦ .basic (.tenum enumName)}
─────────────────────────────────────────────────────────────────────────────────
typecheck_stmt lenv env (letBind s (packVariant enumName variantName fields) cont) retTypes
```
No path environment changes — enum values are owned values, not references.

**`unpackVariant_rule`** — Unpack an owned enum value into field sites:
```
siteEnv(src) = .basic (.tenum ename)
enumEnv(ename) = enumDef
enumDef.variants(variantName) = variantDef
fields match variantDef
siteEnv' = addFieldSites variantDef.fields (delete siteEnv src) fields
─────────────────────────────────────────────────────────────────────
typecheck_stmt lenv env (unpackVariant variantName fields src cont) retTypes
```
Reuses the existing `addFieldSites` helper from record unpacking.

**`unpackVariant_ref_rule`** — Unpack a reference to an enum into field borrows:
```
siteEnv(src) = .ref (.tenum ename) r bk
enumEnv(ename) = enumDef
enumDef.variants(variantName) = variantDef
fields match variantDef
env' = addRefFieldSites r bk variantDef.fields fields {env with siteEnv := delete siteEnv src}
─────────────────────────────────────────────────────────────────────────────────
typecheck_stmt lenv env (unpackVariant variantName fields src cont) retTypes
```
`addRefFieldSites` allocates a fresh abstract reference for each field,
recording paths from the parent reference through each field name. This
mirrors `borrowField` / `borrowMutField` for records.

**`variantSwitch_rule`** — Branch on the runtime variant tag:
```
siteEnv(src) = .ref (.tenum ename) r bk
enumEnv(ename) = enumDef
all variants covered: ∀ vname ∈ enumDef.variants, ∃ label, (vname, label) ∈ cases
all labels well-typed: ∀ (vname, label) ∈ cases, lenv(label) subsumes env
pathEnv' = delete_ref_node(pathEnv, r)
─────────────────────────────────────────────────────────────────────────────────
typecheck_stmt lenv env (variantSwitch src cases) retTypes
```
The enum reference is consumed after the switch. Each branch label must
subsume the current environment (similar to `branch`).

### Operational semantics

At runtime, enum operations interact with the site store, heap, and
control flow:

| Operation | Reads | Writes | Error conditions |
|---|---|---|---|
| `packVariant` | field sites | site store (new variant value) | uninitialized field |
| `unpackVariant` (owned) | src site (variant) | site store (field values) | variant name mismatch |
| `unpackVariant` (ref) | heap (variant via ref) | heap (alloc each field), site store (field refs) | dangling ref, variant mismatch |
| `variantSwitch` | heap (variant via ref) | (none) | dangling ref, variant not in cases |

**Variant mismatch at runtime.** If `unpackVariant` expects variant `V1`
but the runtime value is variant `V2`, the interpreter produces
`variantMismatch`. This error is **acceptable** — the type system does not
track which variant an enum value holds statically (only that it has the
correct enum type).

### Value typing

The `HasType` relation includes a variant case that uses **flat encoding**
— all variants share the same qualified field types via
`allEnumQualifiedFieldTypes`:
```lean
HasType.variant : ∀ (vname ename : Id) (fields : List (Field × Value))
    (fentries : AssocMap Field BasicMoveType),
    allEnumQualifiedFieldTypes enumEnv ename = some fentries →
    (∀ f, lookup fentries f ≠ none → fields.lookup f ≠ none) →
    (∀ f, fields.lookup f ≠ none → lookup fentries f ≠ none) →
    (∀ f bt v, lookup fentries f = some bt → fields.lookup f = some v →
      HasType enumEnv v bt) →
    enumVariantFields enumEnv ename vname ≠ none →
    HasType enumEnv (.variant vname ename fields) (.tenum ename)
```

A variant value has type `tenum ename` if (1) all qualified field types
from **all variants** of the enum are present in the value's field list
(via `allEnumQualifiedFieldTypes`), (2) the value's field domain matches
exactly, (3) each field value matches its declared type, and (4) the
variant name `vname` is a valid variant of the enum.

The key design choice is that `fentries` comes from
`allEnumQualifiedFieldTypes` — which depends only on `ename`, not
`vname` — so **two values of the same enum type always have the same
field type map**, regardless of which variant they hold. This is the
flat encoding that makes `readPath_HasType_transfer` unconditionally true.

Notably, `HasType` takes an `EnumEnv` parameter (required for resolving
variant field types) — this is a cross-cutting change affecting all
`HasType` uses throughout the codebase.

### The `enumEnv` parameter threading

Adding `EnumEnv` to `HasType` is the most pervasive change in this
extension. Every function and lemma that mentions `HasType` must now
thread the `enumEnv` parameter. Key affected signatures include:

- `WellTypedState`: the `enumEnv` is stored as `env.enumEnv` and
  passed to all `HasType` occurrences in the 35 fields
- `StackSafe`: frame-level `HasType` uses the env's `enumEnv`
- `SoundnessAssumptions`: `checkDecidable` verifies that label
  environment entries agree on `enumEnv` (`lenv_enumEnv_eq`)
- `hasType_bool`: the decidable `HasType` check (does not yet handle
  variant or vector values — returns `false` for these)

### Flat encoding and the writeRef transfer lemmas

The core challenge for multi-variant enums is the `writeRef` suffix case:
when two references point to the same heap location, writing through one
must preserve typing for the other. With per-variant field types, two
values of the same enum type could have **different field structures**
(different variant → different fields), making `readPath_HasType_transfer`
false.

**Solution: flat encoding.** Every enum value carries **all** fields from
**all** variants, using qualified names (e.g., `"Ok.val"`, `"Err.msg"`).
Inactive variants' fields are filled with default values. The key function
is `allEnumQualifiedFieldTypes`, which returns the union of all variants'
field types with qualified names:

```lean
def allEnumQualifiedFieldTypes (enumEnv : EnumEnv) (ename : Id)
    : Option (AssocMap Field BasicMoveType) :=
  match enumEnv.lookup ename with
  | some enumDef => some ⟨allEnumFieldTypes enumDef⟩
  | none => none
```

Since `allEnumQualifiedFieldTypes` depends only on `ename` (not on
`vname`), two values of the same enum type always have the **same field
type map**. This makes both transfer lemmas unconditionally true:

```lean
theorem readPath_HasType_transfer (v1 v2 : Value) (bt : BasicMoveType)
    (path : List Field) (h1 : HasType enumEnv v1 bt)
    (h2 : HasType enumEnv v2 bt) (hread : readPath v1 path ≠ none) :
    readPath v2 path ≠ none

theorem typeAtPathV_HasType_determined (v1 v2 : Value) (bt : BasicMoveType)
    (path : List Field) (h1 : HasType enumEnv v1 bt)
    (h2 : HasType enumEnv v2 bt) :
    typeAtPathV enumEnv v1 bt path = typeAtPathV enumEnv v2 bt path
```

No `variantCompatible` hypothesis, no `containsEnum` check, no
`enum_field_compatibility` invariant in `WellTypedState`. The flat
encoding eliminates all of these by construction.

### Soundness proof structure

The enum extension adds 4 cases to each of the three main proof files:

**Preservation** (`Preservation.lean`): 4 helper theorems —
`preservation_packVariant`, `preservation_unpackVariant`,
`preservation_unpackVariant_ref`, and `preservation_variantSwitch`. The
owned pack/unpack cases mirror record pack/unpack. The reference unpack
case mirrors `borrowField` (one fresh reference per field). The
`variantSwitch` case mirrors `branch` — each target label must subsume
the current environment, and the reference is consumed via
`delete_ref_node`.

**Progress** (`Progress.lean`): 4 cases in `step_error_is_acceptable`
(variant mismatch is acceptable) and 4 cases in `step_danglingRef_source`
(enum operations that access the heap cannot produce dangling-ref errors
given `WellTypedState` invariants).

**Weakening** (`Weakening.lean`): 4 cases in `typecheck_stmt_weaken`. Each
shows that enum typing rules transfer through subsumption. The
`unpackVariant_ref_rule` case requires showing that `addRefFieldSites`
preserves subsumption invariants.

### Parser and translator

The enum extension includes a complete **parser** for Move IR enum
syntax, translating `.mvir` files with enum definitions, variant packing,
variant unpacking (both owned and reference), and `variant_switch`
statements into MoveLight AST. Key components:

- `parseEnumDef`: parses `enum Name has { V1 { fields }, V2 { fields } }`
- `parsePackVariant`: translates `EnumName.VariantName { f: s, ... }`
- `parseUnpackVariant`: translates `EnumName.VariantName { f: s } = src`
  (both owned and reference patterns like `&mut EnumName.VariantName { ... }`)
- `parseVariantSwitch`: translates `variant_switch EnumName (&src) { V1: l1, V2: l2 }`

The translator produces a pair `(functions, enumEnv)` via
`parseAndTranslateWithEnums`, where the `EnumEnv` is extracted from parsed
module definitions.

### Design decisions

1. **`variantMismatch` is acceptable.** The type system tracks the enum
   *type* but not which variant a value holds. Unpacking with the wrong
   variant name is a runtime error analogous to `vectorError` for
   out-of-bounds access.

2. **Multi-variant enum soundness via flat encoding.** The core
   challenge for multi-variant enums is the `writeRef` suffix case:
   when two references point to the same heap location, writing through
   one must preserve typing for the other. With per-variant field types,
   two values of the same enum type could have different field
   structures, making `readPath_HasType_transfer` false.

   Our solution uses **flat encoding**: every enum value carries all
   fields from all variants using qualified names (`qualifyField vname f`
   produces `"vname.f"`). The `HasType.variant` constructor uses
   `allEnumQualifiedFieldTypes` which depends only on the enum name,
   not the variant. This makes `readPath_HasType_transfer` and
   `typeAtPathV_HasType_determined` unconditionally true — no
   `variantCompatible` check, no `enum_field_compatibility` invariant,
   and no `checkEnumSingleVariant` restriction needed.

   At runtime, the semantics builds flat variant values via
   `buildFlatVariantFields`, which iterates all variants and fills
   inactive variants' fields with `defaultValue`. The `qualifyField`
   function ensures field names from different variants don't collide
   (e.g., `"Ok.val"` vs `"Err.msg"`).

   This approach replaces the earlier `containsEnum`-conditional
   restrictions and `checkEnumSingleVariant`.

3. **`EnumEnv` as explicit parameter.** Rather than embedding enum
   definitions in the type itself (`BasicMoveType` carries only the enum
   name), the `EnumEnv` is threaded through `HasType`, `WellTypedState`,
   and `SoundnessAssumptions`. This mirrors Move's own architecture where
   enum definitions are module-level and type references are by name.

4. **Reuse of record machinery.** Enum variant fields use the same
   `AssocMap Field BasicMoveType` representation as record fields, and
   the typing rules reuse `addFieldSites` (owned unpack) and
   `addRefFieldSites` (reference unpack). The semantics qualifies
   field names at runtime (via `qualifyField`) to match the flat
   encoding, while the typing rules work with unqualified field
   names — the soundness proof bridges the two representations via
   `buildFlatVariantFields_HasType` and related transfer lemmas.

5. **Conditional borrow restrictions for enum-containing types.**
   When a mutable borrow targets a variable whose type transitively
   contains an enum (`containsEnum τ = true`), the typing rule
   (`let_bind_borrowMut`) additionally requires `not_borrowed x env`
   (no existing borrows of `x`) and invalidates the source variable
   in the continuation environment. This prevents aliased mutable
   writes that could change the variant tag at a shared heap location,
   which would break `readPath_HasType_transfer` for co-borrowers.
   For non-enum types, these conditions are vacuously satisfied
   (the `containsEnum τ → ...` implication is vacuously true and
   the conditional `if` takes the `else` path). The same guard is
   applied to `var_assign_valid`.

6. **`enum_fields_nodup` and `enum_names_nodup` in
   `SoundnessAssumptions`.** The decidable soundness certificate
   (`checkDecidable`) verifies that enum type names are unique,
   variant names are unique within each enum, and field names are
   unique within each variant. These are syntactic well-formedness
   conditions that ensure `allEnumQualifiedFieldTypes` produces
   well-formed field maps. The `defaultValues_typed` check further
   verifies that `defaultValue` produces well-typed fill values for
   inactive variant fields.

### Test coverage

The test suite includes programs from the Move bytecode verifier's enum
test suite:

- **`enum_match`**: variant packing with a 3-variant enum
  (`Threes { One{pos0:u64}, Two{}, Three{pos0:u64} }`),
  `variant_switch` dispatch, field extraction. Includes both runtime
  tests (`#eval`/`#guard`) and a **decidable type soundness certificate**
  (`enum_match_no_danglingRef`) proving that execution with 3 variants
  never produces a preventable error — the key demonstration that
  multi-variant enum soundness works end-to-end.
- **`enum_borrow_field_mutable`**: mutable field borrows through enum
  references, freeze, multi-module examples (type-checking + soundness
  certificate for single-block functions)
- **`enum_two_mutable_unpacks`**: multiple mutable variant unpacks from
  the same reference (type-checking + runtime test)
- **`enum_variant_factor`**: parsing and translation of multi-variant
  enum definitions

---

## Appendix — Syntactic macros (`Lang/Macros.lean`)

MoveLight's AST uses continuation-passing style (CPS): non-terminal
statements carry their continuation as the last argument. Writing programs
directly with `Stmt.letBind`, `Stmt.writeRef`, etc. is verbose. The file
`Lang/Macros.lean` provides Lean macros that closely mirror Move IR syntax
while expanding to the same AST constructors.

### The `;;` operator and StmtBuilder

A `StmtBuilder` is a function `Stmt → Stmt` — it takes a continuation and
produces a complete statement. The right-associative operator `;;` (priority
20) threads continuations:

```lean
infixr:20 " ;; " => fun (f : StmtBuilder) (s : Stmt) => f s
```

For example, `(letsite s ← move x) ;; ret [s]` expands to
`Stmt.letBind s (Expr.usage (Usage.move x)) (Stmt.ret [s])`.

### Macro reference

| Macro | Expands to | Move IR equivalent |
|---|---|---|
| `letsite s ← #n` | `Stmt.letBind s (Expr.intLit n) cont` | `s = n` |
| `letsite s ← copy x` | `Stmt.letBind s (Expr.usage (Usage.copy x)) cont` | `s = copy(x)` |
| `letsite s ← move x` | `Stmt.letBind s (Expr.usage (Usage.move x)) cont` | `s = move(x)` |
| `letsite s ← &x` | `Stmt.letBind s (Expr.usage (Usage.borrowImm x)) cont` | `s = &x` |
| `letsite s ← &mut x` | `Stmt.letBind s (Expr.usage (Usage.borrowMut x)) cont` | `s = &mut x` |
| `letsite s ← *b` | `Stmt.letBind s (Expr.readRef b) cont` | `s = *b` |
| `letsite s ← freeze b` | `Stmt.letBind s (Expr.freeze b) cont` | `s = freeze(b)` |
| `letsite s ← pack("T", fs)` | `Stmt.letBind s (Expr.pack "T" fs) cont` | `s = T { ... }` |
| `letsite s ← borrowField(a, bt, f)` | `Stmt.letBind s (Expr.borrowField a bt f) cont` | `s = &a.T::f` |
| `letsite s ← borrowMutField(a, bt, f)` | `Stmt.letBind s (Expr.borrowMutField a bt f) cont` | `s = &mut a.T::f` |
| `x ::= a` | `Stmt.assign x a cont` | `x = a` |
| `*a ::= b` | `Stmt.writeRef a b cont` | `*a = b` |
| `release s` | `Stmt.release s cont` | `_ = move(s)` (consume) |
| `unpack(fields, src)` | `Stmt.unpack fields src cont` | `T { f: s } = src` |
| `call(rets, fn, args)` | `Stmt.call rets fn args cont` | `rets = fn(args)` |
| `letsite s ← vecPack(T, es)` | `Stmt.letBind s (Expr.vecPack T es) cont` | `s = vec_pack(es)` |
| `letsite s ← vecLen(a)` | `Stmt.letBind s (Expr.vecLen a) cont` | `s = vec_len(a)` |
| `letsite s ← vecImmBorrow(a, i)` | `Stmt.letBind s (Expr.vecImmBorrow a i) cont` | `s = vec_imm_borrow(a, i)` |
| `letsite s ← vecMutBorrow(a, i)` | `Stmt.letBind s (Expr.vecMutBorrow a i) cont` | `s = vec_mut_borrow(a, i)` |
| `letsite s ← vecPopBack(a)` | `Stmt.letBind s (Expr.vecPopBack a) cont` | `s = vec_pop_back(a)` |
| `vecUnpack(T, rs, a)` | `Stmt.vecUnpack T rs a cont` | `rs = vec_unpack(a)` |
| `vecPushBack(a, v)` | `Stmt.vecPushBack a v cont` | `vec_push_back(a, v)` |
| `vecSwap(a, i, j)` | `Stmt.vecSwap a i j cont` | `vec_swap(a, i, j)` |
| `jump l` | `Stmt.jump l` | `jump l` |
| `branch c l1 l2` | `Stmt.branch c l1 l2` | `jump_if (c) l1` |
| `ret sites` | `Stmt.ret sites` | `return sites` |
| `abort s` | `Stmt.abort s` | `abort s` |

### Syntactic differences from Move IR

The macros bring MoveLight syntax close to Move IR, but some differences
remain due to A-normal form and Lean's syntax rules:

1. **A-normal form decomposition.** Move IR allows nested expressions like
   `*move(x) = 0` or `f = &copy(s).S::f`. In MoveLight, each sub-expression
   is bound to a site first:
   ```
   -- Move IR:  *move(x) = 0
   -- MoveLight:
   (letsite s1 ← move var_x) ;;
   (letsite s2 ← #0) ;;
   (*s1 ::= s2) ;;
   ```

2. **Integer literals use `#n`.** Move IR writes bare `0`; MoveLight uses
   `#0` to distinguish integer literals from other terms.

3. **Field borrows carry explicit type arguments.** Move IR writes
   `&mut copy(p).Point::x`; MoveLight writes
   `letsite s ← borrowMutField(s0, .trecord point_entries, field_x)` with
   the parent struct type passed explicitly.

4. **Branch vs jump_if.** Move IR uses `jump_if (move(cond)) L` with
   fall-through. MoveLight uses `branch s "L_true" "L_false"` with both
   targets explicit.

5. **No `Stmt.skip` macro.** The no-op terminal is written as `Stmt.skip`
   directly (rarely used in practice).

### Example

Move IR:
```
t() {
    let a: u64;
    let x: &mut u64;
label b0:
    a = 0;
    x = &mut a;
    *move(x) = 0;
    return;
}
```

MoveLight with macros:
```lean
def t : FunDef := {
  params := []
  returnType := []
  locals := [
    { name := var_a, type := .basic .u64 },
    { name := var_x, type := .ref .u64 (.refid 1) .siteBorrowMut }
  ]
  blocks := [
    { label := "b0"
      body :=
        (letsite s0 ← #0) ;;
        (var_a ::= s0) ;;
        (letsite s1 ← &mut var_a) ;;
        (var_x ::= s1) ;;
        (letsite s2 ← move var_x) ;;
        (letsite s3 ← #0) ;;
        (*s2 ::= s3) ;;
        ret []
    }
  ]
}
```
