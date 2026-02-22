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
  dangling-pointer errors** at runtime, under assumptions that are
  **decidable** and **practically satisfiable** (parameter well-formedness,
  heap validity, callee typing).
- We demonstrate this end-to-end on programs drawn from the **Move bytecode
  verifier's own test suite**: each program is type-checked, executed on a
  concrete heap, and certified free of dangling references — all within a
  single `lake build`.

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
│   │   ├── TypeCheckingAlgorithmic.lean       Executable type checker
│   │   ├── AlgorithmicTypingSoundness.lean    Algorithmic ⇒ relational
│   │   └── DecidableTypeEnv.lean              Decidable environment checks
│   │
│   ├── Soundness/
│   │   ├── Defs.lean              WellTypedState, StackSafe, FunTypeSafe
│   │   ├── InitState.lean         Initial state safety, SoundnessAssumptions
│   │   ├── Preservation.lean      Preservation theorem (per-rule case proofs)
│   │   ├── Weakening.lean         Weakening / subsumption lemmas
│   │   ├── StackSafeUtils.lean    Stack frame safety utilities
│   │   ├── Progress.lean          No danglingRef from well-typed states
│   │   └── SafeExec.lean          SafeExecState, iterated safety
│   │
│   └── TypeSoundness.lean         Main theorems: type_soundness, type_soundness_dec
│
├── Structures/                    AssocMap, Regex, ListUtils, PathMap
│
└── Tests/
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
`assign`, `release`, `unpack`, or `call`, where `cont` is the continuation
statement within the same block.

Types are either *basic* (`u64`, `bool`, `unit`, records) or *references*
`ref τ r bk`, carrying a basic content type `τ`, an abstract reference `r :
Aref`, and a borrowing kind `bk` (immutable or mutable). Abstract references
(`Aref`) are either `.root` (the local variable root), `.refid n` (a
placeholder used during type checking), or `.varRef v` (tied to parameter `v`).

### Operational semantics (`Semantics/Smallstep.lean`)

The interpreter defines:

| Definition | Purpose |
|---|---|
| `Machine` | Running state: current frame, call stack, heap |
| `ExecState` | `.running Machine \| .halted vals \| .error err` |
| `step : ExecState → ExecState` | One evaluation step |
| `run (fuel : Nat) : ExecState → ExecState` | Bounded evaluation |
| `initState` | Build initial machine from function, arguments, heap |

Errors include `danglingRef loc` (dereferencing freed memory), as well as
`uninitializedVar`, `typeMismatch`, etc. Type soundness rules out
`danglingRef`; other errors correspond to statically prevented operations.

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
theorem type_soundness (f : FunDef) (lenv : LabelEnv)
    (funEnv : AssocMap Id FunDef) (args : List Value) (heap : Heap)
    (htyped : typecheck_fun f lenv)
    (hfunEnv : ∀ fname fdef, lookup funEnv fname = some fdef
                             → FunTypeSafe fdef funEnv)
    (ha : SoundnessAssumptions f lenv funEnv heap args) :
    ∀ n loc, run n (initState f funEnv args heap) ≠ .error (.danglingRef loc)
```

In words: if a function is well-typed (`typecheck_fun`), every callee is
safely typed (`FunTypeSafe`), and the runtime configuration satisfies the
soundness assumptions, then execution never produces a dangling-reference
error regardless of how many steps are taken.

### Algorithmic type checker (`Typing/Algorithmic/`)

The executable checker mirrors the relational rules:

| File | Role |
|---|---|
| `TypeCheckingAlgorithmic.lean` | `check_stmt_dec`, `check_fun_dec`, `subsumes_bool` |
| `AlgorithmicTypingSoundness.lean` | `check_fun_dec_sound : check_fun_dec f lenvDec = true → typecheck_fun f lenvDec.toLabelEnv` |
| `DecidableTypeEnv.lean` | Decidable `PathEnvDec`, `TypeEnvDec`, `LabelEnvDec`; `checkFunEnv`; `allVarRefsTracked_bool` |

The algorithmic checker uses decidable data structures (`AssocMap`-based
`PathEnvDec` with explicit ref lists and path maps) and boolean checks. Its
soundness theorem `check_fun_dec_sound` bridges to the relational system.

### Decidable soundness (`type_soundness_dec`)

```lean
theorem type_soundness_dec (f : FunDef) (lenvDec : LabelEnvDec)
    (funEnv : AssocMap Id FunDef) (fte : FunTypingEnv)
    (args : List Value) (heap : Heap)
    (hdec : SoundnessAssumptions.checkDecidable f lenvDec funEnv fte heap args = true) :
    ∀ n loc, run n (initState f funEnv args heap) ≠ .error (.danglingRef loc)
```

The single boolean `checkDecidable` combines:
1. `check_fun_dec` — algorithmic type checking of the function
2. `checkFunEnv` — all callees are well-typed (11 checks per function)
3. Argument/heap/parameter well-formedness (decidable by construction)

Because `checkDecidable` returns `Bool`, the proof obligation `(by rfl)`
reduces entirely at the Lean kernel level — no proof term is needed.

### Tests and practical meaning (`Tests/Runtime/AllTests.lean`)

Each test section in `AllTests.lean` follows the same pattern:

1. **Define a heap** with allocated values
2. **`#guard` execution halts**: `(run N (initState f funEnv args heap)).isHalted`
3. **Prove no dangling refs**: `type_soundness_dec f lenvDec funEnv fte args heap (by rfl)`

For example:

```lean
-- Execution succeeds
#guard (run 200 (initState t empty args twoStructsHeap.1)).isHalted

-- Type soundness certificate
theorem ext_writes_join_t_true_no_danglingRef :
    ∀ n loc, run n (initState t empty args twoStructsHeap.1)
             ≠ .error (.danglingRef loc) :=
  type_soundness_dec t t_lenvDec empty empty args twoStructsHeap.1 (by rfl)
```

The `#guard` confirms the program actually runs and terminates (the soundness
theorem only rules out one class of errors — it does not guarantee
termination). The `type_soundness_dec` certificate then proves that *for any
fuel bound*, the program never encounters a dangling reference. Together,
these demonstrate that the soundness statement is practically meaningful: it
applies to concrete programs with concrete heaps and produces a machine-checked
safety guarantee.

The test suite covers programs with borrowing, mutable references, field
access, function calls, control-flow joins, loops, packing/unpacking records,
and aliasing patterns — all drawn from the Move bytecode verifier's own test
suite.

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
  └── safe_run_no_danglingRef          (fuel induction)
      └── safe_step                    (one-step safety preservation)
          ├── preservation             (WellTypedState preserved by step)
          └── no_danglingRef_progress  (well-typed state ≠ danglingRef error)
```

**`SafeExecState`** defines safety: running states have a `WellTypedState`
and `StackSafe` witness; halted states are safe; `danglingRef` errors are
contradictory; other errors are safe (they correspond to operations the type
system permits to fail, such as `outOfFuel`).

**Progress** (`Progress.lean`) shows that `danglingRef` errors arise only
from `readRef` and `writeRef`, and that both succeed when the reference's
abstract location is mapped to a valid heap location — which `WellTypedState`
guarantees via `rmap_live`.

**Preservation** (`Preservation.lean`) is the heart of the proof: for each
typing rule, when the interpreter takes a step, the resulting machine state
admits a new `WellTypedState` (and `StackSafe` is maintained). The file
contains one case proof per typing rule (~25 cases), plus inversion lemmas
that extract hypotheses from each `typecheck_stmt` constructor.

### Regex-based path tracking (`Structures/Regex.lean`, `Types.lean`)

The central technical device in MoveLight is representing the *borrow graph*
— the set of reachability relationships between abstract references — as a
map from pairs of references to **regular expressions** over path elements:

```
pathEnv.paths : (Aref × Aref) → Regex PathElement
```

A path element is either `.field f` (a record field access) or
`.root_to_var x` (a link from the local root to variable `x`). The regex
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
| `update_with_extension z s p` | `borrowField`, `borrowMut`, `borrowImm` | Add ref `z`; paths to `z` extend through `p`, paths from `z` are derivatives by `p` |
| `update_with_epsilon z s` | `copy` (ref type) | Shorthand for `update_with_extension z s []` — `z` is an alias of `s` with identity paths |
| `delete_ref_node r` | `readRef`, `release` | Remove `r` from tracked refs; clear all its edges |
| `garbage_collect r` | `writeRef`, `assign` (valid) | Same as `delete_ref_node` — remove `r` after a write consumes it |
| `consume_ref_transfer r r'` | `freeze` | Remove `r`, transfer incoming edges to `r'` (union of old `r'` and `r` edges) |
| `extend_with_star t s` | `call` (path connection) | Add `t →[·★] s` and `s →[·★] t` paths — the callee may have created arbitrary relationships |

**Decidable path checks.** The typing rules query the path graph via
`check_outbound` and `not_borrowed`, both of which ask whether certain
regexes accept only the empty word (or nothing at all). The decidable
checker (`TypeCheckingAlgorithmic.lean`) answers these queries by:

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

The `WellTypedState` structure (23 fields) ties the abstract type world to
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

These invariants are established once by `initState_safe` and then maintained
inductively by each preservation case. The interplay between reference
tracking, path graph well-formedness, and the reference map is what makes the
Move borrow-checking discipline sound: the type system's abstract graph
faithfully reflects the concrete heap's reference structure at every step.

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
