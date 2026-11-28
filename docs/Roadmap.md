# Roadmap

Crane is an evolving extraction system from verified Rocq programs to
modern, idiomatic C++. This page lists what recently landed and what comes
next, by area. Open defects are tracked as tests in
[`tests/wip`](https://github.com/bloomberg/crane/tree/main/tests/wip).

---

## 1. Mappings

**Done.** Typed mappings replace template strings with data: a
`TypeMapping` or `OperationMapping` instance gives a type's C++ type as a
structured value and states its copy, access, view and lifetime models and
each operation's contract. Instances are selected by imports, ambiguity is an
error, a unit's selected mappings are recorded in its compiled interface and
checked by the units that include its header, and `Crane Show Mapping` /
`Crane Check Mapping` inspect them. Parameter passing follows from what each
function does with each argument (an access analysis over the whole
program), with read and writable views (`std::string_view`, `std::span`)
where a mapping declares them. Every file in `theories/Mapping/` (`Std`,
`StdCore`, `BDE`, the `nat`/`N`/`Z` flavours, GMP, `Real`, `AsciiChar`,
`DequeList`, `Shared`) and the `ST` monad's arrays and references are typed.
See the [Reference Manual](Reference-Manual.md#typed-mappings) and
[Compiler-Pipeline.md](Compiler-Pipeline.md#7-typed-mappings-in-the-pipeline).

**Next.**

* Typed forms for monads, `Crane Extract Skip`, `Crane Extract Void` and
  `Crane Extract Numeral`, which are still commands.
* Acting on the parts of a descriptor that are validated but not yet used by
  code generation: `RegionOwned` and `ManualShared` lifetimes, `DrainWith`
  release plans, value models.
* View parameters for first-class function values, which keep canonical
  parameter forms today.
* Better diagnostics when a mapping's C++ does not compile.

---

## 2. Compiler internals

**Done.** Lowering is typed: every lowered expression carries its C++ type,
every position states what it asks of the value, and every adapter between
the two (boxing, erasure, eta-expansion, regrouping, conversion) is one
decision, `Coerce.decide`, expanded by one finishing pass. Under
`CRANE_CHECK_IR` a value that does not fit its slot fails extraction unless
it is on a shrink-only allowlist. See
[Compiler-Pipeline.md](Compiler-Pipeline.md#61-typed-lowering).

**Next.**

* Shrink the typed-fit allowlist (`unit_tests/typed_fit_allowlist.txt`, 211
  entries). Each entry is a type-reconstruction defect: erased or boxed
  components (47), higher-kinded carriers and monad instances against their
  unfolding (34), promoted variables and instance members (29), other wrong
  value types (29), event families named unapplied (25), callables grouped
  otherwise (22), `itreeF` against `itree` (12), type variables against
  concrete types (8), monad transformers by name (4).
* Typed CppIR phase E: view conversions as coercion plans decided at
  lowering, with `view_args` keeping only cross-argument checks; optionally
  regrouping through `crane::regroup<Into>`.

---

## 3. Rocq language coverage

Crane handles a large subset of Rocq's functional core, including modules,
functors, type classes and coinductive types. Ongoing work:

* more complex module and functor patterns,
* advanced type class features (higher-kinded and rank-2 uses),
* universe polymorphism edge cases,
* value-dependent types that survive extraction, with less type erasure.

---

## 4. Testing

Crane's correctness strategy is empirical validation of the extractor:

* random generation of typed Rocq programs, compared between `vm_compute`
  and the extracted C++ (in use; the defects it finds are filed under
  `tests/wip`),
* differential testing against other extractors (OCaml extraction,
  [CertiCoq](https://github.com/CertiCoq/certicoq)),
* runtime checks with [AddressSanitizer](https://clang.llvm.org/docs/AddressSanitizer.html),
  [UndefinedBehaviorSanitizer](https://clang.llvm.org/docs/UndefinedBehaviorSanitizer.html)
  (`CRANE_CPP_SANITIZE` in the test scripts),
  [ThreadSanitizer](https://clang.llvm.org/docs/ThreadSanitizer.html) and
  [MemorySanitizer](https://clang.llvm.org/docs/MemorySanitizer.html),
* static analysis of the generated C++ with [Infer](https://fbinfer.com/)
  (`scripts/run-infer.sh`),
* the `CRANE_CHECK_IR` boundary checks, on for the whole test suite.

---

## 5. Effects and concurrency

Crane has a library of effects on
[interaction trees](https://github.com/DeepSpec/InteractionTrees): IO
(console and files), STM, threads, futures, clock, directories, environment,
paths and temporary files, plus the `ST` monad for local mutable state.
Planned:

* typed event and monad mappings (section 1),
* additional effect libraries (state, nondeterminism),
* simpler definition of custom effects,
* richer concurrency abstractions and a faster STM backend,
* techniques for reasoning about monadic code.

---

## 6. Performance of the generated code

Extracted C++ should be competitive with hand-written C++ and with the
OCaml extraction of the same source.

**Done.** Perceus-style in-place reuse, scoped arenas, non-atomic reference
counting, shared variants, loopification of tail, tail-modulo-cons and tree
recursion, immortal top-level constants (never counted or freed), a sticky
reference count under `NonAtomicRc` plus `SingleThreaded`, borrowing of pair
components, moves at the last use in loop frames, and
[`Crane Bake`](Reference-Manual.md#crane-bake) for constants computed at
extraction time.

**Next.**

* constant-initialised nodes for baked inductives and lists, which are
  rebuilt at startup today, and baking support for immer containers,
* closing the [remaining loopification gap](Reference-Manual.md#set-crane-loopify--crane-loopify)
  (self-calls inside lambdas and continuations, local fixpoints a machine
  cannot enter),
* extending the benchmark suite beyond `ParseALot`.

---

## 7. Verified components at scale

A goal is to deploy verified libraries in production across Bloomberg's C++
systems. This requires:

* scaling extraction to large Rocq developments,
* stabilizing Crane's API and generated-code conventions,
* guarantees about interface compatibility across separately extracted
  units (compiled interfaces check typed mappings today),
* migration guidance as Crane evolves.

---

## 8. Developer experience

* clearer error messages during extraction,
* editor tooling and integration with Rocq IDEs,
* utilities for inspecting generated C++ and the decisions behind it.
