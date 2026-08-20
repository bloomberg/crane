# Roadmap

Crane is an evolving extraction system for lowering verified Rocq programs into modern, idiomatic C++. This roadmap outlines the major areas of ongoing and planned development.

---

## 1. Broader Rocq Language Coverage

Crane handles a large subset of Rocq's functional core, including modules, type classes, and coinductive types. Ongoing work includes expanding support for:

* more complex module and functor patterns,
* advanced type class features,
* universe polymorphism edge cases,
* other currently unsupported features.

The goal is to enable extraction of a wider range of Rocq developments without requiring user workarounds.

---

## 2. Improved Testing

A key part of Crane's correctness strategy is **empirical validation**:

* random generation of Rocq programs,
* differential testing against other extractors (e.g. OCaml extraction, [CertiCoq](https://github.com/CertiCoq/certicoq)),
* property-based and fuzz testing of the generated C++,
* runtime detection of issues in the generated C++ with [AddressSanitizer](https://clang.llvm.org/docs/AddressSanitizer.html), [MemorySanitizer](https://clang.llvm.org/docs/MemorySanitizer.html), [ThreadSanitizer](https://clang.llvm.org/docs/ThreadSanitizer.html), and [UndefinedBehaviorSanitizer](https://clang.llvm.org/docs/UndefinedBehaviorSanitizer.html),
* static analysis of the generated C++ with [Infer](https://fbinfer.com/).

Work is ongoing to expand this pipeline and automate the detection of discrepancies.

---

## 3. Enhanced Concurrency and Effects

Crane includes a growing library of monadic effects built on [interaction trees](https://github.com/DeepSpec/InteractionTrees), including IO (console + file), STM, threads, parallelism, clock, directory, environment, path, and temporary file operations. Future extensions include:

* additional effect libraries (state, nondeterminism, etc.),
* streamlined interfaces for defining custom effects,
* richer concurrency abstractions,
* improved performance of the STM backend,
* techniques for reasoning about monadic code.

---

## 4. More Customizable Extraction Rules

Crane's macro language allows developers to tailor how Rocq definitions map to C++ syntax. We plan to:

* add more macro constructs for finer control,
* offer higher-level templates for common extraction patterns,
* improve diagnostics when custom mappings fail,
* provide built-in mappings for more Rocq standard library components.

This will reduce the boilerplate needed when integrating large developments.

---

## 5. Performance of the Generated Code

Extracted C++ should be competitive with what an engineer would write by hand,
and with the OCaml extraction of the same Rocq source. Current and planned work
includes:

* reducing allocation volume — Perceus-style in-place reuse, container mappings
  that match the source's asymptotics, and scoped arenas,
* eliminating recursion so deep inputs cannot overflow the stack, and closing
  the [remaining gap](Reference-Manual.md#shapes-that-still-decline) in that
  pass,
* narrowing the cost of type erasure for dependent types that survive
  extraction,
* extending the benchmark suite beyond the `ParseALot` pipeline so regressions
  are caught on realistic workloads.

---

## 6. Verified Components at Scale

A future goal is to **deploy verified libraries into production** across Bloomberg's C++ systems.
This requires:

* scaling extraction to large Rocq codebases,
* stabilizing Crane's API and generated code conventions,
* strengthening guarantees about interface compatibility,
* providing migration guidance as Crane evolves.

---

## 7. Developer Experience and Tooling

Planned enhancements include:

* improved error messages during extraction,
* better documentation and examples,
* editor tooling and integration with Rocq IDEs,
* utilities for inspecting generated C++,
* quality-of-life improvements for everyday users.
