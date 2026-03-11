# Design Principles

## Goals and Constraints

### What Crane aims to achieve

Crane has two main roles:

1. **Make verified Rocq components deployable in production.**  
   Engineers should be able to take Rocq code, run it through Crane, and
   integrate the resulting C++ directly into existing systems.

2. **Let a small verification team serve many C++ developers.**  
   A handful of Rocq experts can build and maintain verified libraries;
   application teams consume those libraries as "normal" C++.

### The environment we target

Crane is designed with Bloomberg's C++ landscape in mind:

- C++ is the dominant implementation language.
- Code must fit long-standing coding standards (e.g., [BDE style](https://bloomberg.github.io/bde/knowledge_base/coding_standards.html)).
- Readability and maintainability matter as much as raw performance.
- Static analysis, testing, and code review are already widely used.

Crane therefore **optimizes for credibility as well as correctness**:
developers must be able to read the generated C++ and recognize it as
"real code they might have written," not as an opaque artifact from a
foreign toolchain.

---

## Principles

### 1. Readability and idiomatic C++ first

We prefer an extraction that:

- uses familiar C++ constructs (smart pointers, variants, lambdas),
- aligns with established coding guidelines,
- and produces code that is comfortable to review and debug.

Crane is not trying to minimize internal representation size or emulate Rocq syntax one-to-one.
Instead, it aims for **"this looks like a well-written C++ library"**.

**Practical consequence:**  
You should be able to open a Crane-generated file and reason about it using the
same habits you use for hand-written C++: step through with a debugger, skim
for invariants, and review diffs in code review.

---

### 2. Functional structure, C++ surface

Rocq programs are fundamentally functional. Crane keeps that structure visible,
but renders it in idiomatic modern C++:

- algebraic data types become `std::variant`-like shapes,
- pattern matches become structured conditionals,
- higher-order functions become lambdas and callable objects,
- monadic effects become libraries with concrete C++ APIs.

The goal is to **preserve the conceptual shape** of the Rocq program so that
proofs and implementation still "match up" in a human's head.

---

### 3. Memory- and thread-safety as a default

Crane aims for **safe by construction** code:

- smart pointers and value types, instead of raw `new`/`delete`,
- carefully controlled sharing and mutation,
- concurrency built on top of [software transactional memory (STM)](https://en.wikipedia.org/wiki/Software_transactional_memory) style
  abstractions, rather than ad-hoc locking.

The intention is that **races and lifetime bugs are hard to express** in the
generated code, not just hard to test for.

This safety story is complemented (not replaced) by:

- static analysis for memory and thread safety,
- fuzzing and property-based testing of the extracted programs,
- differential testing vs other Rocq extractors.

---

### 4. Pragmatic trust, not fully verified compilation

Crane deliberately *does not* start from a fully verified compiler pipeline in
the style of [CompCert](https://compcert.org/).

Instead:

- acknowledge that verifying the entire extractor would be a large,
  multi-year effort,
- focus on expressive code generation that people will actually use,
- rely on **differential testing and static analysis** to validate the
  extractor itself.

In other words: Crane chooses **practical assurance plus verified source
programs**, rather than delaying useful output until the extractor is fully
proved.

---

### 5. Configurability over hard-coding

Different projects have different C++ "worlds":

- some only use the C++ standard library,
- others use Bloomberg's core libraries ([BDE](https://bloomberg.github.io/bde/)),
- others may have their own foundational libraries.

Crane avoids hard-coding mappings from Rocq to C++.
Instead it provides:

- a **macro language** for custom extraction of Rocq definitions, and
- a way to define **effect interfaces** and monadic APIs with user-chosen
  C++ representations.

This makes Crane **adaptable**:

- you can map Rocq's `option` to `std::optional<T>` or to a house-style
  optional type,
- you can decide how a particular effect (e.g. `IO`, `STM`) should be represented
  and sequenced in C++.

---

### 6. General-purpose, not Bloomberg-locked

While Crane grew out of Bloomberg's needs, it is explicitly designed to be
usable by any Rocq programmer:

- Bloomberg-specific integrations (e.g. BDE) are optional modules,
- the core extraction targets "plain" modern C++,
- the macro and effect mechanisms are open-ended.

You can adopt Crane in a non-Bloomberg codebase and still get idiomatic C++
tailored to your own libraries and conventions.
