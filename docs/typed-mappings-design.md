# Typed Custom Mappings for Crane

## A standalone design for values, views, mutable state, identity handles, and resource lifetime

**Status:** implementation proposal  
**Baseline:** the `main` branch of `bloomberg/crane` as inspected on **2026-11-19**, pinned for implementation at `b54509ddc`  
**Audience:** an engineer or coding agent implementing the redesign in Crane  
**Scope:** Rocq-side mapping declarations, type-class discovery, parameter and call planning, C++ type construction, effects, views, lifetime management, migration, and tests

> This is the design as specified by the project owner. The implementation plan,
> grounded in the code at the pinned commit, is `docs/typed-mappings-plan.md`.
> Where the plan and this document disagree on mechanics, the plan records why;
> the semantic distinctions and validation rules here are normative.
>
> The Rocq and OCaml fragments specify the intended public shape and invariants. Universe annotations, implicit arguments, module paths, and some dependent indices may need adjustment. The semantic distinctions and validation rules are normative.

## Contents

1. Executive summary
2. Current `main`-branch failure
3. Goals and non-goals
4. Public design principles
5. Structured C++ types
6. Copy, access, value, and lifetime models
7. Read and writable views
8. Components and constructor mappings
9. The flattened `TypeMapping` class
10. Import-based mapping selection
11. Operation mappings
12. Interprocedural parameter planning
13. Complete `STArray` design
14. Strings, `std::string_view`, vectors, and `std::span`
15. `bool`, `option`, product, and recursive container mappings
16. Exact mappings for `nat`, `positive`, `N`, and `Z`
17. Numeral mappings
18. Templates and staging
19. Validation rules
20. Compiled interfaces and separate compilation
21. Integration with current Crane
22. Migration from current commands
23. Implementation sequence
24. Regression tests
25. Acceptance criteria
26. Final model

---

## 1. Executive summary

Crane's current custom-mapping mechanism associates Rocq declarations with C++ text templates and stores important semantic facts in separate tables. That is sufficient for simple scalar replacements, but it cannot reliably answer questions such as:

- Is the canonical C++ value cheap to copy?
- Should read-only access use a value, `const T&`, `std::string_view`, or `std::span<const T>`?
- Should writable access use `T&`, a handle passed by value, a handle passed by `const&`, or `std::span<T>`?
- Does an operation mutate the canonical representation, mutate an object reached through a handle, or replace the handle itself?
- May an operation retain an argument?
- Does copying preserve one identity, duplicate a structural value, or merely copy bits?
- Which views are invalidated by a write?
- Who owns and releases an object allocated by a mapped operation?

The redesign should replace the scattered tables with **typed Rocq type-class instances**. The plugin reads those instances during extraction and compiles them into its internal plans. No mapping dictionary is emitted to C++.

The central model is:

1. Every mapped Rocq type has one **canonical C++ value representation**.
2. A type may expose no view, one read-only view, or a matched pair of read-only and writable views.
3. Typical views are:
   - `std::string_view` for `std::string`;
   - `std::span<const T>` for read-only access to contiguous storage;
   - `std::span<T>` for call-bounded writable access to contiguous storage.
4. The mapping declares how canonical values are copied, read, written, retained, and released.
5. Mapped operations declare how each argument is used:
   - `Ignore`;
   - `Read`;
   - `ReadCanonical`;
   - `Write`;
   - `WriteCanonical`;
   - `Take`;
   - `Replace`;
   - or `OpaqueUse`.
6. Crane propagates those requirements through generated functions, alongside its existing ownership analysis.
7. C++ parameter syntax is selected from structured mapping metadata. It is not guessed from an opaque C++ type string.
8. Mappings are selected by the Rocq files the user imports. There is no extra mapping-family parameter in the class types.
9. Mapping declarations use the inductive constructors and record fields directly. The public design does not hide the model behind helper functions that behave like smart constructors.

For `STArray`, the recommended first representation is:

```cpp
std::shared_ptr<std::vector<T>>
```

with these access paths:

```text
read-only element access       std::span<const T>
writable element access        std::span<T>
canonical read/write access    const std::shared_ptr<std::vector<T>>&
retained identity              std::shared_ptr<std::vector<T>>
replace the handle             std::shared_ptr<std::vector<T>>&
```

Once the instantiated storage provides ordinary addressable contiguous elements, a generated helper that only reads and writes array elements can take `std::span<T>`. Otherwise the same design falls back to the canonical mutable-handle ABI. A helper that must retain the array takes the shared pointer by value. A helper that resizes the vector or otherwise requires the concrete owner takes the shared pointer by `const&`. A helper that replaces the handle takes a non-const reference to the shared pointer.

For a raw pointer representation such as `std::vector<T>*`, passing the pointer by value is normally preferable for both reading and mutating the pointee. Copying one pointer is cheap. `std::vector<T>*&` is required only when the callee may reseat the caller's pointer. It is not a faster form of element mutation.

---

## 2. Current `main`-branch failure

### 2.1 Current ST array mapping

The current `theories/Monads/STMonad.v` defines `NewArray`, `ReadArray`, `WriteArray`, and `GetElems`, and maps them to C++:

```coq
Crane Extract Inductive STArray => "std::vector<%t2> *" [ "" ] From "vector".
Crane Extract Inlined Constant newArray =>
  "%result = new std::remove_pointer_t<decltype(%result)>(%a2 - %a1 + 1, %a3)"
  From "type_traits".
Crane Extract Inlined Constant readArray => "(*%a1)[%a2]".
Crane Extract Inlined Constant writeArray => "(*%a1)[%a2] = %a3".
Crane Extract Inlined Constant newListArray =>
  "%result = new std::remove_pointer_t<decltype(%result)>(...)".
```

This creates two independent problems.

#### Problem A: the generated parameter loses logical mutability

A generated helper receiving an `STArray` can be classified as borrowing that parameter. The custom mapped type is an opaque foreign type template, so the generic borrowed-parameter logic adds `const` and `&`. For the spelling `std::vector<T>*`, Crane can emit the equivalent of:

```cpp
const std::vector<T>*&
```

That is a reference to a pointer to a const vector. It prevents `WriteArray` from assigning to an element.

The current printer (`src/emit/print.ml`) prints references, pointers, and const qualification independently:

```ocaml
| Reference (Lvalue, t) -> pp_rec false t ++ str "&"
| Pointer t -> pp_rec false t ++ str "*"
| Const t -> str "const " ++ pp_rec false t
```

For pointer types, prefixing `const` changes the pointee rather than the pointer:

```cpp
const T*      // pointer to const T
T* const      // const pointer to mutable T
T* const&     // reference to a const pointer to mutable T
const T*&     // reference to a pointer to const T
```

These types are not interchangeable.

#### Problem B: the allocation has no owner

`newArray` and `newListArray` allocate with raw `new`. The mapping supplies no owner or corresponding deletion path. Every successfully allocated array therefore leaks.

Adding a `delete` template by itself is not enough. `STArray` is an identity handle and handles may be copied. Deleting every raw-pointer copy would double-free; deleting none leaks. The representation must declare an ownership model such as shared RAII, a region owner, or a complete manual retain/release protocol.

### 2.2 Why `Crane TriviallyCopyable STArray` does not solve it

The current mapping stores the C++ type as a template string. `src/base/table.ml` explains that such a string does not state how copying behaves, so `Crane TriviallyCopyable` is maintained separately.

The current conditional behavior is suitable for bounded componentwise aggregates:

```text
std::optional<A>
std::pair<A, B>
```

Their copy cost depends on their components. It is not suitable for a handle:

```text
std::vector<A>*
std::shared_ptr<std::vector<A>>
```

The cost and semantics of copying the handle do not structurally depend on copying `A`.

### 2.3 Existing ownership analysis is necessary but insufficient

Crane already computes an interprocedural fixed point classifying generated-function parameters as borrowed or owned (`src/core_plan/ownership.mli`). Custom constants are excluded from body inspection because their behavior comes from their mapping rather than a generated body (`src/core_plan/ownership.ml`).

The missing information is orthogonal to ownership:

```text
ownership
    may this call retain, store, capture, or return the argument?

access
    does it ignore, read, write, or replace the logical object?

representation requirement
    may it use a view, or does it require the canonical object?
```

The redesign retains the ownership fixed point and adds access and representation requirements.

---

## 3. Goals and non-goals

### 3.1 Goals

The redesign must:

1. Use ordinary Rocq type classes as the public registry.
2. Let imported mapping files determine the active mappings.
3. Reject ambiguous applicable mappings rather than silently choosing by import order.
4. Use one canonical C++ value representation for each mapped Rocq type.
5. Support an optional read view and optional writable view.
6. Treat `std::string_view`, `std::span<const T>`, and `std::span<T>` as first-class examples of views.
7. Distinguish mutation through a value, mutation through a handle, and replacement of a handle.
8. Keep copy behavior, value semantics, access, and lifetime as separate facts.
9. Preserve constructor identity and source field identity.
10. Express mapped-operation argument use, result provenance, retention, writes, invalidation, and identity allocation.
11. Propagate operation requirements through ordinary generated helper functions.
12. Produce declarator-correct C++ types.
13. Make resource ownership explicit.
14. Keep expression and statement templates as the emission mechanism.
15. Use inductive constructors and record fields directly in mapping declarations.
16. Preserve compatibility with current commands during migration.

### 3.2 Non-goals

This proposal does not attempt to:

- parse arbitrary C++ expression and statement templates into a full C++ AST;
- prove that trusted C++ templates obey their declared contracts;
- infer retention, mutation, or ownership from C++ syntax;
- support an unbounded list of competing view representations for one source type;
- make all dependent Rocq types representable by arbitrary C++ layouts;
- make shared mutable data automatically thread-safe;
- replace Crane's existing ownership, escape, loopification, or release analyses.

---

## 4. Public design principles

### 4.1 One canonical value

A mapping names one C++ value type used for stored fields, owning locals, constructor payloads, captures that outlive a call, owned parameters, ordinary public results, and retained identities.

For Rocq strings, that canonical type is `std::string`. For `STArray`, it is the chosen identity handle, preferably `std::shared_ptr<std::vector<T>>`.

### 4.2 Views are capabilities, not alternative owners

A view is a non-owning, call-bounded capability derived from a live canonical value or handle. It may expose less power than the canonical representation.

```text
std::string                 -> std::string_view
std::vector<T>              -> std::span<const T>
std::vector<T>              -> std::span<T>
shared_ptr<vector<T>>       -> std::span<const T>
shared_ptr<vector<T>>       -> std::span<T>
```

A view does not by itself keep its owner alive.

### 4.3 Read and write views are paired deliberately

The public type declares one of exactly three states: no views; one read-only view; one read-only view plus one writable view. There is no list of view alternatives and no preference list. The compiler has one deterministic preferred representation for read access and, when available, one deterministic preferred representation for write access.

### 4.4 Direct constructors, not an authoring facade

The mapping library defines inductive types and records. Mapping instances use those constructors and fields directly. The design intentionally avoids author-facing helpers such as `Type.by_ref`, `Type.with_view`, `Op.read`, `Op.pure`, `Case.borrow`. Direct declarations are more verbose, but they are locally understandable and searchable. The mapping itself is the documentation.

### 4.5 Import-based selection

The class types have no mapping-family parameter. A user selects a coherent mapping set by importing the desired files, as Crane already does with `Crane.Mapping.Std`:

```coq
From Crane Require Import Mapping.Std.
```

or an alternative library file:

```coq
From MyProject Require Import Mapping.Bsl.
```

Only one applicable instance for a particular source type or source operation may be active. Importing incompatible mapping modules produces an ambiguity diagnostic.

### 4.6 The plugin elaborates, but does not reinterpret

The plugin resolves the class instance, normalizes its data while preserving declaration references, validates it, and compiles it into a richer internal plan. It must not infer semantic facts from template text.

---

## 5. Structured C++ types

### 5.1 Why type strings are insufficient

Expression and statement bodies may remain strings with validated holes. C++ types need enough structure for Crane to apply pointers, const qualification, and references correctly. The current CppIR already represents forms such as `Const`, `Reference`, `Pointer`, and external template applications. The mapping API should construct equivalent structured forms rather than flattening the entire type to text.

```coq
Module Crane.
Module Cpp.

Inductive TypeExpr : Type :=
| Name (qualified_name : string)
| Apply (qualified_name : string) (arguments : list TypeArgument)
| SourceType (T : Type)
| StoredComponent (name : string)
| Pointer (pointee : TypeExpr)
| Const (inner : TypeExpr)
| UnsafeVerbatim (cpp : string)

with TypeArgument : Type :=
| TypeArg (type_argument : TypeExpr)
| ValueArg (value_argument : string).

End Cpp.
End Crane.
```

Examples:

```coq
Crane.Cpp.Name "bool"

Crane.Cpp.Apply "std::optional"
  [Crane.Cpp.TypeArg (Crane.Cpp.StoredComponent "element")]

Crane.Cpp.Pointer
  (Crane.Cpp.Apply "std::vector"
    [Crane.Cpp.TypeArg (Crane.Cpp.StoredComponent "contents")])

Crane.Cpp.Apply "std::shared_ptr"
  [Crane.Cpp.TypeArg
    (Crane.Cpp.Apply "std::vector"
      [Crane.Cpp.TypeArg (Crane.Cpp.StoredComponent "contents")])]

Crane.Cpp.Apply "std::span"
  [Crane.Cpp.TypeArg (Crane.Cpp.Const (Crane.Cpp.StoredComponent "contents"))]
```

`SourceType T` refers to an ordinary Rocq type expression in the mapping instance's telescope. `StoredComponent name` asks Crane for the selected physical storage type of a named logical component.

### 5.2 Declaration references

Mapping metadata refers to Rocq declarations by identity rather than by strings:

```coq
Inductive Declaration : Type :=
| Ref : forall {T : Type}, T -> Declaration.
```

`Ref (@Some)` packages a declaration together with its Rocq type. The plugin must preserve it as a reference boundary while normalizing mapping data. It must not unfold the declaration and lose its identity.

### 5.3 Construction templates

```coq
Inductive Construction : Type :=
| Expr (cpp : string)
| WithBody (initialiser body : string).
```

`Expr e` emits an expression that creates the result. `WithBody init body` initializes an owning `%result` slot from `init`, then executes `body`.

### 5.4 Canonical types are value types

A canonical representation must not contain a top-level C++ reference. Crane adds references according to parameter planning. `Crane.Cpp.Pointer (Crane.Cpp.Name "Node")` is valid; `Crane.Cpp.UnsafeVerbatim "Node*&"` should be rejected as a canonical type. `UnsafeVerbatim` exists only as a migration escape hatch. A mapping that uses it loses automatic declarator manipulation and must supply exact physical argument types through an advanced access specification.

### 5.5 Declarator-correct printing

The printer must preserve the difference between top-level and pointee constness:

```text
Const(Pointer(T))                     T* const
Pointer(Const(T))                     const T*
LvalueReference(Const(Pointer(T)))    T* const&
LvalueReference(Pointer(Const(T)))    const T*&
```

The robust implementation is to print a type around a declarator hole instead of recursively prefixing and suffixing text.

---

## 6. Copy, access, value, and lifetime models

These dimensions answer different questions and must not be collapsed.

### 6.1 Copy model

```coq
Inductive CopyModel : Type :=
| BitCopy
| RetainIdentity
| DuplicateValue
| CopyComponents (components : list string)
| UnknownCopy.
```

| Constructor | Meaning |
| --- | --- |
| `BitCopy` | Copying the canonical value is a cheap scalar or raw-handle copy. |
| `RetainIdentity` | Copying the canonical value retains the same identity, as with `shared_ptr`. |
| `DuplicateValue` | Copying creates an independent structural value and may be nontrivial. |
| `CopyComponents names` | Bounded aggregate copy behavior derives from the named components. |
| `UnknownCopy` | Conservative compatibility fallback. |

```text
bool                               BitCopy
std::string                        DuplicateValue
std::optional<A>                   CopyComponents ["element"]
std::pair<A,B>                     CopyComponents ["first"; "second"]
std::shared_ptr<std::vector<A>>    RetainIdentity
std::vector<A>*                    BitCopy
```

`CopyComponents` is appropriate only for bounded aggregates. It is not appropriate for `std::vector<A>`, whose copy duplicates an unbounded number of elements.

### 6.2 Canonical read style

```coq
Inductive ReadStyle : Type :=
| ReadByValue
| ReadByConstReference
| ReadByComponents (components : list string).
```

`ReadByComponents names` means: pass the aggregate by value if every named component is read by value; otherwise pass the aggregate by const reference.

### 6.3 Handle pass style

```coq
Inductive HandlePass : Type :=
| HandleByValue
| HandleByConstReference.
```

```text
raw pointer handle       HandleByValue
shared_ptr handle        HandleByConstReference
small integer handle     HandleByValue
```

### 6.4 Explicit physical parameter forms

```coq
Inductive PhysicalParameter : Type :=
| CanonicalByValue
| CanonicalByConstReference
| CanonicalByMutableReference
| ExactParameter (cpp : string).

Record ExplicitAccessSpec : Type := {
  explicit_read : PhysicalParameter;
  explicit_write : option PhysicalParameter;
  explicit_replace : option PhysicalParameter
}.
```

`ExactParameter` is a compatibility escape hatch for an unusual ABI. It receives the same prominent diagnostics as `UnsafeVerbatim`.

### 6.5 Canonical access model

```coq
Inductive AccessModel : Type :=
| ReadOnlyValue (read_style : ReadStyle)
| MutableValue (read_style : ReadStyle)
| ReadOnlyHandle (handle_pass : HandlePass)
| MutableHandle (handle_pass : HandlePass)
| ExplicitAccess (specification : ExplicitAccessSpec).
```

- `ReadOnlyValue read_style`: the canonical representation is a structural value. Mapped operations may read or take it, but may not logically mutate or replace it. Examples: `bool`, `std::string` used as an immutable Rocq string, `std::optional<A>`, `cpp_int` used for Rocq numbers.
- `MutableValue read_style`: the canonical representation itself may be mutated. Canonical write access is `T&`; replacement is also `T&`, but the semantic contracts differ. Example: a source-level mutable buffer represented directly by `std::vector<T>`.
- `ReadOnlyHandle handle_pass`: the canonical representation is a handle. It may be inspected or retained, but the logical referent is not mutable through mapped operations.
- `MutableHandle handle_pass`: the canonical representation is a handle to mutable identity. Canonical read and write-through access use the handle pass style. Replacing or reseating the handle uses `T&`. Examples: `std::vector<T>*` (`HandleByValue`), `std::shared_ptr<std::vector<T>>` (`HandleByConstReference`), `std::shared_ptr<Cell<T>>` (`HandleByConstReference`). For `const std::shared_ptr<std::vector<T>>&`, top-level const prevents reseating the shared pointer but does not make the vector const.
- `ExplicitAccess`: an advanced compatibility escape hatch for unusual ABIs. It supplies exact physical parameter forms for canonical read, canonical write, and replacement. New standard mappings should use one of the first four constructors.

### 6.6 Physical canonical parameter forms

Ignoring preferred views for the moment:

| Access model | Canonical read | Canonical write-through | Replace representation | Take/retain |
| --- | --- | --- | --- | --- |
| `ReadOnlyValue ReadByValue` | `T` | invalid | invalid | `T` |
| `ReadOnlyValue ReadByConstReference` | `const T&` | invalid | invalid | `T` |
| `MutableValue read` | derived from `read` | `T&` | `T&` | `T` |
| `ReadOnlyHandle HandleByValue` | `T` | invalid | invalid | `T` |
| `ReadOnlyHandle HandleByConstReference` | `const T&` | invalid | invalid | `T` |
| `MutableHandle HandleByValue` | `T` | `T` | `T&` | `T` |
| `MutableHandle HandleByConstReference` | `const T&` | `const T&` | `T&` | `T` |

The distinction between write-through and replacement is essential:

```cpp
void mutate(std::vector<int>* p);      // writes through p
void replace(std::vector<int>*& p);    // may assign a different pointer to p
```

The second form is not a performance improvement over the first. It is a stronger capability.

### 6.7 Value model

```coq
Inductive ValueModel : Type :=
| Structural
| Identity
| Unspecified.
```

`Structural` means copies represent the same source value without hidden identity. `Identity` means copies alias one logical mutable or externally observable identity. `Unspecified` requires conservative dependency and alias reasoning. `CopyModel` and `ValueModel` are independent: a small integer handle can be `BitCopy` plus `Identity`.

### 6.8 Lifetime model

```coq
Inductive LifetimeModel : Type :=
| NativeRAII
| RegionOwned (region : Declaration)
| ExternallyOwned
| ManualShared (retain : Declaration) (release : Declaration).
```

- `NativeRAII`: the canonical C++ value owns or safely retains its resource.
- `RegionOwned`: an explicit owner releases all identities in the region.
- `ExternallyOwned`: Crane never owns the referent; allocation cannot claim fresh ownership.
- `ManualShared`: trusted retain/release operations manage copied handles.

Validation must reject a raw pointer with `NativeRAII`.

### 6.9 Nested release plan

```coq
Inductive ReleasePlan : Type :=
| OrdinaryRelease
| DrainWith (cpp : string).
```

Top-level resource ownership and nested stack-safe release are different. `DrainWith` does not turn a raw pointer into an owner.

---

## 7. Read and writable views

### 7.1 View modes

```coq
Inductive ViewMode : Type :=
| ReadOnlyView
| WritableView.
```

A view is always non-owning and cheap to pass by value. The view type itself must not be a top-level C++ reference.

### 7.2 Escape policy

```coq
Inductive ViewEscape (T : Type) : Type :=
| MaterialiseView (construction : Construction)
| BorrowOnly.
```

`MaterialiseView` means the current logical value can be copied into an independent canonical representation (e.g. `std::string_view -> std::string`, `std::span<const T> -> std::vector<T>`). `BorrowOnly` means materialization would not reproduce the same logical identity (e.g. `std::span<T>` derived from an `STArray` identity: copying the span's elements into a new vector would create a different array identity).

### 7.3 View specification

```coq
Record ViewSpec (T : Type) (mode : ViewMode) : Type := {
  view_headers : list string;
  view_cpp : Crane.Cpp.TypeExpr;

  (* %value is a live canonical lvalue or handle. *)
  view_from_canonical : string;

  view_escape : ViewEscape T
}.
```

### 7.4 Exactly zero, one, or two views

```coq
Inductive Views (T : Type) : Type :=
| NoViews
| ReadViews
    (read_view : ViewSpec T ReadOnlyView)
| ReadWriteViews
    (read_view : ViewSpec T ReadOnlyView)
    (write_view : ViewSpec T WritableView)
    (read_from_write : string).
```

This shape makes several invalid states unrepresentable: there cannot be two competing read views; there cannot be a preference list whose order changes the ABI; there cannot be a writable view without a corresponding read view; every writable view declares how it is narrowed to the read view; a view must declare whether it is materializable or borrow-only.

### 7.5 Selection rules

```text
Read            use the read view if one exists; otherwise canonical read access.
ReadCanonical   ignore views and use canonical read access.
Write           use the writable view if one exists; otherwise canonical write-through access.
WriteCanonical  ignore views and use canonical write-through access.
Take            use the canonical value by value.
Replace         use a mutable reference to the canonical representation.
```

A writable-view parameter also satisfies read-only uses through the declared `read_from_write` conversion.

### 7.6 `std::string_view` and `std::span`

`std::string_view` is a non-owning read-only view of a contiguous character sequence; `std::span<const T>` a non-owning read-only view of a contiguous sequence of `T`; `std::span<T>` a non-owning writable view. `std::string_view` provides string-oriented operations; `std::span` works for arbitrary element types, can express writable access, and represents subranges through `subspan`; neither owns or extends the lifetime of the underlying storage. Generated code is compiled as C++26 (`-std=c++2c`), so `std::span` is available. An alternative mapping file may use `bsl::span`, `gsl::span`, or another view type by changing only the mapping instance.

### 7.7 Full ranges and subranges

A view created from a canonical container may cover the entire container (`std::span<const T>{vector}`, `std::span<T>{vector}`) or a subrange (`std::span<T>{vector}.subspan(offset, count)`). The mapping contract must preserve the owner provenance of the resulting view. A subspan cannot outlive the vector storage. An operation that resizes or reallocates the vector must declare that it invalidates outstanding views.

### 7.8 View invalidation

```text
array[i] = value
    may invalidate borrows into the old element;
    does not normally invalidate a span over the array.

vector.resize(...), reserve(...), push_back(...)
    may reallocate;
    invalidates spans and references into the old storage.
```

The operation fact vocabulary therefore distinguishes element-borrow invalidation from whole-view invalidation.

---

## 8. Components and constructor mappings

### 8.1 Declaration references

`Declaration` and its `Ref` constructor were defined in Section 5. Mapping instances use `Ref` directly for constructors, operations, region owners, and manual lifetime operations.

### 8.2 Components

```coq
Inductive ComponentType : Type :=
| KnownType (T : Type)
| FieldType (constructor : Declaration) (field : nat).

Record Component : Type := {
  component_name : string;
  component_type : ComponentType
}.
```

Examples: `std::optional<A>` has `element : A`; `std::pair<A,B>` has `first : A`, `second : B`; `STArray S A` and `STRef S A` have `contents : A`. A component need not correspond to exactly one C++ field: `contents : A` for an array denotes arbitrarily many stored `A` values. Components serve as stored-type inputs, copy-cost dependencies, dependency destinations, effect targets, view invalidation domains, and typed release ports. Component names must be unique within one mapping.

### 8.3 Construction templates

`Construction`, `Expr`, and `WithBody` were defined in Section 5.

### 8.4 Projections

```coq
Inductive Projection : Type :=
| OwnedProjection (cpp : string)
| CanonicalBorrowProjection (cpp : string)
| ReadViewProjection (cpp : string).
```

`OwnedProjection` produces an independent canonical field value. `CanonicalBorrowProjection` aliases the field's canonical representation. `ReadViewProjection` produces the field type's declared read view. Borrowed and viewed projections create lifetime edges to the scrutinee. If they escape the scrutinee, Crane must retain a suitable owner or materialize when the view policy permits it.

### 8.5 Constructor views

```coq
Inductive ObservationRequirement : Type :=
| PreferredObservation
| CanonicalObservation.

Record ConstructorView : Type := {
  view_requirement : ObservationRequirement;
  case_test : string;
  case_fields : list (nat * Projection)
}.

Record ConstructorMapping : Type := {
  ctor_source : Declaration;
  ctor_build : Construction;
  ctor_view : option ConstructorView
}.
```

`PreferredObservation` permits the mapped type's read view. `CanonicalObservation` requires the canonical representation. Field numbers are source constructor field positions after family parameters. The plugin records their canonical binder identities before erasure.

### 8.6 Abstract and algebraic interfaces

```coq
Inductive TypeInterface : Type :=
| AbstractInterface
| AlgebraicInterface (constructors : list ConstructorMapping).
```

An abstract type is used only through mapped operations. Direct source construction or pattern matching is a diagnostic. `AlgebraicInterface []` represents a genuinely empty source type and is distinct from `AbstractInterface`.

### 8.7 Numeral descriptors

```coq
Inductive NumeralAction : Type :=
| NumeralZero
| NumeralOne
| NumeralSuccessor (field : nat)
| NumeralDouble (field : nat)
| NumeralDoublePlusOne (field : nat)
| NumeralIdentity (field : nat)
| NumeralNegate (field : nat).

Record NumeralCase : Type := {
  numeral_constructor : Declaration;
  numeral_action : NumeralAction
}.

Inductive NumeralEmitter : Type :=
| IntegerToken (prefix suffix : string)
| DecimalConstructor (callee : string).

Record NumeralSpec (T : Type) : Type := {
  numeral_cases : list NumeralCase;
  numeral_emitter : NumeralEmitter;
  numeral_converters : list Declaration
}.
```

---

## 9. The flattened `TypeMapping` class

```coq
Class TypeMapping (T : Type) : Type := {
  type_headers : list string;
  type_cpp : Crane.Cpp.TypeExpr;

  type_components : list Component;
  type_copy : CopyModel;
  type_access : AccessModel;
  type_views : Views T;

  type_interface : TypeInterface;
  type_model : ValueModel;
  type_lifetime : LifetimeModel;
  type_release : ReleasePlan;

  type_numerals : option (NumeralSpec T)
}.
```

Every instance fills these fields directly. There is no author-facing layer of functions that hides which constructors were chosen. A simple instance:

```coq
#[global] Instance example_mapping : TypeMapping Example :=
  {| type_headers := ["example.hpp"];
     type_cpp := Crane.Cpp.Name "example::value";
     type_components := [];
     type_copy := DuplicateValue;
     type_access := ReadOnlyValue ReadByConstReference;
     type_views := NoViews Example;
     type_interface := AbstractInterface;
     type_model := Structural;
     type_lifetime := NativeRAII;
     type_release := OrdinaryRelease;
     type_numerals := None |}.
```

---

## 10. Import-based mapping selection

### 10.1 The imported files are the configuration

A mapping file exports instances (`#[export] Instance std_string_mapping : TypeMapping PrimString.string := ...`). A user selects the mapping set by importing the desired file. No extra class index or extraction command is required.

### 10.2 Unique-instance rule

For each concrete source type `T`, the plugin must find: zero applicable `TypeMapping T` instances (use Crane's normal generated representation); exactly one (normalize, validate, compile, and freeze it); more than one (report an ambiguity and list the candidates). The plugin must not let instance priority or import order silently change a C++ ABI. The same rule applies to operation mappings.

### 10.3 Parametric instances

Ordinary Rocq instance parameters describe families: `#[export] Instance std_option_mapping (A : Type) : TypeMapping (option A) := ...`. When Crane encounters `option nat`, type-class resolution instantiates the mapping with `A := nat`.

### 10.4 Separate compilation

The resolved mapping instance identity and physical ABI are recorded in Crane's compiled interface. A consumer that resolves the same source type or operation differently must receive a mapping mismatch diagnostic.

---

## 11. Operation mappings

### 11.1 Input uses

```coq
Inductive InputUse : Type :=
| Ignore
| Read
| ReadCanonical
| Write
| WriteCanonical
| Take
| Replace
| OpaqueUse.
```

- `Ignore`: the mapping does not observe, mutate, or retain the runtime argument. Its template may not reference the argument.
- `Read`: call-bounded logical read. Use the read view when one exists; otherwise use canonical read access (Rocq string: `std::string_view`; structural vector: `std::span<const T>`; `STArray`: `std::span<const T>`; `bool`: `bool`).
- `ReadCanonical`: call-bounded logical read that requires the concrete canonical representation (a string API that requires `c_str()`; an allocator-aware API that requires `std::vector<T>`; an ST operation that needs the shared owner rather than only the elements).
- `Write`: call-bounded mutation of the represented logical object. It does not replace the canonical value or handle and does not retain it. Use the writable view when one exists; otherwise use canonical write-through access (STArray element assignment: `std::span<T>`; raw pointer handle without a write view: `T*` by value; shared_ptr handle without a write view: `const shared_ptr<T>&`; mutable value without a write view: `T&`).
- `WriteCanonical`: call-bounded mutation that specifically requires the canonical representation (`vector.resize`, `vector.reserve`, operations that inspect or change allocator state, operations that need identity-handle services).
- `Take`: the mapping receives an owning canonical slot by value. Crane moves at the source's final use and copies or retains when the source remains live.
- `Replace`: the operation may replace or reseat the caller's canonical representation. The physical ABI is `T&`.
- `OpaqueUse`: unknown access and retention. Conservative compatibility behavior.

### 11.2 Named runtime arguments

```coq
Record ArgumentSpec : Type := {
  argument_name : string;
  argument_use : InputUse
}.
```

The list is written in canonical retained-runtime-binder order after Crane's existing implicit-argument and proof erasure rules. Names must be unique. Templates use `%arg(name)`. Legacy `%aN` holes may remain supported while old commands are migrated, but the compiled plan should resolve all holes to canonical binder identities immediately.

### 11.3 Borrow origins

```coq
Record ComponentPath : Type := {
  path_argument : string;
  path_components : list string
}.
```

### 11.4 Fresh-identity initialisers

```coq
Inductive InitialMultiplicity : Type :=
| InitialiseOnce
| InitialiseMany.

Record ComponentInitialiser : Type := {
  initial_component : string;
  initial_source_argument : option string;
  initial_multiplicity : InitialMultiplicity
}.
```

### 11.5 Result specifications

```coq
Inductive BorrowForm : Type :=
| CanonicalBorrow
| ReadViewBorrow
| WritableViewBorrow.

Inductive ResultSpec : Type :=
| ReturnValue
| ReturnBorrowed
    (form : BorrowForm)
    (origin : ComponentPath)
| ReturnSameIdentity
    (argument : string)
| ReturnFreshIdentity
    (initialisers : list ComponentInitialiser)
| ReturnOpaque.
```

A `ReadViewBorrow` or `WritableViewBorrow` is valid only if the result type declares the corresponding view.

### 11.6 Operation facts

```coq
Inductive OperationFact : Type :=
| ReadsComponent (target : ComponentPath)
| WritesComponent (target : ComponentPath) (source_argument : option string)
| InvalidatesElementBorrows (target : ComponentPath)
| InvalidatesViews (target : ComponentPath)
| RetainsArgument (argument : string) (destination : ComponentPath)
| ReleasesIdentity (argument : string)
| ExternalEffect (name : string).
```

`array[i] = value` declares `InvalidatesElementBorrows contents`; `vector.resize(...)` declares `InvalidatesViews contents`.

### 11.7 Pure, effectful, and opaque contracts

```coq
Inductive OperationContract : Type :=
| PureOperation
    (arguments : list ArgumentSpec) (result : ResultSpec) (facts : list OperationFact)
| EffectfulOperation
    (arguments : list ArgumentSpec) (result : ResultSpec) (facts : list OperationFact)
| OpaqueOperation.
```

The plugin validates that a `PureOperation` does not contain `Write`, `WriteCanonical`, `Replace`, `ReturnFreshIdentity`, `WritesComponent`, retention outside the result, release, or an external effect. `ReadsComponent` and borrowed-result provenance are allowed in a pure operation.

### 11.8 The flattened `OperationMapping` class

```coq
Class OperationMapping (source : Declaration) : Type := {
  operation_headers : list string;
  operation_cpp : Construction;
  operation_contract : OperationContract
}.
```

```coq
#[global] Instance example_operation_mapping :
  OperationMapping (Ref example_operation) :=
  {| operation_headers := ["example.hpp"];
     operation_cpp := Expr "example::operation(%arg(value))";
     operation_contract :=
       PureOperation
         [{| argument_name := "value"; argument_use := Read |}]
         ReturnValue
         [] |}.
```

### 11.9 Single evaluation

Crane evaluates every retained source argument once, in source order, before expanding the template. Repeated `%arg(name)` holes refer to the prepared slot and never repeat a source computation.

---

## 12. Interprocedural parameter planning

### 12.1 Requirement dimensions

```ocaml
type ownership = Borrowed | Owned

type access =
  | Unused
  | Read_access
  | Write_access
  | Replace_access

type representation_requirement =
  | Preferred_representation
  | Canonical_representation

type parameter_requirement = {
  ownership : ownership;
  access : access;
  representation : representation_requirement;
}
```

### 12.2 Join order

```text
Borrowed < Owned
Unused < Read_access < Write_access < Replace_access
Preferred_representation < Canonical_representation
```

### 12.3 Requirements from mapped calls

```text
Ignore          Unused, Borrowed, Preferred
Read            Read_access, Borrowed, Preferred
ReadCanonical   Read_access, Borrowed, Canonical
Write           Write_access, Borrowed, Preferred
WriteCanonical  Write_access, Borrowed, Canonical
Take            Read_access or Write_access as declared by facts, Owned, Canonical
Replace         Replace_access, Borrowed, Canonical
OpaqueUse       Owned, Replace_access, Canonical
```

### 12.4 Fixed point

Start each parameter at the least requirement; inspect local uses and calls; read callee summaries for direct calls; join the caller's corresponding parameter requirements; repeat until no summary changes. Access only moves upward in a finite lattice, so the analysis terminates.

### 12.5 Selecting the physical parameter type

```text
if ownership = Owned:                                    canonical T by value
else if access = Replace_access:                         mutable reference to canonical T
else if access = Write_access, Preferred, has write view: writable view by value
else if access = Write_access:                           canonical write-through ABI from AccessModel
else if access = Read_access, Preferred, has read view:  read view by value
else:                                                    canonical read ABI from AccessModel
```

### 12.6 The `swapArray` result

With `ReadArray` declared `Read` and `WriteArray` declared `Write`, the fixed point gives `swapArray`'s array parameter `Borrowed + Write_access + Preferred_representation`, which becomes `std::span<T>` for the recommended `STArray` mapping. The helper can therefore remain a separate C++ function.

### 12.7 View conversions at calls

| Caller slot | Callee requirement | Action |
| --- | --- | --- |
| canonical owner | read view | apply `view_from_canonical` |
| canonical borrow | read view | apply `view_from_canonical` |
| canonical owner | writable view | apply writable `view_from_canonical` |
| writable view | read view | apply `read_from_write` |
| read view | read view | pass directly |
| writable view | writable view | pass directly |
| read view | canonical owner | materialize if allowed; otherwise reject or force caller canonical |
| writable view | canonical owner | materialize only if allowed and semantically valid |
| view | canonical read | materialize a local if allowed; otherwise force caller canonical |
| canonical owner | canonical read | direct borrow or value copy |
| canonical owner | take | move at last use; copy or retain otherwise |

The planner should prefer upgrading a generated function's parameter to canonical over repeatedly materializing views inside it.

### 12.8 View results

A borrowed view result carries owner provenance. If it remains within the owner's lifetime, Crane may keep it as a view. If it escapes: `MaterialiseView` lets Crane create an independent canonical result; `BorrowOnly` requires retaining an owner in the result representation, keeping the result internal with a proven lifetime, or rejecting the escape. A public function returning ordinary Rocq `string` should normally return `std::string`, not `std::string_view`.

### 12.9 Higher-order functions

First-class callable parameters and results use canonical value ABIs; known direct calls may use views and canonical borrows. Adapters bridge direct functions to first-class callable values. A future callable-capability analysis may admit view ABIs for function values with explicit contracts.

---

## 13. Complete `STArray` design

### 13.1 Fresh-identity metadata

`InitialMultiplicity` and `ComponentInitialiser` were defined in Section 11.

### 13.2 Recommended canonical representation

Use `std::shared_ptr<std::vector<T>>`: copied handles preserve one array identity; the shared pointer owns the vector; `std::make_shared` removes the unconditional raw-pointer leak; read/write helpers can avoid reference-count changes by taking a view or `const shared_ptr&`; retained arrays can be passed by value; replacement remains explicit through `shared_ptr&`. This does not collect strong-reference cycles. A future `runST`-owned region is the stronger lifetime model when cyclic ST identity graphs must be reclaimed deterministically.

### 13.3 Type mapping

```coq
#[export] Instance st_array_mapping
    (T S A : Type) : TypeMapping (STArray T S A) :=
  {| type_headers := ["memory"; "span"; "vector"];
     type_cpp :=
       Crane.Cpp.Apply "std::shared_ptr"
         [Crane.Cpp.TypeArg
           (Crane.Cpp.Apply "std::vector"
             [Crane.Cpp.TypeArg (Crane.Cpp.StoredComponent "contents")])];
     type_components :=
       [{| component_name := "contents"; component_type := KnownType A |}];
     type_copy := RetainIdentity;
     type_access := MutableHandle HandleByConstReference;
     type_views :=
       ReadWriteViews
         {| view_headers := ["span"];
            view_cpp :=
              Crane.Cpp.Apply "std::span"
                [Crane.Cpp.TypeArg (Crane.Cpp.Const (Crane.Cpp.StoredComponent "contents"))];
            view_from_canonical := "std::span<const %stored(contents)>{*%value}";
            view_escape := BorrowOnly |}
         {| view_headers := ["span"];
            view_cpp :=
              Crane.Cpp.Apply "std::span"
                [Crane.Cpp.TypeArg (Crane.Cpp.StoredComponent "contents")];
            view_from_canonical := "std::span<%stored(contents)>{*%value}";
            view_escape := BorrowOnly |}
         "std::span<const %stored(contents)>{%view}";
     type_interface := AbstractInterface;
     type_model := Identity;
     type_lifetime := NativeRAII;
     type_release := OrdinaryRelease;
     type_numerals := None |}.
```

The read and writable spans are borrow-only because a copied vector would not be the same `STArray` identity.

### 13.4 `newArray`

```coq
#[export] Instance new_array_mapping (* source parameters and type-class assumptions *) :
  OperationMapping (Ref (@newArray (* source parameters *))) :=
  {| operation_headers := ["memory"; "vector"];
     operation_cpp :=
       Expr
         "std::make_shared<std::vector<%stored(contents)>>(\
            static_cast<std::size_t>(%arg(hi) - %arg(lo) + 1),\
            %arg(default_value))";
     operation_contract :=
       EffectfulOperation
         [{| argument_name := "idx"; argument_use := Ignore |};
          {| argument_name := "lo"; argument_use := Read |};
          {| argument_name := "hi"; argument_use := Read |};
          {| argument_name := "default_value"; argument_use := Take |}]
         (ReturnFreshIdentity
           [{| initial_component := "contents";
               initial_source_argument := Some "default_value";
               initial_multiplicity := InitialiseMany |}])
         [] |}.
```

`Take` does not mean the vector fill constructor moves the value into every element. It means Crane prepares an owning slot. The C++ implementation may copy from that slot as many times as required.

### 13.5 `readArray`

```coq
  {| operation_headers := ["span"];
     operation_cpp := Expr "%arg(array)[%arg(index)]";
     operation_contract :=
       PureOperation
         [{| argument_name := "idx"; argument_use := Ignore |};
          {| argument_name := "array"; argument_use := Read |};
          {| argument_name := "index"; argument_use := Read |}]
         ReturnValue
         [ReadsComponent {| path_argument := "array"; path_components := ["contents"] |}] |}.
```

`Read` selects `std::span<const T>`.

### 13.6 `writeArray`

```coq
  {| operation_headers := ["span"; "utility"];
     operation_cpp := Expr "%arg(array)[%arg(index)] = std::move(%arg(value))";
     operation_contract :=
       EffectfulOperation
         [{| argument_name := "idx"; argument_use := Ignore |};
          {| argument_name := "array"; argument_use := Write |};
          {| argument_name := "index"; argument_use := Read |};
          {| argument_name := "value"; argument_use := Take |}]
         ReturnValue
         [WritesComponent {| path_argument := "array"; path_components := ["contents"] |} (Some "value");
          InvalidatesElementBorrows {| path_argument := "array"; path_components := ["contents"] |}] |}.
```

`Write` selects `std::span<T>`. Element assignment does not reallocate the vector, so this mapping does not declare `InvalidatesViews`.

### 13.7 `getElems`

```coq
  {| operation_headers := ["span"];
     operation_cpp :=
       WithBody
         "List<%stored(contents)>::nil()"
         "for (std::size_t i = %arg(array).size(); i > 0; --i) {\
            %result = List<%stored(contents)>::cons(%arg(array)[i - 1], std::move(%result));\
          }";
     operation_contract :=
       PureOperation
         [{| argument_name := "idx"; argument_use := Ignore |};
          {| argument_name := "array"; argument_use := Read |}]
         ReturnValue
         [ReadsComponent {| path_argument := "array"; path_components := ["contents"] |}] |}.
```

### 13.8 Canonical-only mutation

An operation that resizes the underlying vector cannot use `std::span<T>` because resize may reallocate. It must use `WriteCanonical` and declare `InvalidatesViews contents`. For the recommended mapping, the array parameter is `const std::shared_ptr<std::vector<T>>&`: the shared pointer is not reseated, but the vector may be resized.

### 13.9 Subarrays

The current `STEvent` API has no subarray constructor. If a future Rocq API introduces a slice whose semantics are an alias to a contiguous subrange, its mapping can return `ReturnBorrowed WritableViewBorrow {| path_argument := "array"; path_components := ["contents"] |}` with an expression such as `std::span<T>{*array}.subspan(offset, count)`. The result must retain owner provenance; it cannot outlive the array or a reallocation of its vector.

### 13.10 Raw-pointer alternative

```coq
type_cpp := Crane.Cpp.Pointer (Crane.Cpp.Apply "std::vector" [Crane.Cpp.TypeArg (Crane.Cpp.StoredComponent "contents")]);
type_copy := BitCopy;
type_access := MutableHandle HandleByValue;
type_model := Identity;
type_lifetime := RegionOwned (Ref runST_region_owner).
```

Without a span view: `Read`/`Write` pass `std::vector<T>*` by value; `Replace` passes `std::vector<T>*&`. A raw-pointer mapping must not use `NativeRAII`.

### 13.11 Why a reference is not faster for a raw pointer

`void f(T* p)` copies one machine word and can mutate `*p`. `void f(T*& p)` adds a level of indirection and grants the ability to reseat `p`; it is not a performance optimization for pointee mutation. For `std::shared_ptr<T>`, copying by value normally changes the reference count, so `const std::shared_ptr<T>&` is useful for call-bounded access. For `std::span<T>`, passing by value is idiomatic.

### 13.12 Lifetime caveat

`std::shared_ptr` fixes the current unconditional leak for ordinary acyclic handle graphs. It does not collect strong-reference cycles. The proposal should support a later `RegionOwned` implementation in which `runST` owns all ST allocations and releases them together.

### 13.13 `STRef`

```coq
#[export] Instance st_ref_mapping (S A : Type) : TypeMapping (STRef S A) :=
  {| type_headers := ["memory"];
     type_cpp := Crane.Cpp.Apply "std::shared_ptr" [Crane.Cpp.TypeArg (Crane.Cpp.StoredComponent "contents")];
     type_components := [{| component_name := "contents"; component_type := KnownType A |}];
     type_copy := RetainIdentity;
     type_access := MutableHandle HandleByConstReference;
     type_views := NoViews (STRef S A);
     type_interface := AbstractInterface;
     type_model := Identity;
     type_lifetime := NativeRAII;
     type_release := OrdinaryRelease;
     type_numerals := None |}.
```

`newSTRef`: `ReturnFreshIdentity`, initialized once from the value argument. `readSTRef`: `Read`, `ReturnValue`, `ReadsComponent contents`. `writeSTRef`: `Write`, `WritesComponent contents`, `InvalidatesElementBorrows contents`. Because there is no writable view, `Write` uses the canonical mutable-handle ABI `const std::shared_ptr<A>&`.

---

## 14. Strings, `std::string_view`, vectors, and `std::span`

### 14.1 String type mapping

Plain Rocq strings are immutable values; canonical `std::string`, a read view, no writable view:

```coq
#[export] Instance std_string_mapping : TypeMapping PrimString.string :=
  {| type_headers := ["string"; "string_view"];
     type_cpp := Crane.Cpp.Name "std::string";
     type_components := [];
     type_copy := DuplicateValue;
     type_access := ReadOnlyValue ReadByConstReference;
     type_views :=
       ReadViews
         {| view_headers := ["string_view"];
            view_cpp := Crane.Cpp.Name "std::string_view";
            view_from_canonical := "std::string_view{%value.data(), %value.size()}";
            view_escape := MaterialiseView (Expr "std::string{%view.data(), %view.size()}") |};
     type_interface := AbstractInterface;
     type_model := Structural;
     type_lifetime := NativeRAII;
     type_release := OrdinaryRelease;
     type_numerals := None |}.
```

```text
ordinary read                 std::string_view
canonical-only read           const std::string&
owned or escaping value       std::string
logical write                 invalid for plain Rocq string
```

### 14.2-14.5 String operations

- `PrimString.length`: `Expr "static_cast<std::int64_t>(%arg(text).size())"`, `PureOperation [text: Read] ReturnValue []`; physical parameter `std::string_view`.
- `PrimString.cat`: `WithBody "std::string{%arg(left)}" "%result.append(%arg(right));"`, `PureOperation [left: Read; right: Read] ReturnValue []`.
- `PrimString.sub`: returns an owner even if the implementation reads through a view; a distinct borrowed-slice API may use `ReadViewBorrow` with provenance from the input string.
- An operation requiring NUL termination (`c_str()`) requests `ReadCanonical`; the physical parameter is `const std::string&`.

### 14.6 Structural vector with a read span

An immutable source sequence represented by `std::vector<A>` may declare `type_copy := DuplicateValue`, `type_access := ReadOnlyValue ReadByConstReference`, and `ReadViews` with `std::span<const A>` materialisable back into `std::vector<A>{%view.begin(), %view.end()}`.

### 14.7 Mutable buffer with read and write spans

`type_access := MutableValue ReadByConstReference` with `ReadWriteViews` (read `std::span<const A>`, write `std::span<A>`, `read_from_write := "std::span<const %stored(element)>{%view}"`):

```text
Read                 std::span<const A>
Write                std::span<A>
ReadCanonical        const std::vector<A>&
WriteCanonical       std::vector<A>&
Take                 std::vector<A>
Replace              std::vector<A>&
```

### 14.8 Subarray operations

A mapped source operation whose semantics are explicitly borrowed may return `ReturnBorrowed ReadViewBorrow ...` or `ReturnBorrowed WritableViewBorrow ...` with `std::span<T>{buffer}.subspan(offset, count)`. Owner provenance is mandatory. The plugin must not silently reinterpret an independent source array result as an aliasing subarray.

### 14.9 The `std::vector<bool>` exception

`std::vector<bool>` uses a proxy representation rather than ordinary addressable `bool` elements, so it cannot generally provide `std::span<bool>` or `std::span<const bool>`. A generic span-enabled vector or `STArray` mapping must choose one of: (1) a Crane array-storage wrapper that does not specialize `bool`; (2) a distinct addressable stored representation for logical `bool`, with declared load and store conversions; (3) a specialized no-span mapping for the incompatible instantiation; (4) conservatively omit spans from the generic mapping and use canonical handle access. The span-enabled `STArray` instance must not ship as universally valid for every `A` until one of these is implemented. The immediate correctness fix may use `type_views := NoViews`, `type_access := MutableHandle HandleByConstReference`, which gives both `ReadArray` and `WriteArray` a physical `const shared_ptr<vector<A>>&` argument and still permits element mutation. Regression tests must cover both `nat` and `bool` arrays.

---

## 15. `bool`, `option`, product, and recursive container mappings

### 15.1 `bool`

`type_cpp := Name "bool"`, `BitCopy`, `ReadOnlyValue ReadByValue`, `NoViews`, `AlgebraicInterface` with `true` (`Expr "true"`, test `%scrut`) and `false` (`Expr "false"`, test `!%scrut`), both `PreferredObservation`, `Structural`, `NativeRAII`, `OrdinaryRelease`. A read-only `bool` parameter is passed by value.

### 15.2 `option A`

`type_cpp := Apply "std::optional" [TypeArg (StoredComponent "element")]`, component `element : A`, `CopyComponents ["element"]`, `ReadOnlyValue (ReadByComponents ["element"])`, `NoViews`, `AlgebraicInterface`: `Some` built by `std::optional<%stored(element)>{std::move(%arg(0))}`, observed with `CanonicalObservation`, test `%scrut.has_value()`, field 0 `CanonicalBorrowProjection "*%scrut"`; `None` built by `std::optional<%stored(element)>{}`, test `!%scrut.has_value()`. The component policy yields `option<bool>` and `option<int64>` normally by value, `option<string>` normally by const reference. A borrowed `Some` payload of type string may immediately be converted to that payload type's `std::string_view` when subsequent uses require only `Read`.

### 15.3 Product

`std::pair<%stored(first), %stored(second)>`, components `first`, `second`, `CopyComponents ["first"; "second"]`, `ReadOnlyValue (ReadByComponents ["first"; "second"])`, constructor `pair` with `CanonicalBorrowProjection "%scrut.first"` / `"%scrut.second"`.

### 15.4 Recursive list mapped to `std::deque`

`std::deque<%stored(element)>`, `DuplicateValue` (not `CopyComponents`: copying a deque duplicates an unbounded number of elements), `ReadOnlyValue ReadByConstReference`, `nil`/`cons` constructors (`cons` built with `WithBody "std::move(%a1)" "%result.push_front(std::move(%a0));"`; head `CanonicalBorrowProjection "%scrut.front()"`; tail `OwnedProjection` copying the rest), and `type_release := DrainWith "while (!%scrut.empty()) { auto %tmp0 = std::move(%scrut.front()); %scrut.pop_front(); %yield(element, std::move(%tmp0)); }"`. The drain describes destruction, not ordinary traversal; the logical tail projection copies and can make head-tail recursion quadratic; efficient folds need a separate traversal lowering or operation mapping. A heterogeneous aggregate can expose several typed release ports.

---

## 16. Exact mappings for `nat`, `positive`, `N`, and `Z`

Rocq's ordinary `nat`, `positive`, `N`, and `Z` are unbounded. Mapping them silently to fixed-width C++ integers changes their semantics when values overflow. An exact mapping file can use `boost::multiprecision::cpp_int`; an alternative fixed-width mapping file may use `std::uint64_t` / `std::int64_t` under explicit project assumptions. The user selects one set by importing one mapping file. The plugin supplies only validated decimal digits and an optional sign to the selected emitter.

- `nat`: `O` built `cpp_int{0}`, test `%scrut == 0`; `S` built `(%a0 + 1)`, test `%scrut > 0`, field 0 `OwnedProjection "(%scrut - 1)"`; numerals `[O: NumeralZero; S: NumeralSuccessor 0]`, emitter `DecimalConstructor "boost::multiprecision::cpp_int"`.
- `positive`: `xH` = 1, `xO p` = `(%a0 << 1)` with test `(%scrut > 1) && ((%scrut & 1) == 0)` and projection `(%scrut >> 1)`, `xI p` = `((%a0 << 1) + 1)` with test `(%scrut > 1) && ((%scrut & 1) != 0)`; numerals `[xH: NumeralOne; xO: NumeralDouble 0; xI: NumeralDoublePlusOne 0]`.
- `N`: `N0` = 0; `Npos` = `%a0`, test `%scrut > 0`, projection `OwnedProjection "%scrut"`; numerals `[N0: NumeralZero; Npos: NumeralIdentity 0]`. Ownership is a semantic declaration, not a conclusion drawn from expression syntax.
- `Z`: `Z0` = 0; `Zpos` = `%a0` (test `%scrut > 0`); `Zneg` = `(-%a0)` (test `%scrut < 0`, projection `(-%scrut)`); numerals `[Z0: NumeralZero; Zpos: NumeralIdentity 0; Zneg: NumeralNegate 0]`.
- Arithmetic, e.g. `Nat.add`: `Expr "(%arg(left) + %arg(right))"`, `PureOperation [left: Read; right: Read] ReturnValue []`; both physical arguments are `const cpp_int&`.

---

## 17. Numeral mappings

`NumeralAction` describes how an inductive constructor contributes to a numeral without making the plugin know specific names such as `O`, `S`, `xH`, or `Zneg`. The plugin validates that each constructor belongs to the mapped type, referenced fields exist, recursive numeral fields have the expected source type, cases are nonoverlapping, and the emitter accepts only validated decimal values. `IntegerToken "" "ULL"` emits `123ULL`; `DecimalConstructor "boost::multiprecision::cpp_int"` emits an exact large value through a trusted decimal constructor. Numeral metadata belongs inside `TypeMapping`, so one instance cannot choose a C++ representation while another chooses an incompatible literal emitter.

---

## 18. Templates and staging

### 18.1 Hole vocabulary

| Hole | Meaning |
| --- | --- |
| `%tN` | Logical target type argument in Crane's established numbering. |
| `%stored(name)` | Physical stored type of a named component. |
| `%arg(name)` | Prepared operation argument identified by canonical binder name. |
| `%aN` | Prepared constructor argument or legacy operation argument. |
| `%ret` | Result type of the current construction or projection. |
| `%result` | Owning result slot in `WithBody`. |
| `%scrut` | Observed mapped value. |
| `%value` | Canonical value used to construct a view. |
| `%view` | View value being converted or materialized. |
| `%tmpN` | Fresh local identifier. |
| `%yield(name, e)` | Release expression through a named typed component port. |

### 18.2 Context-sensitive validation

Each template context has an explicit set of legal holes (`view_from_canonical`: `%value`, `%stored(name)`, type holes, fresh names; `read_from_write`: `%view`, ...; `MaterialiseView` construction: `%view`, result holes, ...; operation template: `%arg(name)`, `%stored(name)`, `%ret`, `%result`, fresh names; constructor test: `%scrut`, type holes, fresh names). Malformed or unavailable holes are registration errors.

### 18.3 Lexing

The template lexer must recognize comments, character and string literals, raw string literals, balanced delimiters, and mapping holes. It must not interpret hole-like text inside C++ literals or comments.

### 18.4 Control flow

Source branches, returns, recursive exits, and loopification remain structured compiler nodes. A foreign template may build an expression or execute a local body, but it must not silently take over source-level control flow. Unsupported `return`, `goto`, exception, or scope behavior in a template must be rejected or treated conservatively.

---

## 19. Validation rules

### 19.1 Mapping discovery

1. For each concrete `T`, at most one applicable `TypeMapping T` may resolve.
2. For each mapped source operation, at most one applicable `OperationMapping (Ref source)` may resolve.
3. Ambiguity is an error even if Rocq instance priority could choose one candidate.
4. Unconstrained evars in a selected instance are an error.
5. The plugin freezes the selected instance once per extraction plan.

### 19.2 C++ types

1. Canonical types may not contain a top-level reference.
2. `UnsafeVerbatim` produces a prominent diagnostic and disables automatic qualifier manipulation for that type.
3. Component names in `StoredComponent` must exist.
4. Structured pointer and const nodes must print with correct declarator binding.
5. View types must be passable by value and must not contain top-level references.

### 19.3 Copy and access

1. Every `CopyComponents` name must exist.
2. Every `ReadByComponents` name must exist.
3. `ReadWriteViews` is valid only for `MutableValue`, `MutableHandle`, or a compatible `ExplicitAccess`.
4. `Write` and `WriteCanonical` are invalid for read-only access models.
5. `Replace` is invalid for read-only access models.
6. A raw pointer with `NativeRAII` is invalid.
7. A fresh identity result requires an owning or externally justified lifetime model.

### 19.4 Views

1. `ReadViews` contains exactly one read view.
2. `ReadWriteViews` contains exactly one read and one writable view plus a writable-to-read conversion.
3. The `read_from_write` template must produce the declared read-view type from the declared writable-view type.
4. A `MaterialiseView` construction must produce the canonical logical type.
5. A `BorrowOnly` view may not be silently materialized.
6. A borrowed view result must name a valid owner path.
7. `ReadViewBorrow` requires a read view.
8. `WritableViewBorrow` requires a writable view.
9. A view that escapes its owner must retain an owner, materialize when allowed, or be rejected.
10. An operation that can reallocate backing storage must declare `InvalidatesViews`.

### 19.5 Constructors

1. Constructor references must belong to the mapped source family.
2. Each constructor may appear at most once.
3. Constructor argument positions must be valid after source parameter handling and erasure.
4. Projection field positions must exist.
5. `ReadViewProjection` requires a read view for the projected field type.
6. An unavailable constructor view is allowed only until source code needs to match the type; that use then produces a diagnostic.
7. `AbstractInterface` rejects direct source construction and matching.

### 19.6 Operations

1. Argument names are unique.
2. The argument list matches retained runtime binders in source order.
3. `%arg(name)` may refer only to a declared argument.
4. `Ignore` arguments may not appear in the template.
5. `PureOperation` rejects writes, replacement, fresh mutable identity, release, external effects, and external retention.
6. `Write` and `WriteCanonical` require a mutable type mapping.
7. `Replace` requires replace capability.
8. A `WritesComponent` target must exist.
9. A source argument named by `WritesComponent` or `RetainsArgument` must exist.
10. A borrowed result must identify a valid origin.
11. Mapped-operation summaries are used by interprocedural planning; missing summaries are conservative.

### 19.7 Numerals

1. Numeral constructors belong to the mapped type.
2. Field indices are valid.
3. The action matches the recursive field type.
4. The emitter receives only validated decimal text.
5. Converters return the mapped source type.

### 19.8 Trust boundary

Rocq checks the descriptor's Rocq types and constructor forms. Crane checks source identities, hole contexts, capabilities, and lifetime plans. The C++ compiler checks emitted types. Mapping-provided C++ remains trusted to obey its declared semantic contracts. C++ syntax alone does not prove those contracts: `const T&` does not prove non-retention; `T&` does not prove uniqueness; `std::string_view` or `std::span<T>` does not own storage; `std::move` does not prove that transfer occurred.

---

## 20. Compiled interfaces and separate compilation

A compiled Crane interface must record enough mapping information to prevent cross-unit ABI disagreement: selected `TypeMapping` and `OperationMapping` instance identities; canonical C++ type plan; copy model; access model; view types and escape policies; parameter ABI summaries; constructor plans; result provenance; component dependencies; lifetime and release model; operation facts. A consumer that resolves a different mapping for an imported source declaration must receive a diagnostic. Import order must not silently produce a different header signature. The Rocq dictionary itself is not emitted into C++.

---

## 21. Integration with current Crane

### 21.1 Relevant current files

| Current source | Responsibility |
| --- | --- |
| `theories/Mapping/Std.v` | Current standard mappings for option, product, string, int63, and float. |
| `theories/Monads/STMonad.v` | Current ST reference and raw-pointer ST array mappings. |
| `src/base/table.ml` | Current custom tables and `TriviallyCopyable` side tables. |
| `src/g_extraction.mlg` | Current mapping commands and parser entry points. |
| `src/cpp_ir/foreign_template.ml(i)` | Template parsing and placeholder categories. |
| `src/core_plan/ownership.ml(i)` | Existing interprocedural ownership fixed point. |
| `src/cpp_ir/grammar.ml` | Structured C++ type and expression IR. |
| `src/emit/print.ml` | Final C++ type and declaration printing. |
| `src/core_to_cpp/inductives.ml` | Constructor handling and release generation. |

### 21.2 New Rocq descriptor library

Add `theories/Mapping/Descriptor.v` defining `Declaration`, structured `Cpp.TypeExpr`, components, copy/access/value/lifetime models, view specifications, constructor mappings, numeral specifications, `TypeMapping`, operation argument/result/fact types, and `OperationMapping`. It should contain constructors and records, not an additional authoring facade.

### 21.3 Type-class discovery

At the first use of a concrete source type or mapped source operation: query the dedicated type-class database; enumerate successful applicable mapping instances; reject ambiguity; preserve declaration-reference boundaries while normalizing the selected dictionary; validate it; compile it to an internal plan; cache it by canonical source identity and instantiated source arguments.

### 21.4 Internal tables

```ocaml
type compiled_type_mapping = {
  instance : Names.GlobRef.t;
  source_pattern : Core.Type.t;
  canonical_type : Cpp_ir.lowered Cpp_ir.Type.t;
  components : compiled_component list;
  copy : copy_model;
  access : access_model;
  views : compiled_views;
  interface : compiled_interface;
  value_model : value_model;
  lifetime : lifetime_model;
  release : release_plan;
  numerals : compiled_numeral_spec option;
}

type compiled_operation_mapping = {
  instance : Names.GlobRef.t;
  source : Core.Ref.Can.t;
  template : compiled_template;
  arguments : compiled_argument_use list;
  result : compiled_result;
  facts : compiled_fact list;
  purity : purity;
}
```

Names are illustrative.

### 21.5 Access analysis

Add an access fixed point beside ownership. It should consume mapped-operation argument uses, generated-function direct calls, local stores, captures, and returns, constructor and projection uses, and view escape requirements. The final callable ABI record should store ownership, access, representation form, logical type, physical type, and required conversion for each parameter.

### 21.6 Declarator printer

Fix type printing independently of the mapping redesign. The printer must place const qualification at the correct level for pointers and references. Mapping metadata should reach CppIR as structured types, so the final printer never needs to infer pointer structure from text.

### 21.7 C++ standard

Generated code is compiled as C++26 (`-std=c++2c`). The standard mapping may therefore use `<span>`. Alternative imported mapping files remain free to choose other span implementations.

---

## 22. Migration from current commands

### 22.1 `Crane Extract Inductive`

During migration, translate an old inductive mapping to a conservative internal descriptor: canonical type parsed structured where possible, otherwise `UnsafeVerbatim`; copy `UnknownCopy` unless a legacy side declaration supplies more; access `ReadOnlyValue ReadByConstReference`; no views; translated constructors and match rule; value model `Unspecified`; lifetime `NativeRAII` only when the canonical type is a value owner, otherwise require explicit migration.

### 22.2 `Crane Extract Inlined Constant`

Translate to `OpaqueOperation` unless an explicit new `OperationMapping` exists. The compatibility path must not infer read, write, retention, or result provenance from C++ text.

### 22.3 `Crane TriviallyCopyable`

Preserve current behavior for legacy mappings, but deprecate the command in favor of explicit `BitCopy` / `CopyComponents [...]`. The migration must not translate an ST identity handle to `CopyComponents` merely because it has type arguments.

### 22.4 Mapping activation

New mappings need no registration or activation command. Exported type-class instances become available through ordinary Rocq imports.

### 22.5 Incremental coexistence

Resolution order during migration: prefer a unique new type-class mapping; if none exists, use the legacy mapping table; if both exist for the same declaration, report a conflict unless a temporary migration option explicitly permits the new mapping to replace the old one.

---

## 23. Implementation sequence

- **Phase 1, structured type correctness:** add the Rocq descriptor definitions; the minimal structured C++ type grammar; lower mapping `Cpp.TypeExpr` into CppIR types; reject top-level references in canonical mappings; fix declarator-correct printing; add focused printer tests (`T*`, `const T*`, `T* const`, `T*&`, `T* const&`, `const T*&`, `const std::shared_ptr<T>&`, `std::span<const T>`, `std::span<T>`) before changing parameter inference.
- **Phase 2, unique type-class resolution:** discover `TypeMapping T` instances; reject multiple applicable instances; preserve `Declaration.Ref` boundaries; compile and cache descriptors; record selected instance identities in extraction interfaces; import-based selection tests with two incompatible mapping modules.
- **Phase 3, type representation planning:** components and `StoredComponent` substitution; copy models; canonical access models; value and lifetime models; constructor mappings and projection lifetimes; release plans; replace relevant `TriviallyCopyable` queries with descriptor queries when a new mapping exists.
- **Phase 4, operation mappings:** `OperationMapping (Ref source)` discovery; bind named argument specifications to canonical runtime binders; compile `InputUse`, `ResultSpec`, `OperationFact`; preserve single source-argument evaluation; feed operation ownership and retention facts into the existing ownership fixed point; treat absent or legacy summaries conservatively.
- **Phase 5, access and representation fixed point:** add the lattice; summarize each generated function's parameters; propagate across direct calls; store logical and physical parameter types together; insert declared view conversions and materializations; prefer canonical parameters over repeated internal materialization; keep first-class callable ABIs canonical initially.
- **Phase 6, views:** `NoViews`, `ReadViews`, `ReadWriteViews`; `MaterialiseView` and `BorrowOnly`; read-view selection for `Read`; writable-view selection for `Write`; canonical bypass for `ReadCanonical` and `WriteCanonical`; owner provenance for borrowed view results; `InvalidatesElementBorrows` separately from `InvalidatesViews`; `std::string_view` and `std::span` regression tests.
- **Phase 7, ST arrays:** replace the raw pointer mapping with `shared_ptr<vector<T>>`; map `newArray` and `newListArray` to `make_shared`; contracts for `readArray`, `writeArray`, `getElems`; verify first that `swapArray` extracts as a separate function using the canonical mutable-handle ABI; add a bool-safe contiguous storage plan or another explicit solution to `vector<bool>`; add read and writable span views; verify span-enabled `swapArray` takes `std::span<T>`; add a multi-helper quicksort regression that does not rely on whole-program inlining; run ASan, UBSan, and LSan on ST tests; document shared-pointer cycle behavior.
- **Phase 8, standard mappings:** migrate `bool` if custom mapped; `option` and product; primitive string operations; int63 and float; exact-number mapping examples or tests; container mappings and release plans; deprecate legacy commands only after equivalent coverage exists.

---

## 24. Regression tests

- **24.1 Import selection:** import only A selects A; only B selects B; A and B gives an explicit ambiguity diagnostic naming both; separately compiled producer and consumer selecting different mappings gives an interface mismatch diagnostic.
- **24.2 Direct-constructor readability:** golden Rocq mapping files containing only record literals, the descriptor library's constructors, and ordinary `Some`, `None`, lists. They serve as documentation tests.
- **24.3 Pointer declarators:** `Pointer T, HandleByValue, Read` gives `T*`; `Pointer T, Replace` gives `T*&`; `Const(Pointer T), reference` gives `T* const&`; `Pointer(Const T), reference` gives `const T*&`. Compile with Clang and GCC.
- **24.4 Strings:** a function only calling string length takes `std::string_view`; several view-compatible operations `std::string_view`; a `c_str`-requiring operation `const std::string&`; observing and returning the input string `std::string`; a view result escaping as an ordinary Rocq string result is materialized `std::string`; a plain Rocq string operation declaring `Write` is a validation failure.
- **24.5 Structural spans:** read-only vector helper `std::span<const T>`; mutable-buffer helper with element writes `std::span<T>`; helper calling resize gets `std::vector<T>&` or the canonical handle ABI, not span; subspan within owner lifetime needs no materialization; subspan escaping with a materializable view is copied; borrow-only subspan escaping without owner is a diagnostic; resize after span creation requires and respects the invalidation fact.
- **24.6 ST arrays:** a function that reads one cell and writes it back compiles without inlining as `void read_then_write(std::span<T> array, index_type index)`; `swapArray` likewise; a helper chain `outer -> middle -> writeArray` propagates the writable requirement; mixed requirements (Read + Write gives `std::span<T>`; Write + WriteCanonical gives the canonical write ABI; retaining gives `shared_ptr<vector<T>>` by value; replacing gives `shared_ptr<vector<T>>&`).
- **24.7 Span compatibility and `vector<bool>`:** `STArray nat` with span-enabled storage reads through `span<const ...>` and writes through `span<...>`; `STArray bool` uses a bool-safe addressable stored representation or falls back to canonical handle access, never `span<bool>` over `std::vector<bool>`. Compile and run both read and write operations.
- **24.8 Raw pointer ST alternative:** a test-only raw-pointer mapping produces `vector<T>*` by value for Read/Write without views and `vector<T>*&` for Replace; it is rejected with `NativeRAII` and accepted only with region, external, or complete manual lifetime metadata.
- **24.9 ST resource lifetime:** LSan verifies that ordinary acyclic `newArray` and `newListArray` programs no longer leak under the shared-pointer mapping; a deliberate strong-reference cycle test, when the Rocq types permit one, documents that shared pointers do not collect it.
- **24.10 Option and product:** `option<bool>` canonical read by value; `option<string>` by const reference; a `Some string` payload used only for `Read` becomes `std::string_view` after projection conversion; a borrowed payload escaping its scrutinee retains an owner or is materialized; `pair<int,int>` by value; `pair<string,int>` by const reference.
- **24.11 Exact numbers:** `nat` O/S, `positive` xH/xO/xI, `N` N0/Npos, `Z` Z0/Zpos/Zneg build and match; large literals beyond 64 bits; negative `Z` literals; mapped arithmetic; recursive numeric functions; differential comparison with Rocq evaluation or OCaml extraction.
- **24.12 Invalid descriptors:** each produces a focused diagnostic: multiple `TypeMapping` instances; multiple `OperationMapping` instances; unknown component name; view with invalid `StoredComponent`; writable view on read-only access model; `Write`/`WriteCanonical`/`Replace` on a read-only type; raw pointer plus `NativeRAII`; `ReadViewBorrow` with no read view; `WritableViewBorrow` with no writable view; borrowed result with no owner; `PureOperation` containing `Write`; `PureOperation` containing `ReturnFreshIdentity`; `InvalidatesViews` naming an unknown component; constructor from the wrong family; invalid constructor field position; `Ignore` argument referenced by template; unavailable template hole.
- **24.13 Existing behavior:** run the complete current Crane test suite. Legacy mappings must retain their current behavior until migrated. New mappings should not change unrelated generated code.

---

## 25. Acceptance criteria

1. `TypeMapping T` is the only public type-mapping class and contains the descriptor fields directly.
2. `OperationMapping (Ref source)` is the only public operation-mapping class and contains its fields directly.
3. Neither class has a mapping-family parameter.
4. Imported mapping files determine available instances.
5. Ambiguous applicable instances are rejected explicitly.
6. Mapping examples use inductive constructors and records directly, without an author-facing helper layer.
7. Canonical C++ types are structured enough to distinguish pointer constness correctly.
8. A type can declare no views, one read view, or one read plus one writable view with an explicit writable-to-read conversion.
9. `std::string_view`, `std::span<const T>`, and `std::span<T>` are covered by the same view mechanism.
10. `Read`, `ReadCanonical`, `Write`, `WriteCanonical`, `Take`, and `Replace` have distinct semantics.
11. A raw pointer is passed by value for read/write-through access and by reference only for replacement.
12. A shared handle can be passed by `const&` while permitting mutation of its referent.
13. Generated helper requirements propagate across calls.
14. A helper using `WriteArray` can remain a separate function.
15. The standard `STArray` mapping has a real owner and does not unconditionally leak.
16. Span invalidation is distinct from element-borrow invalidation.
17. Borrow-only views cannot silently become canonical identities.
18. Compiled interfaces record selected mapping instances and physical ABIs.
19. Legacy commands continue to work conservatively during migration.
20. The complete regression suite and sanitizer tests pass.

---

## 26. Final model

A type mapping says: what is the canonical C++ value; what logical components it can contain; what copying means; how the canonical value is read; whether it can be mutated directly or through a handle; whether it has a read view and also a writable view; whether it is structural, identity-bearing, or unspecified; who owns its lifetime; how it is constructed, observed, and released; how numerals are emitted.

An operation mapping says, for each source argument, whether it is ignored, read through the preferred representation, read canonically, written through the preferred representation, written canonically, taken, replaced, or opaque; for the result, whether it is an independent value, a canonical borrow, a read or writable view, a preserved identity, a fresh identity, or opaque; and for dependencies and effects, which components are read or written, which arguments are retained, which element borrows or views are invalidated, which identities are released, and which external effects occur.

The compiler resolves one imported instance, validates it, freezes it, computes ownership and access requirements across calls, chooses the least powerful physical representation that satisfies every use, inserts only declared conversions, tracks owners for all non-owning views, and emits structured, declarator-correct C++ types.

```text
Rocq string
    canonical        std::string
    read             std::string_view
    canonical read   const std::string&
    owned result     std::string

structural vector
    canonical        std::vector<T>
    read             std::span<const T>
    canonical read   const std::vector<T>&

mutable buffer
    canonical        std::vector<T>
    read             std::span<const T>
    write            std::span<T>
    canonical write  std::vector<T>&

STArray
    canonical        std::shared_ptr<std::vector<T>>
    read             std::span<const T>
    write            std::span<T>
    canonical access const std::shared_ptr<std::vector<T>>&
    retain           std::shared_ptr<std::vector<T>>
    replace          std::shared_ptr<std::vector<T>>&
```
