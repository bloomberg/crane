# Reference Manual

This manual documents every Crane vernacular command, option and mapping
form, and the environment variables a user may set. For how the plugin works
inside, see [Compiler-Pipeline.md](Compiler-Pipeline.md).

Every command needs the plugin loaded: `From Crane Require Extraction.` (or
`From Crane Require Import Extraction.`). Command names, option names and
the syntax below are those of `src/g_extraction.mlg` and `src/base/table.ml`.

Contents:

- [Extracting](#extracting): `Crane Extraction` and its variants,
  `Crane Show Extraction`, `Crane Extraction Language`
- [Mappings](#mappings): how Rocq types and operations become C++
- [Typed mappings](#typed-mappings): `TypeMapping`, `OperationMapping`,
  `Crane Show Mapping`, `Crane Check Mapping`
- [Legacy mapping commands](#legacy-mapping-commands): `Crane Extract
  Inductive`, `Crane Extract Inlined Constant`, `Crane Extract Constant`,
  `Crane Extract Foreign Constant`, `Crane Extract Numeral`,
  `Crane TriviallyCopyable`, `Crane Extract Monad`, `Crane Extract Skip`,
  `Crane Extract Skip Module`, `Crane Extract Void`, `Crane Extract Callback`
- [Which headers a unit includes](#which-headers-a-unit-includes)
- [`Crane Bake`](#crane-bake)
- [Code generation options](#code-generation-options): `StdLib`, `Loopify`,
  `Reuse`, `Arena`, `NonAtomicRc`, `SingleThreaded`, `FastVariant`,
  `SharedVariant`, `BoxedFields`, `Format Style`, output and optimisation
  options
- [Other commands](#other-commands): `Crane Extraction Inline`,
  `Crane Extraction Implicit`, `Crane Extraction Blacklist`,
  `Crane Guard Compare`, `Crane Benchmark`
- [Environment variables](#environment-variables)

---

## Extracting

### `Crane Extraction`

```coq
Crane Extraction <qualid>.
Crane Extraction "<output path>" <qualid> ... <qualid>.
Crane Recursive Extraction <qualid> ... <qualid>.
Crane Separate Extraction <qualid> ... <qualid>.
Crane Extraction Library <ident>.
Crane Recursive Extraction Library <ident>.
Crane Extraction TestCompile <qualid> ... <qualid>.
Crane Extraction TestCompile "<output path>" <qualid> ... <qualid>.
```

* `Crane Extraction <qualid>` extracts one definition, module or type with
  its dependencies and prints the code instead of writing files.
* `Crane Extraction "<output path>" ...` writes `<output path>.h` and
  `<output path>.cpp` (a trailing `.cpp` in the path is dropped). A relative
  path is resolved against the output directory (see
  [Output options](#output-options)). The usual form names one module:
  `Crane Extraction "tokenizer" Tokenizer.` The module becomes a C++ struct
  (or a namespace) named after it.
* `Crane Recursive Extraction` extracts several definitions and their
  dependencies together and prints the result.
* `Crane Separate Extraction` writes one `.h`/`.cpp` pair per Rocq library
  the definitions and their dependencies come from, each including the
  headers of the libraries it uses.
* `Crane Extraction Library <ident>` extracts the loaded library `<ident>`
  to files named after it; `Crane Recursive Extraction Library` also extracts
  every library it depends on.
* `Crane Extraction TestCompile` extracts as `Crane Extraction` does and then
  compiles the result with `clang++` (using the `StdLib` and BDE settings),
  as a check that it builds.

Every extraction uses the mappings and options in effect at the command.
A unit that includes the header of a unit extracted earlier (separate
extraction across files) must resolve the same typed mappings for the heads
that header was written against; a different instance or no mapping is an
error naming both.

### `Crane Show Extraction`

```coq
Crane Show Extraction.
```

Inside a proof, prints the C++ extraction of the term built so far.

### `Crane Extraction Language`

```coq
Crane Extraction Language C++.
```

`C++` is the only language. The command exists for parity with Rocq's
extraction.

---

## Mappings

A mapping tells Crane how to represent a Rocq type, or how to implement a
Rocq operation, in C++. Without one, Crane generates its own C++ for every
inductive type and function it extracts.

There are two mechanisms:

* **Typed mappings** are type-class instances of `TypeMapping` and
  `OperationMapping` from `theories/Mapping/Descriptor.v`. They state the C++
  type as structured data, and contracts that the access, ownership and view
  analyses read: how a value is copied, read, written and passed, and what
  an operation does with each argument. An instance is active when the
  module that declares it is imported (`#[export] Instance`), so the imports
  of a file are its mapping configuration. Every mapping in
  `theories/Mapping/` and the ST arrays and references of
  `Monads/STMonad.v` are typed.
* **Legacy mapping commands** (`Crane Extract Inductive`, `Crane Extract
  Inlined Constant`, ...) give C++ as template strings with no contract.
  They remain necessary for monads and effects (`Crane Extract Monad`,
  `Skip`, `Void`), which have no typed form yet, and are used by the effect
  libraries in `theories/Monads/` and `theories/External/`.

A head may be mapped by one mechanism only. When an extraction starts, a
head mapped both by an active instance and by a legacy `Crane Extract ...`
(or `Crane Extract Numeral`) command is an error:

```text
Crane: option is mapped twice: by the typed mapping std_option_mapping and by
a legacy Crane Extract command. ...
```

Because typed instances activate on `Import`, a bare
`Require Crane.Mapping.Std.` no longer selects the standard mappings; write
`From Crane Require Import Mapping.Std.`

---

## Typed mappings

The descriptor library is `Crane.Mapping.Descriptor`. It contains inductive
types and records only. Strings are `PrimString.string`, so a mapping file
opens `pstring_scope`. How the pipeline compiles and uses a mapping is in
[Compiler-Pipeline.md](Compiler-Pipeline.md#7-typed-mappings-in-the-pipeline).

A typed mapping separates questions a C++ type string cannot answer: what a
copy costs (`type_copy`), how the canonical value is read, written and
replaced (`type_access`), which cheaper non-owning views exist
(`type_views`), whether copies share one identity (`type_model`), and who
releases the resource (`type_lifetime`). Every mapped type has one canonical
C++ type, used for stored fields, owned locals and parameters, results and
captures; references and views are added by Crane where a function's use of
a value allows them.

### Example

An abstract type mapped to `std::uint64_t`, with three operations:

```coq
From Corelib Require Import PrimString.
From Stdlib Require Import List.
Import ListNotations.
From Crane Require Import Extraction Mapping.Descriptor.
From Crane Require Import Mapping.Std Mapping.NatIntStd.
Open Scope pstring_scope.

Axiom Counter : Type.
Axiom counter_zero : Counter.
Axiom counter_add : Counter -> nat -> Counter.
Axiom counter_value : Counter -> nat.

#[export] Instance counter_mapping : TypeMapping Counter :=
  {| type_headers := ["cstdint"];
     type_cpp := Crane.Cpp.Name "std::uint64_t";
     type_components := [];
     type_copy := BitCopy;
     type_access := ReadOnlyValue ReadByValue;
     type_views := NoViews Counter;
     type_interface := AbstractInterface;
     type_model := Structural;
     type_lifetime := NativeRAII;
     type_release := OrdinaryRelease;
     type_numerals := None |}.

#[export] Instance counter_zero_mapping : OperationMapping (Ref counter_zero) :=
  {| operation_headers := ["cstdint"];
     operation_cpp := Expr "std::uint64_t{0}";
     operation_contract := PureOperation [] ReturnValue [] |}.

#[export] Instance counter_add_mapping : OperationMapping (Ref counter_add) :=
  {| operation_headers := [];
     operation_cpp := Expr "(%arg(c) + %arg(n))";
     operation_contract :=
       PureOperation
         [{| argument_name := "c"; argument_use := Read |};
          {| argument_name := "n"; argument_use := Read |}]
         ReturnValue [] |}.

#[export] Instance counter_value_mapping : OperationMapping (Ref counter_value) :=
  {| operation_headers := [];
     operation_cpp := Expr "%arg(c)";
     operation_contract :=
       PureOperation [{| argument_name := "c"; argument_use := Read |}]
         ReturnValue [] |}.

Module Counting.
Definition total (xs : list nat) : nat :=
  counter_value (fold_left counter_add xs counter_zero).
End Counting.

Crane Extraction "counting" Counting.
```

`Counting::total` is generated as a fold over the list whose accumulator is
a `std::uint64_t`, starting at `std::uint64_t{0}` and adding with
`(_x0 + _x1)`. Algebraic examples (a user inductive mapped to
`std::uint8_t` or `std::optional`, matches included) are in
`tests/regression/typed_mapping_algebraic/`; `theories/Mapping/StdCore.v` maps
`option` and `prod` the same way.

### `TypeMapping T`

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

An instance may be parametric (`Instance m (A : Type) : TypeMapping (option
A)`); it is compiled once per head, and a type argument at a use stands for
the parameter it instantiates.

| Field | Meaning |
| --- | --- |
| `type_headers` | Headers the C++ type needs, included wherever a unit uses the type. |
| `type_cpp` | The canonical C++ type, structured: `Crane.Cpp.Name "std::string"`, `Crane.Cpp.Apply "std::optional" [Crane.Cpp.TypeArg t]`, `Crane.Cpp.Pointer t`, `Crane.Cpp.Const t`, `Crane.Cpp.StoredComponent "c"` (the C++ type Crane chose for component `c`), `Crane.Cpp.SourceType T` (the C++ type of a Rocq type), `Crane.Cpp.UnsafeVerbatim "..."` (raw text; warns). `Crane.Cpp.ValueArg "..."` is a non-type template argument. Must not be a reference. |
| `type_components` | Named parts of the value, each `{\| component_name := "c"; component_type := ... \|}`: `KnownType A` (a type parameter) or `FieldType (Ref ctor) i` (field `i`, from 0 after the parameters, of a constructor). Templates refer to them with `%stored(c)`. |
| `type_copy` | What a copy costs: `BitCopy` (scalar or raw handle), `RetainIdentity` (shares one identity, as `shared_ptr`), `DuplicateValue` (independent copy, possibly expensive), `CopyComponents ["c"; ...]` (a bounded aggregate that costs what the named components cost, as `std::optional` or `std::pair`; not a container such as `std::vector` or `std::deque`, which copies every element and is `DuplicateValue`), `UnknownCopy`. Replaces `Crane TriviallyCopyable`. |
| `type_access` | How the canonical value may be read, written and passed (below). |
| `type_views` | `NoViews T`, `ReadViews r`, or `ReadWriteViews r w read_from_write` (below). |
| `type_interface` | `AbstractInterface` (no constructors visible: building or matching the type in source is an error, so it is used only through mapped operations), or `AlgebraicInterface [ctor mappings]`: how each constructor is built and matched (below). `AlgebraicInterface []` is an empty type. |
| `type_model` | `Structural` (copies are the same value), `Identity` (copies alias one mutable identity), `Unspecified`. Independent of `type_copy`: a small integer handle is `BitCopy` and `Identity`. |
| `type_lifetime` | `NativeRAII` (the C++ value owns its resource), `RegionOwned (Ref r)`, `ExternallyOwned`, `ManualShared (Ref retain) (Ref release)`. A raw pointer with `NativeRAII` is rejected. |
| `type_release` | `OrdinaryRelease` or `DrainWith "..."`. |
| `type_numerals` | How a literal of the type is written (below), or `None`. |

`type_model`, `RegionOwned`, `ManualShared` and `DrainWith` are validated and
recorded in a unit's compiled interface; code generation does not yet act on
them.

#### Access models

| `type_access` | Canonical read | Write through | Replace | Take |
| --- | --- | --- | --- | --- |
| `ReadOnlyValue ReadByValue` | `T` | invalid | invalid | `T` |
| `ReadOnlyValue ReadByConstReference` | `const T&` | invalid | invalid | `T` |
| `ReadOnlyValue (ReadByComponents cs)` | `T` if every component in `cs` is read by value, else `const T&` | invalid | invalid | `T` |
| `MutableValue style` | from `style` | `T&` | `T&` | `T` |
| `ReadOnlyHandle HandleByValue` | `T` | invalid | invalid | `T` |
| `ReadOnlyHandle HandleByConstReference` | `const T&` | invalid | invalid | `T` |
| `MutableHandle HandleByValue` | `T` | `T` | `T&` | `T` |
| `MutableHandle HandleByConstReference` | `const T&` | `const T&` | `T&` | `T` |

`ExplicitAccess {| explicit_read := ...; explicit_write := ...;
explicit_replace := ... |}` gives each form directly (`CanonicalByValue`,
`CanonicalByConstReference`, `CanonicalByMutableReference`, or
`ExactParameter "..."`, which warns).

Writing through a value and replacing it are different capabilities. A raw
pointer handle (`MutableHandle HandleByValue`) is passed as `T*` to write
its pointee, which costs one word, and as `T*&` only to a function that may
reseat the caller's pointer. A `const std::shared_ptr<V>&`
(`MutableHandle HandleByConstReference`) cannot be reseated, but its `V` can
be written, and passing it avoids a reference-count update.

Crane picks each generated function's parameter form from what the function
does with the parameter, joined over its uses and across the functions it
calls (the access analysis), and from the type's access model. In order:

1. a parameter the function keeps (owns) is taken as `T`;
2. one it replaces takes the replace form (`T&`);
3. one it writes takes the writable view, where the type has one and no use
   needs the canonical representation (`WriteCanonical`), else the
   write-through form;
4. one it only reads takes the read view, where the type has one and no use
   needs the canonical representation (`ReadCanonical`), else the canonical
   read form.

So a function that only reads a `ReadByConstReference` value takes
`const T&`, one that writes through a `MutableHandle HandleByConstReference`
handle takes `const T&` too, one that replaces it takes `T&`, and one that
keeps it takes `T`. Views and mutable references are given only to top-level
generated functions that are called directly. A function named as a value
(passed, stored, partially applied) or generated as a method keeps canonical
forms, and takes a copy by value of a parameter it writes or replaces;
lambdas and local fixpoints keep canonical forms.

#### Views

A view is a non-owning value, cheap to pass, that a function may take
instead of the canonical value:

```coq
Record ViewSpec (T : Type) (mode : ViewMode) : Type := {
  view_headers : list string;
  view_cpp : Crane.Cpp.TypeExpr;
  view_from_canonical : string;   (* %value: a live canonical value *)
  view_escape : ViewEscape T      (* MaterialiseView (Expr "...%view...") | BorrowOnly *)
}.
```

`ReadViews r` declares a read view; `ReadWriteViews r w "..."` adds a
writable view and the conversion (over `%view`) that narrows it to the read
view. A parameter that is only read (`Read`) takes the read view, one that
is written (`Write`) the writable view. A view returned borrowed from an
operation stays a view while its owner lives; where it escapes (returned,
stored, passed canonically) it is materialised by `MaterialiseView`, or
refused under `BorrowOnly`. A view passed beside an argument the callee may
invalidate views of is taken of a copy, or refused.

`BorrowOnly` is for a view whose owner has an identity: copying the elements
of an ST array's span into a new array would make a different array. A view
does not keep its owner alive.

At a call Crane converts only with the declared conversions: a canonical
value with `view_from_canonical`, a writable view to the read view with
`read_from_write`; a view of the kind taken is passed as it is. A
`MaterialiseView` construction must be an `Expr`. The read view of a type
with literals (a string) must be constructible from a C++ string literal and
from a literal and its length: a literal passed as a view is the view of the
literal.

Element assignment (`InvalidatesElementBorrows`) and reallocation
(`InvalidatesViews`, a resize) are distinct facts: assigning an element
leaves a span over the array valid. An operation that may reallocate takes
its argument `ReadCanonical`, `WriteCanonical` or `Replace`; validation
refuses `InvalidatesViews` on an argument given as a view.

The standard string mapping (`Mapping/Std.v`) declares a
`std::string_view` read view materialised as `std::string`, so a generated
function that only reads a string takes `std::string_view`. ST arrays
(`Monads/STMonad.v`) declare `std::span<const T>` and `std::span<T>` views,
`BorrowOnly`.

#### Constructors and matches

```coq
Record ConstructorMapping : Type := {
  ctor_source : Declaration;           (* Ref (@Some A) *)
  ctor_build : Construction;           (* Expr "..." or WithBody "init" "body" *)
  ctor_view : option ConstructorView
}.
Record ConstructorView : Type := {
  view_requirement : ObservationRequirement;  (* PreferredObservation | CanonicalObservation *)
  case_test : string;                          (* over %scrut *)
  case_fields : list (nat * Projection)        (* field index, projection *)
}.
```

A projection is `OwnedProjection "..."` (a new value),
`CanonicalBorrowProjection "..."` (a reference into the scrutinee) or
`ReadViewProjection "..."` (a read view of a field). A match tests the
constructor views in the order the list gives them; the last needs no test.
Each constructor of the type appears at most once.

#### Numerals

```coq
Record NumeralSpec (T : Type) : Type := {
  numeral_cases : list NumeralCase;      (* per constructor: NumeralZero, NumeralOne,
                                            NumeralSuccessor i, NumeralDouble i,
                                            NumeralDoublePlusOne i, NumeralIdentity i,
                                            NumeralNegate i *)
  numeral_emitter : NumeralEmitter;      (* IntegerToken "prefix" "suffix"
                                            | DecimalConstructor "callee" *)
  numeral_converters : list Declaration  (* e.g. [Ref Nat.of_num_uint] *)
}.
```

`Mapping/NatIntStd.v` maps `nat` to `uint64_t` with
`IntegerToken "UINT64_C(" ")"`, so `S (S (S O))` is written `UINT64_C(3)`.
A typed type's literals come from its descriptor; an extraction where the
type also has a `Crane Extract Numeral` fails. The actions name no
constructor Crane knows: each constructor has at most one case, a
successor or doubling action's field is of the mapped type, an identity or
negation action's field is of another inductive (whose own numeral it
reads), the emitter's text only wraps a numeric literal (`IntegerToken`) or
is a qualified name (`DecimalConstructor`), and every converter returns the
mapped type.

### `OperationMapping (Ref op)`

```coq
Class OperationMapping (source : Declaration) : Type := {
  operation_headers : list string;
  operation_cpp : Construction;
  operation_contract : OperationContract
}.
```

`Ref op` names the operation by identity; Crane never unfolds it.
`Ref (@fst)` and `Ref (@PrimArray.get)` name polymorphic operations.
`operation_cpp` is `Expr "..."` or `WithBody "init" "body"`, where the body
completes the `%result` slot the initialiser declares.

The contract is `PureOperation args result facts`,
`EffectfulOperation args result facts`, or `OpaqueOperation`. `args` binds
one `{| argument_name := "x"; argument_use := u |}` to each argument Crane
keeps at run time, in source order (type arguments, proofs, type-class
instances and `Crane Extraction Implicit` positions are not listed); the
template names them `%arg(x)`. Crane evaluates every argument once, in
source order, before the template is expanded, however often the template
mentions it.

| `InputUse` | Meaning | Parameter it asks for |
| --- | --- | --- |
| `Ignore` | not observed; the template may not mention it | none |
| `Read` | read during the call | read view if any, else canonical read |
| `ReadCanonical` | read, and needs the canonical representation | canonical read |
| `Write` | mutated in place during the call, not kept | writable view if any, else write-through |
| `WriteCanonical` | mutated, needs the canonical representation | write-through |
| `Take` | owned by the operation | the value (moved at its last use, else copied) |
| `Replace` | may replace or reseat the caller's value | `T&` |
| `OpaqueUse` | unknown | conservative |

A view is given only to an argument whose binder's type is a mapped type
declaring one: an argument typed by a type variable (`d : A`) receives the
canonical value whatever its use, so a caller's parameter passed there is
not taken as a view. An argument written or replaced in place must be a
variable the caller may write; anything else is copied into a temporary
for the call.

| `ResultSpec` | Meaning |
| --- | --- |
| `ReturnValue` | a new value |
| `ReturnBorrowed form {\| path_argument := "x"; path_components := [...] \|}` | a borrow (`CanonicalBorrow`, `ReadViewBorrow`, `WritableViewBorrow`) of a component of argument `x` |
| `ReturnSameIdentity "x"` | the identity of argument `x` |
| `ReturnFreshIdentity inits` | a new identity, with its components initialised from arguments |
| `ReturnOpaque` | unknown |

Facts: `ReadsComponent path`, `WritesComponent path (Some "x")`,
`InvalidatesElementBorrows path` (an element assignment),
`InvalidatesViews path` (a resize), `RetainsArgument "x" path`,
`ReleasesIdentity "x"`, `ExternalEffect "name"`. A `PureOperation` may not
write, replace, return a fresh identity, write a component, retain outside
its result, release, or have an external effect.

`Mapping/StdCore.v` maps `fst` and `snd` as borrows
(`ReturnBorrowed CanonicalBorrow` of component `first`/`second`), so a `let`
binding one out of a pair binds it by `const` reference.

### Template holes

| Hole | Meaning | Allowed in |
| --- | --- | --- |
| `%arg(x)` | the prepared argument named `x` | `operation_cpp` |
| `%aN` | constructor argument `N` | `ctor_build` |
| `%stored(c)` | the C++ type of component `c` | everywhere |
| `%tN` | the C++ type of type argument `N` | everywhere |
| `%ret` | the result type | `ctor_build`, projections, `operation_cpp`, `MaterialiseView` |
| `%result` | the owning result slot | the body of a `WithBody` |
| `%scrut` | the value matched | `case_test`, projections |
| `%value` | the canonical value a view is made from | `view_from_canonical` |
| `%view` | the view being converted or materialised | `read_from_write`, `MaterialiseView` |
| `%tmpN` | a fresh local name | reserved: accepted by validation, but compiling a constructor, match, view or operation template that uses it is an error (not supported yet; use `WithBody` and `%result`) |

Holes are found outside C++ comments and string and character literals
(raw string literals are not recognised). A hole not allowed in its context,
or a `%stored(c)` naming an undeclared component, is an error when the
mapping is resolved.

### Restrictions

* An instance must apply to every instantiation of its head's parameters:
  `Instance m (A : Type) : TypeMapping (option A)` is accepted,
  `TypeMapping (option nat)` is not (a plan is compiled once per head, from
  the instance at fresh variables).
* A component's type, and every `SourceType`, must be one of the mapped
  type's parameters (`KnownType A`, or a `FieldType` declared at one), so
  that its C++ type is the one Crane chose for that type argument.
* In an operation, `%stored(c)` is resolved against the mapped types of the
  arguments in source order, then of the result (looking inside it, so a
  monadic result counts); the first one declaring `c` decides, and `c`'s
  type there must be a type parameter of the operation.
* A constant reachable under two names is one head: `PeanoNat.Nat.add` is
  `Nat.add` (an `Include`), so mapping both is an ambiguity.

### Selection and errors

For a type or operation, Crane tries every active instance with that head
and unifies its class argument with the use:

* none applies: the head is unmapped and Crane generates its own C++;
* one applies: it is decoded, validated and compiled;
* more than one applies: an error naming all of them. Instance priorities
  are never consulted, so importing two modules that map the same type
  differently is an error, not an override.

Validation errors name the instance, the mapped type or operation, and the
rule broken (an argument list that does not match the retained arguments,
`Write` on a read-only type, a canonical type that is a reference,
`ReadWriteViews` on a read-only access model, a constructor listed twice, a
field index out of range, ...). `UnsafeVerbatim` and `ExactParameter` are
accepted with the warning `crane-mapping-unsafe`.

Crane checks a mapping's shape, its holes and the capabilities its contract
claims, and Clang checks the emitted types. The C++ text itself is trusted
to do what the contract says: nothing checks that a `Read` operation does not
write or that a `const T&` argument is not retained.

### `Crane Show Mapping` and `Crane Check Mapping`

```coq
Crane Show Mapping <term>.
Crane Check Mapping <term> Selects <qualid>.
Crane Check Mapping <term> Unmapped.
Crane Check Mapping <term> Fails With "<text>".
```

* `Crane Show Mapping` prints the instance that maps a type or an operation
  and the decoded descriptor:

  ```text
  Counter is mapped by counter_mapping:
  TypeMapping
    type_headers := ["cstdint"]
    type_cpp := Name "std::uint64_t"
    ...
  ```

* `Crane Check Mapping ... Selects inst` fails unless `inst` maps the term;
  `Unmapped` fails if any typed mapping applies; `Fails With "text"` fails
  unless resolving the mapping fails with a message containing `text`
  (spacing ignored). They are meant for tests:

  ```coq
  Crane Check Mapping (option nat) Selects std_option_mapping.
  Crane Check Mapping (list nat) Unmapped.
  ```

`CRANE_TRACE_MAPPINGS=1` reports, during extraction, every discovered head
and every resolved descriptor.

### What has no typed form yet

Monads (`Crane Extract Monad`), effect events, `Crane Extract Skip` and
`Crane Extract Void` have no typed counterpart; the effect libraries and
`External/` use the legacy commands. The legacy commands are not deprecated
until they do.

To migrate a legacy mapping, remove the legacy command (a head mapped both
ways is an error) and write:

| Legacy | Typed |
| --- | --- |
| `Crane Extract Inductive T => "..." [ctors] "match"` | `TypeMapping T` with `type_cpp`, and `AlgebraicInterface` with one `ConstructorMapping` per constructor (its build template and, for matching, a `ConstructorView`) |
| `Crane Extract Inlined Constant` of a type constant | `TypeMapping` with `AbstractInterface` |
| `Crane Extract Inlined Constant f => "..."` | `OperationMapping (Ref f)` with named arguments and a contract |
| `Crane TriviallyCopyable T` | `type_copy := BitCopy` or `CopyComponents [...]` |
| `Crane Extract Numeral T => "..."` | `type_numerals` |
| `From "header"` | `type_headers`, `operation_headers` |

Import the module that declares the instances where the legacy file was
only `Require`d.

---

## Legacy mapping commands

These commands map with C++ template strings. A string argument written as
`"..."` may also be a bare identifier where the grammar says `cppname`.

### `Crane Extract Inductive`

```coq
Crane Extract Inductive <inductive> => "<C++ type>"
  [ "<constructor 0>" ... "<constructor n>" ]
  ["<match template>"]
  [Boxed Element "<wrapper>"]
  [Drain "<drain template>"]
  [From "<header>" ...].
```

The clauses must appear in this order; each in brackets is optional. The
constructor list must have one entry per constructor.

| Placeholder | Meaning |
| --- | --- |
| `%t0`, `%t1`, ... | type parameters of the inductive |
| `%a0`, `%a1`, ... | constructor arguments |
| `%scrut` | the matched value |
| `%b0a0` | name bound to argument 0 of branch 0 |
| `%br0`, `%br1`, ... | the branch for constructor 0, 1, ... |
| `%elem` | the element slot of a container with a `Boxed Element` clause |
| `%yield(e)` | in a `Drain` template: push child `e` onto the destructor's worklist |

```coq
Crane Extract Inductive prod =>
  "std::pair<%t0, %t1>"
  [ "std::make_pair(%a0, %a1)" ]
  "const auto& [%b0a0, %b0a1] = %scrut; %br0"
  From "utility".
```

(`option` and `prod` are typed in `Mapping/StdCore.v`; the example is how a
legacy mapping is written.)

#### `Boxed Element`

Some containers need a complete element type where the container type is
named (the immer containers do). An inductive recursive through such a
container, for example a `json` with a field of type `list json`, would name
it with an incomplete element type. `Boxed Element "<wrapper>"` wraps the
element in a pointer-sized indirection only at those recursive occurrences.
Write `%elem` instead of `%t0` in the container's type and constructor
templates; Crane resolves it to the wrapper applied to the element where the
element is a generated inductive recursive through this container, and to
the bare element otherwise. The wrapper must be pointer-sized, copyable, and
convert implicitly to and from `%t0`.

```coq
Crane Extract Inductive list =>
  "immer::flex_vector<%elem>"
  [ "immer::flex_vector<%elem>{}"
    "%a1.push_front(%a0)" ]
  "if (%scrut.empty()) { %br0 }
   else { const %t0& %b1a0 = %scrut.front();
          auto %b1a1 = %scrut.drop(1); %br1 }"
  Boxed Element "immer::box<%t0>"
  From "immer/flex_vector.hpp" "immer/box.hpp".
```

The recursive `list json` becomes `immer::flex_vector<immer::box<json>>`;
`list ascii` stays `immer::flex_vector<char>`. A field already boxed this way
is stored by value, not behind another `std::shared_ptr`.

#### `Drain`

A generated inductive's destructor frees deep values with a loop instead of
recursion. For a field held in a mapped container, `Drain` says how to hand
the container's children to that loop: `%scrut` is the container, and
`%yield(e)` pushes child `e`. Without it the destructor assumes a
smart-pointer field.

```coq
Crane Extract Inductive list =>
  "crane::list<%t0>"
  [ "crane::list<%t0>{}" "crane::cons(%a0, %a1)" ]
  "if (%scrut.empty()) { %br0 } else { const %t0& %b1a0 = %scrut.front(); auto %b1a1 = %scrut.tail(); %br1 }"
  Boxed Element "crane::box<%t0>"
  Drain "%scrut.drain_each([&](auto&& _e) { %yield(std::move(_e)); });"
  From "conslist.h".
```

### `Crane Extract Inlined Constant`

```coq
Crane Extract Inlined Constant <qualid> => "<C++ expression>" [From "<header>" ...].
```

Replaces every use of the constant by the expression, with `%a0`, `%a1`, ...
for its arguments. A constant whose type is a type (`Axiom point : Type.`)
is mapped to a C++ type this way.

```coq
Axiom larger : nat -> nat -> nat.
Crane Extract Inlined Constant larger => "std::max(%a0, %a1)" From "algorithm".
```

An inlined constant has no contract: the access and ownership analyses treat
each argument as a canonical read, and the argument is evaluated once if the
template mentions it more than once.

### `Crane Extract Constant`

```coq
Crane Extract Constant <qualid> [ "<id>" ... ] => "<C++ callable>" [From "<header>" ...].
```

Implements a `Parameter` or `Axiom` (a constant without a body). Crane
generates a function with the constant's signature whose body calls the C++
callable with the constant's arguments in order:

```coq
Parameter foreign_inc : nat -> nat.
Crane Extract Constant foreign_inc => "foreign_inc_impl" From "foreign_inc_impl.h".
```

```cpp
uint64_t foreign_inc(uint64_t x0_) { return foreign_inc_impl(x0_); }
```

The callable is a name, not a `%a0` template. The optional list of strings
is accepted for parity with Rocq's extraction and ignored. On a constant
with a body the command has no effect.

### `Crane Extract Foreign Constant`

```coq
Crane Extract Foreign Constant <qualid> => "<C++ callable>".
```

As `Crane Extract Constant`, for function-typed constants only and without a
`From` clause. Name a C++ function other than the generated one: the
forwarding function has the Rocq constant's name.

```coq
Parameter native_checksum : nat -> nat.
Crane Extract Foreign Constant native_checksum => "native_checksum_impl".
Crane Print Extraction Foreign.
```

`Crane Print Extraction Foreign` lists the constants mapped so.

### `Crane Extract Numeral`

```coq
Crane Extract Numeral <inductive> => "<format>".
```

Folds constructor chains of a unary or binary number type (`S (S (S O))`,
`xO (xI xH)`) into a literal: `%n` in the format is the value. The format
must be a numeric-literal wrapper: exactly one `%n`, and none of `;`, braces,
quotes, backslash, slash or brackets.

```coq
Crane Extract Numeral nat => "%nu".
Crane Extract Numeral Z => "INT64_C(%n)".
```

Every standard number mapping is typed and declares its numerals in its
descriptor: with one of them imported, a `Crane Extract Numeral` on the same
type makes the next extraction fail.

### `Crane TriviallyCopyable`

```coq
Crane TriviallyCopyable <inductive> ... .
```

Declares that the C++ type a legacy `Crane Extract Inductive` mapping
produces is trivially copyable whenever its type arguments are, so Crane
copies it where it would otherwise move or take a reference (most visibly in
loop frames). Built-in scalar names (`int`, `uint64_t`, `double`, ...) need
no declaration. The type must have a legacy mapping; a typed mapping states
its copy cost in `type_copy`, and the command is an error on it.

### `Crane Extract Monad`

```coq
Crane Extract Monad <monad> [ bind := <qualid> , ret := <qualid> ] => "<C++ type>" [From "<header>" ...].
Crane Extract Monad <monad> [ bind := <qualid> , ret := <qualid> ] [From "<header>" ...].
```

`bind` and `ret` may be given in either order. Crane lowers `bind` to
sequential statements and `ret` to the value; the C++ type, with `%t0` for
the result type, is the type of a computation (`"%t0"` when omitted).

```coq
Crane Extract Monad STM [ bind := bind , ret := Ret ] => "%t0".
```

### `Crane Extract Skip` and `Crane Extract Skip Module`

```coq
Crane Extract Skip <qualid>.
Crane Extract Skip Module <module>.
```

Crane emits nothing for the constant, type or module and assumes the C++
provides it. Uses are inlined to nothing; a mapping that still refers to a
skipped type sees it erased.

```coq
Crane Extract Skip Module Rdefinitions.RbaseSymbolsImpl.
```

### `Crane Extract Void`

```coq
Crane Extract Void <void type> [ <ghost term> ].
```

Registers an uninhabited type and a term of it that Rocq requires but that
never exists at run time. Both are erased from the generated C++.

### `Crane Extract Callback`

```coq
Crane Extract Callback ["<label>"] <qualid>.
Crane Print Extraction Callback.
Crane Reset Extraction Callback.
```

Records a constant as an entry point for foreign code, with an optional
label. The registration is stored and listed, but the C++ backend does not
use it yet.

---

## Which headers a unit includes

A generated unit includes the headers of every mapping its code uses, and of
every mapped type its code computes with, including a type it never spells
(such as the type a mapped operation returns into a temporary). A mapping in
scope that the code does not use contributes no header.

So an operation mapping names the headers its own text needs, except those
of the mapped types it takes or returns:

```coq
Axiom point : Type.
Axiom origin_at : bool -> point.
Axiom on_axis : point -> bool.
Definition is_real (b : bool) : bool := on_axis (origin_at b).

Crane Extract Inlined Constant point => "std::complex<double>" From "complex".
Crane Extract Inlined Constant origin_at => "std::complex<double>(%a0 ? 1.0 : 0.0, 0.0)".
Crane Extract Inlined Constant on_axis => "(%a0.imag() == 0.0)".
```

`origin_at` and `on_axis` need no `From` clause: code using either computes
with a `point`, so `<complex>` is included.

A type mapping (an inductive, a constant whose type is a type, a monad, a
`Boxed Element` wrapper) must name the header that declares its C++ type.
Where a legacy one has no `From` clause and its type names anything but
builtin types and placeholders, Crane warns
(`crane-mapping-without-header`). A legacy operation mapping that writes a
standard-library name whose header is neither in its `From` clause nor in
that of a mapped type its signature names gets
`crane-mapping-standard-header`, once, when code using it is first
extracted:

```coq
Axiom larger : nat -> nat -> nat.
(* Warns: std::max is declared in <algorithm>. *)
Crane Extract Inlined Constant larger => "std::max(%a0, %a1)".
```

A typed mapping lists its headers in `type_headers`, `operation_headers` and
`view_headers`.

---

## `Crane Bake`

```coq
Crane Bake <qualid> ... <qualid>.
Set Crane Bake Flags "<extra clang++ flags>".
```

Computes each closed constant once, when the command runs, and extracts it
as data: the generated code initialises the constant from a static image
instead of running its body. Arrays of scalars (and arrays of such arrays)
become constant-initialised immortal blocks; everything else is rebuilt from
a word stream at static initialisation, keeping sharing.

```coq
From Stdlib Require Import List.
From Crane Require Import Extraction Mapping.Std Mapping.NatIntStd.

Module Squares.
Definition table : list nat := List.map (fun n => n * n) (List.seq 0 10).
End Squares.

Crane Bake Squares.table.
Crane Extraction "squares" Squares.
```

`squares.h` declares `table` as
`crane::bake::read<List<uint64_t>>(crane_baked_table_...)`, and
`squares.cpp` ends with the image, one node per row with a comment naming
it.

* The constant must be transparent, outside any functor, module type or
  functor application, and its type must hold only data. Crane refuses a
  function, a type, a proof, a coinductive (lazy or effectful) value, or an
  opaque type without a mapping.
* Put the command after the mappings and options the extraction uses: the
  bake extracts the constant with the settings in effect at the command.
* Crane extracts the constant alone, compiles it with `clang++ -O1` plus
  `Set Crane Bake Flags` and `CRANE_BAKE_FLAGS`, runs it, and records the
  image with the constant, so it survives `Require`. A baked constant is
  never inlined.
* **Stale images.** The bake records every file the compiler read (runtime
  headers, mapping headers, system headers) with its digest, the compiler
  version and `CRANE_BAKE_FLAGS`. An extraction that would emit the image
  checks them and fails with `Crane Bake: the baked image of <c> is stale:
  <file> has changed since it was baked.` Rebuild the file containing the
  `Crane Bake` command. `Crane.Extraction` requires
  `Crane.RuntimeHeaders`, generated with a digest of the runtime headers, so
  under dune a changed runtime header rebuilds every file that loads Crane.
  The check does not re-bake, and does not compare `Set Crane Bake Flags`
  (it is in the document, which the build system sees) or libraries linked
  into the bake (BDE's).

A refused constant is reported as `Crane Bake: <c> is a function, which is
not data.` (or `<c> holds, in a constructor field, ...` for a field). The
type checks pass for every type with a typed or legacy mapping, but the
image must also be able to write the mapped C++ type. It can write
generated inductives and records, `crane::list`, integers, characters,
booleans, enumerations, `float` and `double`, strings (`std::string`,
`bsl::string`), pairs, tuples, optionals, `std::vector`, `std::deque`,
`persistent_array`, `crane::shared_array` and `mpz_class`; so every shipped
mapping except `Mapping.Real` (a `long double`). A type it cannot write
fails when the bake compiles: `crane::bake: a scalar wider than a word ...`
for `long double` or a 128-bit integer, `crane::bake: no way to write a
value of this type` for anything else (`immer` containers, the erased
`crane::obj`).

The image is portable across byte orders but not across data models: it
asserts that the target has the widths of `short`, `int`, `long`,
`long long`, `wchar_t` and `size_t` it was baked with, so cross-compiling a
baked unit is unsupported. Baking costs a compile at `-O1` of the
constant's unit per baked constant, at extraction time. Inductive nodes and
list cells are rebuilt (once, at static initialisation) rather than
constant-initialised; only arrays of scalars are static. The image format is
described in `theories/cpp/crane_bake.h`.

---

## Code generation options

### `Set Crane StdLib`

```coq
Set Crane StdLib "std".   (* default *)
Set Crane StdLib "BDE".
```

Selects the flavour of the names Crane writes itself (`std::shared_ptr` or
`bsl::shared_ptr`, `std::move` or `bsl::move`, ...) and of the BDE build.
It does not load mappings: `Mapping.Std` and `Mapping.BDE` set it when
imported (`#[export] Set Crane StdLib`), so import the mapping flavour you
want and leave this option alone.

### `Set Crane BDE Directory`

```coq
Set Crane BDE Directory "<path>".
```

The BDE installation `Crane Extraction TestCompile` and `Crane Bake` build
against under `StdLib "BDE"`.

### `Set Crane Loopify` / `Crane Loopify`

Turns recursive functions into loops, so deep inputs cannot overflow the C++
stack.

```coq
Set Crane Loopify.             (* all eligible functions; default off *)
Crane Loopify <qualid> ... .   (* these functions *)
Crane NoLoopify <qualid> ... . (* not these *)
Crane Reset Loopify.
Set Crane Loopify Diagnostics. (* report an outcome per recursive function *)
Set Crane Loopify Strict.      (* a function left recursive is an error *)
```

Tail recursion becomes a `while` loop, tail recursion modulo cons a loop
writing through a hole, and other recursion a loop over an explicit heap
stack of frames. A setting for a function of a functor instance, such as
`Crane NoLoopify ZMap.Raw.add` for `ZMap := FMapAVL.Make(Z_as_OT)`, also
applies to every function whose last two path components are the same
(`Raw.add`) when no setting names that function itself.

`CRANE_LOOPIFY_DIAGNOSTICS=1` does the same as `Set Crane Loopify
Diagnostics`. Each line is prefixed with the emitted file:

| Outcome | Meaning |
| --- | --- |
| `tail loop` | a flat `while` |
| `tail-modulo-cons` | a flat `while` writing through a hole |
| `frame stack` | an explicit heap stack: O(depth) heap, O(1) C++ stack |
| `deferred (...)` | left alone; the shape already runs in O(1) stack (a `lazy_`-wrapped cofixpoint body) |
| `DECLINED: ...` | the emitted C++ still calls itself |

The outcome is decided from the emitted code: a transformed body that still
calls itself is a decline, whatever the strategy claimed.
`scripts/loopify-coverage.sh` sweeps the test corpus and diffs the declines
against `tests/loopify-coverage.golden`.

Shapes that still decline: a self-call inside a lambda, a continuation, or a
function passed over the children of a nested inductive (the lambda may run
later, so its call cannot become a frame push); a self-call inside a local
fixpoint or a spliced partner the machine cannot enter (lift the local
fixpoint to a top-level function); a recursive call passing a value-type
receiver.

### `Set Crane Reuse` / `Crane Reuse`

```coq
Set Crane Reuse.               (* default off *)
Crane Reuse <qualid> ... .
Crane NoReuse <qualid> ... .
Crane Reset Reuse.
```

Perceus-style in-place reuse: at a match on an owned recursive value whose
branch rebuilds a constructor of the same type, the matched cell is
rewritten in place when it is uniquely owned, checked at run time. It fires
only under `Set Crane NonAtomicRc` or for a type under
`Set Crane SharedVariant`, never for coinductive types or enums. A
per-function setting overrides the global flag. A loopified recursive
function does not use the match rewrite (exclude it with
`Crane NoLoopify` to get it); under `Reuse` and `NonAtomicRc`, a
tail-modulo-cons loop that owns its input reuses cells itself.

### `Set Crane Arena` / `Crane NoArena`

```coq
Set Crane Arena.               (* default off *)
Crane NoArena <inductive> ... .
```

Makes the allocation of recursive fields check for an open
`crane::arena_scope` and bump-allocate from it. The pointer type and layout
do not change, so arena and heap values mix freely, and a value that
outlives its scope is kept alive by a refcounted keeper. With the flag off,
allocation calls `std::make_shared` (or `crane::make_rc`, or
`bsl::make_shared`) and no arena code is included. `Crane NoArena` keeps the
plain factory for the listed types, for values that outlive the scope.

```cpp
{
  crane::arena_scope _scope;      // a fresh region
  auto t = build_big_tree(input); // recursive fields bump-allocate
  consume(t);
}                                 // region released
```

`crane::arena_use_scope` installs an existing region. Without a scope,
allocations fall back to a per-thread region freed at thread exit.

### `Set Crane NonAtomicRc`

```coq
Set Crane NonAtomicRc.
```

Uses `crane::rc` (non-atomic count in the same allocation as the value)
instead of `std::shared_ptr` for recursive fields, and takes precedence over
`bsl::shared_ptr`. Sound only when values are not shared across threads. A
unit whose program uses a mapping that runs code on several threads
(`<thread>`, `<future>`, `bsl_thread.h`, `bsl_future.h`,
`stm_adapter.h`: `Monads.Thread`, `Monads.Par`, `Monads.STM` and their BDE
flavours) keeps `std::shared_ptr`, with the warning
`crane-non-atomic-rc-concurrent`. Under this option a constructor's factory
takes each field of the inductive's own type as a `crane::child_slot<T>`, so
rebuilding a path in a persistent tree allocates only the nodes on the path.

### `Set Crane SingleThreaded`

```coq
Set Crane SingleThreaded.
```

A promise that the program uses Crane values from one thread at a time: the
runtime's block heap is one global instead of one per thread. Withheld, like
`NonAtomicRc`, from a unit that runs on several threads. With both options
set, immortal blocks use a "sticky" count that is updated without an
immortality test.

### `Set Crane FastVariant`

```coq
Set Crane FastVariant.
```

Stores an inductive's alternatives in `crane::variant` (`crane_variant.h`)
instead of `std::variant`: the same interface, with copies, moves and
destruction as inline switches. Code that matches on an extracted type's
`v()` must then use `crane::holds_alternative`, `crane::get` and
`crane::get_if`. Ignored under BDE.

### `Set Crane SharedVariant`

```coq
Set Crane SharedVariant.
```

Stores a recursive inductive's values as shared blocks
(`crane::shared_variant`, one word per value) and its recursive fields as the
values themselves (`crane::shared_box`). A top-level constant whose type is
not a C++ literal type is initialised through `crane::immortal(...)`: its
blocks are never counted or freed. Ignored under BDE.

### `Set Crane BoxedFields`

```coq
Set Crane BoxedFields.
```

Stores a constructor field whose type is an inductive behind the smart
pointer recursive fields already use (OCaml's representation), so copying or
destroying the outer value stops at the field. A structured binding then
sees the pointer.

### `Set Crane Format Style`

```coq
Set Crane Format Style "None".
```

Crane lays out its output itself, in the LLVM style as clang-format applies
it (two-space indentation, 80 columns, a blank line between definitions,
sorted includes). No external formatter runs. `"None"` keeps the printer's
text as written; any other value (default `"LLVM"`) lays it out.

### Output options

```coq
Set Crane Extraction Output Directory "<dir>".
Set Crane Extraction File Comment "<text>".
```

* **Output Directory**: where files are written, created if missing. Rocq's
  `-output-directory` flag does the same. Without either, Crane writes to
  the current directory and warns (`crane-extraction-default-directory`).
* **File Comment**: a comment at the top of every generated file.

### Optimisation and compatibility options

```coq
Set Crane Extraction Optimize.            (* default on *)
Set Crane Extraction Flag <n>.            (* bitmask of Core simplifications *)
Set Crane Extraction Conservative Types.  (* default off *)
Set Crane Extraction AutoInline.          (* default off *)
Set Crane Extraction TypeExpand.          (* default on *)
Set Crane Extraction AccessOpaque.        (* default on *)
Set Crane Extraction SafeImplicits.       (* default on *)
```

`Optimize` switches the Core simplifications inherited from Rocq's
extraction (inlining, dummy-argument removal, let reduction); `Flag` selects
them individually, `0` being `Unset Crane Extraction Optimize`.
`Conservative Types` keeps dummy lambdas of top-level constants.
`AutoInline` inlines small definitions automatically. `TypeExpand` expands
type abbreviations. `AccessOpaque` extracts the bodies of opaque constants
(with a warning); unset, they are treated as axioms. `SafeImplicits` makes an implicit argument that is still used
an error rather than a warning. These are debugging and compatibility knobs;
the test corpus is validated against the defaults.

---

## Other commands

### `Crane Extraction Inline` / `NoInline`

```coq
Crane Extraction Inline <qualid> ... .
Crane Extraction NoInline <qualid> ... .
Crane Print Extraction Inline.
Crane Reset Extraction Inline.
```

Forces constants to be inlined, or not, at their uses.

### `Crane Extraction Implicit`

```coq
Crane Extraction Implicit <qualid> [ <arg> ... ].
```

Drops the listed arguments (positions from 1, or names) of a constant,
inductive or constructor from the generated signature.

```coq
Crane Extraction Implicit newSTRef [idx].
```

### `Crane Extraction Blacklist`

```coq
Crane Extraction Blacklist <ident> ... .
Crane Print Extraction Blacklist.
Crane Reset Extraction Blacklist.
```

Names Crane must not use for generated files and modules, to avoid
collisions with existing headers.

### `Crane Guard Compare`

```coq
Crane Guard Compare <constant> => <constructor or constant>.
```

Adds an identity short-circuit to a comparison function: when its first two
arguments of the same type are the same value (the same object, or for a
shared variant the same block), it returns the given result at once instead
of walking both. For a structural comparison over large shared values this
turns a deep walk into a pointer test.

```coq
Crane Guard Compare tcompare => Eq.
```

### `Crane Benchmark`

```coq
Crane Benchmark
  <qualid> [As "<label>"], ..., <qualid> [As "<label>"]
On
  <backend> [With "<flags>"], ..., <backend> [With "<flags>"].
```

Compares observationally equivalent definitions, each of type
`unit -> PrimString.string`, across backends (`OCaml`: Rocq's OCaml
extraction and `ocamlopt`; `C++`: Crane and `clang++`) and compiler flags.
Crane builds every combination, runs each once, stops if a build fails or
the outputs differ, and then reports timings with
[hyperfine](https://github.com/sharkdp/hyperfine), which must be installed.

```coq
Crane Benchmark
  baseline As "baseline",
  optimized As "optimized"
On
  C++ With "-O3",
  OCaml With "-O3".
```

---

## Environment variables

Read by the plugin when it runs:

| Variable | Effect |
| --- | --- |
| `CRANE_BAKE_FLAGS` | extra `clang++` flags for `Crane Bake`, recorded with the image |
| `CRANE_LOOPIFY_DIAGNOSTICS=1` | as `Set Crane Loopify Diagnostics` |
| `CRANE_TRACE_MAPPINGS=1` | report discovered typed-mapping heads and resolved descriptors |
| `CRANE_TRACE_ACCESS=1` | print the parameter access summaries |
| `CRANE_CHECK_IR=1` | run every internal consistency check (slower; on in the test suite) |
| `SDKROOT` | the macOS SDK `clang++` is run with |

Developer switches (`CRANE_TRACE_PIPELINE`, `CRANE_TRACE_PASSES`,
`CRANE_PROBE`, `CRANE_RENDER_TWICE`, ...) are listed in
[Compiler-Pipeline.md](Compiler-Pipeline.md#10-checking-tracing-and-layering).

C++ macros the runtime headers read when the generated code is compiled:
`CRANE_STATS` (runtime event counters, `stats.h`), `CRANE_STRICT_ARITY`
(removes `crane::fn`'s implicit conversion between curried and flat argument
groupings, so a crossing the generated code missed does not compile; the
test suite uses it).
