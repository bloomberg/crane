# Crane Bake: constants computed at extraction time

`Crane Bake c1 c2 ...` computes each closed constant once, when the command
runs, and extracts it as data: the generated code initialises the constant
from a static image instead of running its body at startup.

```coq
Crane Bake JSON.json_srules.          (* after the mapping and option settings *)
Crane Separate Extraction lex_json.   (* json_srules is read from its image *)
```

## Why not constexpr, vm_compute or a literal

- C++ `constexpr`/`consteval` cannot build heap structures that survive into
  a constant (clang 22 / libc++ 22): no allocation outlives constant
  evaluation.
- Rocq `vm_compute` of the ParseALot DFA builder does not finish (opaque
  `Poslt_wf`, `Program Fixpoint` merge; 14 GB).
- Emitting the value as code (23K `push_front` calls) takes more than 20
  minutes to compile at -O3.

Running the generated C++ once and emitting the value as data does work.

## How it runs

1. **Check** (`src/driver/bake.ml`, `check`). The constant must be a
   transparent constant outside any functor or module type, and its type must
   hold only data: no function, type, proof (at the top), coinductive (lazy or
   effectful, `itree` included) or opaque axiom type unless it is mapped (a
   typed `TypeMapping` or a legacy custom extraction) or primitive. The check
   runs before any extraction, so it discovers the typed mappings itself
   (`Mapping_discovery.discover`). The walk reduces the type, then
   instantiates each constructor's parameters and checks every non-`Prop`
   field, recursively. A refusal is a `Crane Bake: <c> is a function, which is
   not data.` error (`<c> holds, in a constructor field, ...` for a field).
2. **Bake** (`bake_one`). Inside `Vernacstate.System.protect`, so the
   extraction leaves no trace in the summary or the library, Crane extracts
   `c` on its own into a temporary directory. A constant at a library's top
   level is extracted one file per library (`separate_extraction`, the mode a
   large program such as ParseALot is known to compile in). A constant inside a
   module is extracted into one file (`full_extraction`), because one file per
   library would make it a Meyers-singleton accessor that nothing calls. With
   `Table.bake_root = c`, the constant's initialiser becomes
   `crane::bake::root(<body>)` and its declaration `[[gnu::used]]`
   (`Cpp_state.read_by_a_function`), so it runs at static initialisation.
   Crane links the unit with a driver whose `main` is `crane::bake::main`
   (via `Toolchain.compile_cpp`, `-O1`, plus `Set Crane Bake Flags` and
   `CRANE_BAKE_FLAGS`) and runs it through `Subprocess.capture`. The driver
   writes the image as C++, and Crane records it with the constant
   (`Table.record_baked`, a libobject, so it survives `Require`). A baked
   constant is never inlined (`add_inline_entries false`).
3. **Use**. Lowering (`Functions.baked_initialiser`, on both the definition
   and the header specification path) still generates the body, so the unit
   plans and includes what it would. It then initialises the constant with
   `crane::bake::read<T>(<symbol>)` (CppIR `Baked_value`), `T` its declared
   type. A proxy that converts to the declared type
   (`crane::bake::value{<symbol>}`) is left for a declaration whose type is
   `auto`: copy-initialising a `std::optional<U>` from it picks optional's
   converting constructor, which reads the image as a bare `U`.
   `print_structure_to_file` declares the image `extern` in the header (after
   `#include "crane_bake.h"`, ahead of the namespace) and appends the image
   text, as the driver wrote it, to the implementation file.

## The image (`theories/cpp/crane_bake.h`)

An image is a stream of 64-bit words, a text (the bytes of its strings) and
a table of static blocks. The stream is a table of nodes, then the value.
The serialiser is generic over the generated types. It reads a struct's
fields through `aggregate.h`: C++26 structured binding packs, or under C++20
(a BDE build) a counted binding of up to 32 fields; so no per-type code is
generated, and each type gets its own template instantiation.

- A **node** is a value of a generated inductive with a constructor that has
  fields, or a `crane::list` cell. Each is written once, as one row: its
  constructor's index, then its fields, a node among them as its number.
  Nodes are numbered in the order they are written, after the nodes they
  hold, so a row only names rows above it: sharing is kept (the value comes
  back as the DAG it was, address-based identity on write), and reading is
  one loop front to back, with no recursion and no stack, however deep the
  value (`bake_long_list`, 30000 cells; a left spine in
  `bake_mapped_values`). A constructor without fields is one row for all
  its uses. Rows come in runs of one type: the type's number (its place,
  from 1, in the order `detail::walk_types` meets the node types in the
  value's type, which writer and reader both run) and the run's length; `0`
  ends the table. A `crane::list` cell is `1 head tail`, nil `0`.
  Shared-pointer (`std::shared_ptr`, `bsl::shared_ptr`)/`crane::shared_box`/
  `crane::rc`/`crane::field_box`/`crane::box` (a list's `Boxed Element`)
  fields (`detail::handle`) are transparent;
  a counted pointer to a node is one pointer per node again when read.
- A scalar (integer, char, bool, enum, `float`, `double`) is one word, as is
  a constructor of an inductive none of whose constructors has a field, so
  an enum and a nullary-constructor variant read each other; a wider scalar
  (`long double`, a 128-bit integer) is a compile error. A string
  (`std::string`, `bsl::string`: a `traits_type`, an allocator and a
  constructor from pointer and length) is its length; its bytes are in the
  text, in the order strings are written. Pairs (`first_type`/
  `second_type`), tuples, records and flat structs, and optionals
  (`has_value`, presence word first) are their components. A sequence
  container (`std::vector`, `std::deque`: an allocator and `push_back`) and
  a `persistent_array` (its default element after the length) are their
  length and elements. A number with a text form (`mpz_class`:
  `get_str(16)` and a constructor from a string and a base) is its base-16
  text. An empty type is nothing. These hooks are structural, so the C++
  type of every shipped typed mapping (`Mapping/Std.v`, `BDE.v`,
  `DequeList.v`, the GMP mappings) has one; `Real` (`Mapping/Real.v`, a
  private `long double`) does not.
- `crane::shared_array<E>`: `0` empty, `1 n elems` heap, `k+3` shared, or
  `2 block code` for a static block. A static block is used when `E` is a
  spellable scalar or, recursively, such an array. The block is
  `crane::shared_array<E>::fixed<N>`, `constinit`, `[[clang::no_destroy]]`,
  with its count at `block_detail::immortal`, its elements literals. `code`
  encodes `E`, and reading checks it.

The format does not depend on byte order: a word is written as the number it
is (a C++ literal), a float is its IEEE bits as an integer. `crane_bake.h`
asserts what it does assume (8-bit bytes, IEEE `float`/`double`, a length
fits a word), and each image starts with
`static_assert(crane::bake::data_model == ...)`: the widths of `short`,
`int`, `long`, `long long`, `wchar_t` and `size_t` on the bake host, which
the target must share (a `long` written on LP64 and read on LLP64 would be
truncated). Cross-compiling a baked unit is otherwise unsupported.

### Layout

The driver lays the image out itself (`writer::cpp`), for a reader: the
text as C++ string literals, the words in decimal, one row to a line, each
with a comment that spells it, aligned after it (above it, broken after
commas, when it does not fit in 80 columns):

```cpp
constinit const std::uint64_t crane_baked_entries_a4d00e69f151_words[] = {
    2, 3,              // BakedConstants::tree: #0 to #2
    0,                 // #0 Leaf
    1, 0, 1, 0,        // #1 Node{l = #0, x = 1, r = #0}
    1, 1, 2, 1,        // #2 Node{l = #1, x = 2, r = #1}
    1, 3,              // List<BakedConstants::entry>: #3 to #5
    0,                 // #3 Nil
    // #4 Cons{a = entry{name = "", weight = nullopt, label = #0}, l = #3}
    1, 0, 0, 0, 3,
    // #5 Cons{a = entry{name = "first", weight = 7, label = #2}, l = #4}
    1, 5, 1, 7, 2, 4,
    0,                 // end of the nodes
    5,                 // the value: #5
};
```

A comment names a node by its number (`#4`), a constructor and its fields
by their C++ names, a scoped enumerator by its name, a string or char as a
literal, a float by its shortest decimal, a static block by its name (`b2`
for `<prefix>_b2`). The text holds `"first"`; a static block's elements are
decimal literals of its element type. The text is a table of character
arrays (`<prefix>text0`, `<prefix>text1`, ...) of at most 65535 bytes each,
the longest string literal C++ compilers must support
(`-Woverlength-strings`), a string split across two where it falls on a cut,
and long strings are split into literals that fit a line. A `?` after a `?`
is written `\?`, so no literal spells a trigraph.
Names come from the compiler: a type's from `__PRETTY_FUNCTION__`, a
struct's fields from clang's `__builtin_dump_struct` (`_0`, `_1`, ...
without it). Past `writer::annotated_rows` (1000) rows, rows and run
headers are filled into lines bare (`bake_long_list`;
`bake_alternating_types_quadratic`, where every run is one row long). The
reader's per-type tables grow as vectors do, so reading alternating types
stays linear. The image is not handed to `Emit.Layout`,
which gives every element of a braced list too long for one line a line of
its own. Routing it through CppIR would mean the driver emitting a
structured image for OCaml to rebuild as declarations (`constinit`,
`[[clang::no_destroy]]` and `shared_array::fixed<N>`, none of which CppIR
spells) for the same text.

Reading happens once, at static initialisation. Every block it allocates is
made immortal (`crane::make_immortal`), node by node, bottom up.

Other forms were measured and rejected (2026-11, clang 22). The value as
constructor calls compiles in 5.9 s at -O3 for a 1000-cell list (0.6 s as
words) and is about 140 bytes of code per cell against 24 of data; past a
few hundred cells a nested expression hits the expression nesting limit, and
it is the startup construction baking exists to avoid. Typed rows with
designated initialisers (`{.ctor = 1, .a = true, .l = 0}`) cost the same as
words to compile, but each image would declare row structs and every hook
(optional, string, sequence, `mpz_class`) would need a constant form; the
reader cannot name the row types without spelling the user's types, which
the driver only knows by `__PRETTY_FUNCTION__`. Static reflection is not in
clang 22 (`-freflection` is unknown), and `#embed` makes the data less
readable, not more.

### Immortal representation

A static block starts at `block_detail::born_immortal`, which is the value
`count::make_immortal` stores: `immortal` (`~0`, never changed), or `sticky`
(half the range, plain increments) under NonAtomicRc + SingleThreaded, the
`tm-immortal` scheme. Its `drop` is never called. `shared_array::fixed` is
the only static-block constructor. Under SharedVariant the global's
initialiser is also wrapped in `crane::immortal(...)`, which does nothing to
the `crane::bake::value` proxy. The reader marks the decoded value itself
(`crane::make_immortal`), which reaches lists and arrays too.

## Runtime additions (kept minimal for the merge)

- `shared_array.h`: `value_type`, `fixed<N>` (static block),
  `of_static(fixed&)` (constexpr), `adopt_static(const void*)`, and constexpr
  default/move constructors and destructor.
- `shared_block.h`: `block_detail::born_immortal`.
- `persistent_array.h` (both flavours): `ref(i)`, an element in place. The
  writer knows a node by its address, so it walks every container by
  reference; `get` returns a copy.
- `crane_bake.h`: new.

## Not done (follow-ups)

- **Constinit nodes for inductives and lists.** `shared_variant` stores a
  nullary constructor as an odd integer in a pointer, and `shared_box` stores
  its word in a `uintptr_t`. Neither is allowed in a constant expression, so
  inductive nodes and `crane::list` cells are rebuilt at startup (flat array
  plus decoder). For ParseALot that covers the regexes and the rule list, a
  few hundred nodes. The DFA tables are static blocks. A constinit form would
  need `shared_box` storage that can hold a pointer at compile time, and a
  sentinel object instead of odd tags.
- **immer containers** (`immer::map`, `flex_vector`) have no hook. The plan
  is to write them as flat arrays of entries and rebuild on first use.
- **`crane::obj` / erased values** have no hook either.
  The C++ `static_assert` reports them at bake time as "no way to write a
  value of this type".
- Heap `shared_array`s of non-scalar elements (`shared_array<Regex>`) are
  rebuilt at startup, not static.
- Crane initialises every global of every linked unit at startup. A hoisted
  constant that is *not* baked is therefore built by every program that links
  its unit: the ParseALot runners link all three lexers, so hoisting alone
  costs each runner the other two lexers' DFAs (+45..+106% on tiny inputs).
  Baking turns that into a cheap decode.
- Baking ParseALot makes extraction 8.5 s -> 113 s: three sub-extractions,
  plus `-O1` compiles of each lexer's closure.
- The bake extracts `c` in single-file mode while the user's extraction may be
  separate. The image is structural (constructor indices and fields in order),
  so the two only have to agree on constructor order and on which fields are
  erased, which they do for the same Rocq environment.
- Baking runs when the command runs, so the options it sees (mappings,
  `SharedVariant`) are the ones set before it, not those at extraction time.
  The format is representation independent apart from the static blocks'
  element types, which reading checks.
