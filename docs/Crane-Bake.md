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

An image is a stream of 64-bit words plus a table of static blocks. The
serialiser is generic over the generated types. It uses C++26 structured
binding packs to read a struct's fields, so no per-type code is generated;
each type gets its own template instantiation.

- A scalar (integer, char, bool, enum, floating point) is one word. A
  `std::string` is its length and then its bytes, eight to a word. Pairs,
  tuples and `std::optional` (presence word first) are their components. An
  empty type is nothing.
- A generated inductive, record or flat struct starts with a sharing word:
  `k+1` means the k-th node already read of that type, and `0` means a new node
  (constructor index, then fields). An enum is a new node with its index, so
  an enum and a nullary-constructor variant read each other.
  `std::shared_ptr`/`crane::shared_box`/`crane::rc` fields are transparent;
  the sharing lives at the node level. When reading, a pointer to a node
  already read is the same pointer again.
- `crane::list`: cells `1 head`, ended by `0` (nil) or `k+2` (shared suffix).
- `crane::shared_array<E>`: `0` empty, `1 n elems` heap, `k+3` shared, or
  `2 block code` for a static block. A static block is used when `E` is a
  spellable scalar or, recursively, such an array. The block is
  `crane::shared_array<E>::fixed<N>`, `constinit`, `[[clang::no_destroy]]`,
  with its count at `block_detail::immortal`. `code` encodes `E`, and reading
  checks it.

The format does not depend on byte order: a word is written as the number it
is (a C++ literal), a string's bytes are packed by shifts, a float is its
IEEE bits as an integer. `crane_bake.h` asserts what it does assume (8-bit
bytes, IEEE `float`/`double`, a length fits a word), and each image starts
with `static_assert(crane::bake::data_model == ...)`: the widths of `short`,
`int`, `long`, `long long`, `wchar_t` and `size_t` on the bake host, which
the target must share (a `long` written on LP64 and read on LLP64 would be
truncated). Cross-compiling a baked unit is otherwise unsupported.

The driver lays the image out itself (`writer::declaration`): a declaration
on one line if it fits in 80 columns, else broken after the brace with the
elements filled into lines indented four columns, as clang-format writes a
long initialiser. It is not handed to `Emit.Layout`, which gives every
element of a braced list too long for one line a line of its own (90,002
lines for `bake_long_list`'s stream). Routing it through CppIR would mean
the driver emitting a structured image for OCaml to rebuild as declarations
(`constinit`, `[[clang::no_destroy]]` and `shared_array::fixed<N>`, none of
which CppIR spells) for the same text.

Reading happens once, at static initialisation. Every block it allocates is
made immortal (`crane::make_immortal`). Sharing is kept: the
value comes back as the DAG it was (address-based hash-consing on write).

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
- **`crane::obj` / erased values and persistent arrays** have no hook either.
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
