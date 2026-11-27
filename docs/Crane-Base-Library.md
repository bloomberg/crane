# Crane Base Library

Crane ships a library of mappings, effect definitions and C++ runtime headers
in [`theories/`](https://github.com/bloomberg/crane/tree/main/theories), built
as the Rocq library `Crane`.

- `Extraction.v` loads the plugin: `From Crane Require Extraction.`
- `Mapping/` maps Rocq types and operations to C++. Every file there is a
  [typed mapping](Reference-Manual.md#typed-mappings) and activates on
  `Import`.
- `Monads/` defines effects on interaction trees, mapped with the legacy
  commands, and the `ST` monad, whose arrays and references are typed.
- `External/` declares C++ types used through axioms (vectors, string views),
  mapped with the legacy commands.
- `cpp/` and `cpp_bde/` hold the header-only C++ runtime that generated code
  includes.

Activation follows Rocq's imports. `From Crane Require Import Mapping.Std.`
activates the standard mappings; a bare `Require` loads the file without
activating them. A file that imports two mappings of the same type (say
`Mapping.NatIntStd` and `Mapping.NatGMP`) gets an ambiguity error naming
both instances at extraction.

---

## Mappings

The tables give each file's C++ types; the operations listed are mapped to
native C++ arithmetic or library calls instead of being extracted from their
Rocq definitions.

### Choosing a flavour

| Import | Types |
| --- | --- |
| `Mapping.Std` | standard library: `option`, `prod`, strings, primitive integers and floats |
| `Mapping.BDE` | the same with BDE (`bsl::`) types |
| `Mapping.NatIntStd`, `Mapping.NInt`, `Mapping.ZInt` | `nat`, `N`/`positive`, `Z` as machine integers (bounded; for prototyping) |
| `Mapping.NatIntBDE`, `Mapping.NIntBDE`, `Mapping.ZIntBDE` | the same, BDE flavour |
| `Mapping.NatGMP`, `Mapping.NGMP`, `Mapping.ZGMP` | arbitrary precision with GMP's `mpz_class` |
| `Mapping.Real` | axiomatized reals as `long double` |
| `Mapping.AsciiChar` | `ascii` as `char` |
| `Mapping.DequeList` | `list` as `std::deque` |

Without a list mapping, `list` and every other inductive are generated as
C++ types (`List<A>`, a value type holding a `std::variant`).

### `Mapping/Shared.v`

Shared by every flavour; exported by `Std` and `BDE`.

| Rocq | C++ |
| --- | --- |
| `bool` | `bool` |
| `sumbool A B` | `bool` |
| `unit` | `std::monostate` |
| `PrimArray.array A` | `persistent_array<A>` (`persistent_array.h`, copy-on-write) |

Operations: `negb`, `andb`, `orb`; `PrimArray.make`, `get`, `default`,
`set`, `length`, `copy`.

### `Mapping/StdCore.v` and `Mapping/Std.v`

`StdCore` maps everything but strings; `Std` exports `StdCore` and adds the
string mapping. Both set `Crane StdLib "std"`.

| Rocq | C++ |
| --- | --- |
| `option A` | `std::optional<A>` |
| `prod A B` | `std::pair<A, B>` |
| `PrimInt63.int` | `int64_t` holding 0..2^63-1 |
| `PrimFloat.float` | `double` |
| `PrimString.char63` | `int64_t` (`char63` is `int`; `get` reads a byte as 0..255) |
| `PrimString.string` (`Std` only) | `std::string`, with a `std::string_view` read view |

- `fst` and `snd` borrow their component: a `let` binding one out of a pair
  binds it by `const` reference.
- `PrimInt63`: `add`, `sub`, `mul` (wrapping, computed unsigned and masked
  to 63 bits), `div`, `mod` (Rocq's `x / 0 = 0`, `x mod 0 = x`), `eqb`,
  `ltb`, `leb`, `land`, `lor`, `lxor`, `lsl`, `lsr`, `asr`, and the
  primitives `crane_int63.h` implements after Rocq's kernel: `mulc`, `divs`,
  `mods`, `ltsb`, `lesb`, `addc`, `addcarryc`, `subc`, `subcarryc`,
  `diveucl`, `diveucl_21`, `addmuldiv`, `compare`, `compares`, `head0`,
  `tail0`.
- `PrimFloat`: `add`, `sub`, `mul`, `div`, `opp`, `abs`, `sqrt`, `eqb`,
  `ltb`, `leb`, `of_uint63`, `classify`, `compare`, `normfr_mantissa`,
  `frshiftexp`, `ldshiftexp`, `next_up`, `next_down`, each written with
  `<cmath>` in the mapping.
- `PrimString`, each written with `std::string`/`std::string_view` in the
  mapping: `length`, `cat` (cut to `max_length`, as
  in Rocq), `get` (the byte, unsigned), `make` (length clamped to
  `max_length`), `max_length` (16777211), `compare`, `sub`.

A generated function that only reads a string (passes it to `length`, `get`,
`sub`, or to a function that only reads it) takes `std::string_view`; one
that keeps, returns, stores or matches it takes `const std::string&` (or
`std::string` when it owns it); a function returning a string returns
`std::string`. A string literal passed as a view is the view of the literal.

`Mapping/StringView.v` re-exports `Std`, for files that imported it when the
string-view mapping was separate.

### `Mapping/BDE.v`

The `Std` descriptors with BDE spellings. Exports `Shared`; sets
`Crane StdLib "BDE"`.

| Rocq | C++ |
| --- | --- |
| `option A` | `bsl::optional<A>` |
| `prod A B` | `bsl::pair<A, B>` |
| `PrimString.string` | `bsl::string`, with a `bsl::string_view` read view |
| `PrimInt63.int` | `int64_t` (masked as in `Std`) |
| `PrimFloat.float` | `double` |
| `PrimString.char63` | `int64_t` |

The same operations as `Std`. BDE builds compile as C++20, so the BDE runtime
avoids C++23/26 features (`crane::unreachable` instead of
`std::unreachable`, named instead of repeated `_` structured bindings).

### Numbers

| File | Maps | C++ type | Exports |
| --- | --- | --- | --- |
| `NatIntStd.v` | `nat` | `uint64_t` | `Std` |
| `NatIntBDE.v` | `nat` | `unsigned int` | `BDE` |
| `NInt.v` | `positive`, `N` | `unsigned int` | `Std` |
| `NIntBDE.v` | `positive`, `N` | `unsigned int` | `BDE` |
| `ZInt.v` | `Z` | `int64_t` | `NInt`, `NatIntStd` |
| `ZIntBDE.v` | `Z` | `int64_t` | `NIntBDE`, `NatIntBDE` |
| `NatGMP.v` | `nat` | `mpz_class` | `Std` |
| `NGMP.v` | `positive`, `N` | `mpz_class` | `Std` |
| `ZGMP.v` | `Z` | `mpz_class` | `NGMP`, `NatGMP` |

Each type mapping declares its numerals, so a constructor chain is written as
one literal (`UINT64_C(3)` for `nat` under `NatIntStd`). Operations:

- `nat`: `Nat.add`, `mul`, `div`, `modulo`, `double`, `pred`, `sub`, `max`,
  `min`, `eqb`, `ltb`, `leb`, `compare`, `PeanoNat.Nat.eq_dec`, and in the
  machine-integer files `Nat.iter`. The files also declare
  `nat_of_int : int -> nat` and `string_of_nat : nat -> string` (axioms with
  mapped implementations).
- `positive` and `N`: `add`, `sub`, `mul`, `succ`, `pred`, `eqb`, `ltb`,
  `leb`, `compare`, `eq_dec`, `min`, `max`; for `N` also `div`, `modulo`,
  `double`, `succ_double`; `N.of_nat`, `N.to_nat`, `Pos.of_nat`,
  `Pos.to_nat`.
- `Z`: `add`, `sub`, `mul`, `div`, `modulo`, `opp`, `abs`, `succ`, `pred`,
  `eqb`, `ltb`, `leb`, `gtb`, `geb`, `compare`, `eq_dec`, `min`, `max`,
  `of_nat`, `to_nat`, `of_N`, `to_N`, `abs_N`.

The machine-integer mappings are bounded where Rocq's numbers are not:
arithmetic wraps and conversions truncate past the C++ type's range. Use them
only where values provably fit, or use the GMP files (link with
`-lgmpxx -lgmp`). An exact mapping of `nat` to
`boost::multiprecision::cpp_int` is an example in
`tests/regression/typed_mapping_exact_numbers/`, not a shipped file.

### `Mapping/Real.v`

Maps `R` to `Real` (`crane_real.h`, a `long double`). Exports `Std` only: it
does not choose a representation for `Z`, `N` or `positive`. Programs that
use `INR`, `IZR`, `IPR` or `IPR_2` import an integer flavour too
(`From Crane Require Import Mapping.ZInt Mapping.Real.`).

Operations: `R0`, `R1`, `Rplus`, `Rmult`, `Ropp`, `Rinv`, `Rminus`, `Rdiv`,
`Rabs`, `Rsqr`, `Rmax`, `Rmin`, `pow`, `sqrt`, `sin`, `cos`, `tan`, `asin`,
`acos`, `atan`, `PI`, `Rle_dec`, `Rlt_dec`, `Req_EM_T`, `INR`, `IZR`, `IPR`,
`IPR_2`, `Rabst`, `Rrepr`. The constructive real modules
`Rdefinitions.RbaseSymbolsImpl` and `Rdefinitions.RinvImpl` are skipped.

### `Mapping/AsciiChar.v`

Maps `Ascii.ascii` to `char` (as OCaml's `ExtrOcamlString` does), so
comparing two characters is one instruction instead of a conversion through
`N`. The constructor packs eight `bool`s; a match unpacks them. Maps
`Ascii.compare`, `Ascii.eqb` and `Ascii.ascii_dec`. Exports `Shared`, whose
`bool` its constructor and projections are written against.

### `Mapping/DequeList.v`

Opt-in: maps `list A` to `std::deque<A>` instead of the generated
`List<A>`, for programs that index or work at both ends. A deque copies
every element, so it is read by `const` reference, and a match copies the
tail, so a head-tail recursion over a deque is quadratic. Maps `length`,
`app`, `List.map`, `List.rev`, `List.filter`, `List.fold_right`,
`List.fold_left`, `List.forallb`, `List.flat_map`, `List.concat`,
`String.list_ascii_of_string`, `String.string_of_list_ascii`.

---

## Effects

All effects are built on interaction trees (ITrees) and mapped with the
legacy commands (`Crane Extract Monad`, `Crane Extract Inlined Constant`,
`Crane Extract Skip`). Most effect modules share their definitions: a
`*Defs.v` file holds the flavour-independent effect inductive and smart
constructors, and the flavour files (`IO.v` for the standard library,
`IOBDE.v` for BDE) re-export them with C++ mappings.

### ITree modes

Import one of the two (they are exclusive):

```coq
From Crane Require Import Monads.ITree.          (* erased mode, the default *)
From Crane Require Import Monads.ITreeReified.   (* reified mode *)
```

- **Erased** (`Monads/ITree.v`, re-exports `ITreeBase.v`): `itree E R`
  extracts to `R`. `bind` becomes sequential statements, `Ret` the value, and
  events are dispatched by the smart constructors' mappings. Use it when the
  program only runs effects. Provides `itree`, `bind`, `Ret`, `Tau`, `Vis`,
  `trigger`, `hoist`, and the notations `e1 ;; e2` and `x <- c1 ;; c2`.
- **Reified** (`Monads/ITreeReified.v`): `itree E R` extracts to
  `std::shared_ptr<ITree<R>>` (`crane_itree.h`); `bind` is a call, `Ret`,
  `Tau` and `Vis` are constructors, and `observe` can be matched. Use it for
  CoFixpoint servers, interpreters and schedulers that inspect the tree. A
  function named `main` returning an `itree` is extracted as `_main` with a
  wrapper that runs it.

### `Monads/IO.v` / `Monads/IOBDE.v`

Console (`consoleE`): `print`, `print_endline`, `get_line`. Files (`fileE`):
`read`, `write_file`, `append_file`, `file_exists`, `remove_file`. Shared
definitions in `IODefs.v`.

### `Monads/STM.v` / `Monads/STMBDE.v`

Software transactional memory, implemented by `stm_adapter.h` over
`crane-stm/`. `TVar A`, `newTVar`, `readTVar`, `writeTVar`,
`atomically : itree stmE A -> itree ioE A`, `orElse`, `retry`, `check`,
`modifyTVar`, and `getSTM`, `isEmptySTM` over vectors. Shared definitions
in `STMDefs.v`.

### `Monads/Thread.v` / `Monads/ThreadBDE.v`

`thread` (a `std::shared_future<void>` from `std::async`: copyable, joinable
from any copy, the last copy waiting for the thread), `spawn`,
`join`, `sleep` (milliseconds), `runConc`. `concE` composes `threadE` with
`consoleE`. Shared definitions in `ThreadDefs.v`.

### `Monads/Par.v` / `Monads/ParBDE.v`

Futures: `future B`, `async`, `get_thread` (`.get()`), `runPar`. Shared
definitions in `ParDefs.v`.

### Clock, directories, environment, paths, temporary files

| Module | Operations |
| --- | --- |
| `Clock.v` / `ClockBDE.v` | `steady_now`, `system_now`, `now` (milliseconds as `int`) |
| `Dir.v` / `DirBDE.v` | `create_directory`, `remove_directory`, `list_directory`, `current_path` |
| `Env.v` / `EnvBDE.v` | `get_env`, `set_env`, `unset_env` |
| `Path.v` / `PathBDE.v` | `canonical`, `relative`, `absolute`, `is_directory`, `is_regular_file` |
| `TempFile.v` / `TempFileBDE.v` | `create_temp_file`, `create_temp_dir` |

Each has a `*Defs.v` file with the shared definitions.

### `Monads/ST.v`

A Haskell-style `ST` monad for local mutable state, distinct from STM.
`STFacts.v`, `STSpec.v` and `STArrayFacts.v` hold the
reasoning principles (not extracted). Require it qualified,
`From Crane Require Monads.ST.`, and write `ST.new_ref`, `ST.ref A`: importing
it would shadow ITree's `interp`. Its mapping instances are global, so a
qualified Require is enough.

A program is written against an abstract `ST.Refs` (the type of references
and of arrays, nothing more) and `ST.run` takes it polymorphic in it,
`forall R : ST.Refs, itree (ST.Event R V +' E) A`: inside the program a
reference is of an abstract type, so it cannot be inspected, forged or
returned from the run. `ST.run` interprets the program in a model where a
reference is a location; extraction instantiates it at `ST.cpp_refs` and runs
it with `ST.run_cpp`, the identity. Values of different types share the store
through codes, `V : nat -> Type`; a `Code V A` instance gives `A` its code
(`code_const` does where every value has one type), so no operation takes
one.

The array and reference types are typed mappings:

| Rocq | C++ | Views |
| --- | --- | --- |
| `ST.ref A` | `std::shared_ptr<A>` | `const A*` (read), `A*` (write), borrow-only |
| `ST.array A` | `std::shared_ptr<crane::array_storage<A>>` | `std::span<const A>` (read), `std::span<A>` (write), borrow-only |

| Operation | C++ | Contract |
| --- | --- | --- |
| `ST.new_ref v` | `std::make_shared<A>(v)` | takes `v`, fresh identity |
| `ST.read_ref r` | `*r` | reads `r` |
| `ST.write_ref r a` | `*r = a` | writes `r`, takes `a` |
| `ST.new_array n def`, `ST.array_of_list elems` | a new `array_storage` | fresh identity |
| `ST.read_array arr i` | `arr[i]` | reads `arr` |
| `ST.write_array arr i v` | `arr[i] = v` | writes `arr`, takes `v` |
| `ST.swap_array arr i j` | `std::swap(arr[i], arr[j])` | writes `arr` |
| `ST.array_to_list arr` | the elements as a list | reads `arr` |

So a helper that reads and writes one array extracts as its own function
taking `std::span<A>` (or `const std::shared_ptr<...>&` where it keeps the
array) instead of being inlined into its caller. A reference used only
through its views where it is created is a local (`A x = v;`).
`crane::array_storage<bool>` stores addressable `bool`s, so the span mapping
holds for every element type. Arrays and references are reference counted;
cycles through them are not collected.

Recursive `ST` code is an ordinary `Fixpoint`; one that is not structural
recursion recurses on an accessibility proof, which is erased
(`tests/monadic/st_quicksort`).

### `Monads/Global.v`, `Monads/Error.v`

A global-state event family, its references mapped as ST references
(`std::shared_ptr<A>`), with its reasoning facts in
`GlobalFacts.v`, and `Err`, the error type of runtime errors raised
through ITree's exception events. Require `Global` qualified as `ST`
(`Global.new_ref`, `{H : Global.RefClass T}`).

---

## External types

### `External/Vector.v` / `External/VectorBDE.v`

`vector A` as `std::vector<A>` (or `bsl::vector`): `emptyVec`, `get`,
`push`, `pop`, `size`, `isEmpty`, `assign`. Shared definitions in
`VectorDefs.v`.

### `External/StringViewStd.v` / `External/StringViewBDE.v`

An axiomatized `string_view` type (`std::basic_string_view<char>`) with
`empty`, `empty_sv`, `sv_eq`, `length`, `substr`, `sv_get` (bounds-checked,
returns the byte as `0..255`, `0` out of range), `sv_at` (throws out of
range), `sv_of_string`, `contains`, and axioms relating them
(`StringViewDefs.v`). For strings used as values, prefer `Mapping.Std`,
whose `PrimString.string` mapping already passes read-only strings as
`std::string_view`.

---

## C++ runtime headers

Generated code includes these by name, so `theories/cpp` (or
`theories/cpp_bde` for BDE builds) must be on the include path
(`-I<crane>/theories/cpp`). They are header-only.

| Header | Contents |
| --- | --- |
| `small_vector.h` | `crane::small_vector<T, N>`, a stack with inline storage for the worklists of iterative destructors and the frame stacks of loopified functions |
| `fn.h`, `crane_fn.h` | `crane::fn<R(A...)>`, a closure as a shared immutable value; storing a callable into an erased field; ITree's `rec` and `call` in erased mode |
| `obj.h` | `crane::obj`, an erased value, shared rather than copied; `crane::writable(v).ref()`, a temporary an in-place argument binds; `crane::unreachable()` for builds before C++23; `crane::template_argument_t<T, I>`, used by view conversions |
| `shared_block.h` | the header of every shared runtime block: count and destroy function; immortal and sticky counts |
| `shared_variant.h`, `word.h` | `crane::shared_variant` (`Set Crane SharedVariant`) |
| `crane_variant.h` | `crane::variant` (`Set Crane FastVariant`) |
| `field.h` | `crane::field<T>` (`Set Crane BoxedFields`) |
| `rc.h` | `crane::rc<T>`, single-allocation non-atomic counting (`Set Crane NonAtomicRc`) |
| `pool.h` | the per-thread (or, under `SingleThreaded`, global) heap of small blocks |
| `lazy.h` | `crane::lazy<T>`, a memoising thunk for coinductive values |
| `arena.h` | scoped arenas (`Set Crane Arena`) |
| `persistent_array.h` | the copy-on-write array `PrimArray` maps to |
| `shared_array.h` | `crane::shared_array<T>`, an immutable shared array; static blocks for baked constants |
| `crane_st.h` | `crane::array_storage<T>`, one addressable element each, and the ST array helpers |
| `crane_int63.h` | the `PrimInt63` primitives without an operator (carrying products and two-word divisions loop) |
| `conslist.h` | `crane::list<T>`, a persistent cons list, available as a container mapping |
| `aggregate.h` | a struct's fields as a pack (C++26) or counted bindings (C++20) |
| `crane_bake.h` | the `Crane Bake` writer and reader |
| `crane_itree.h` | reified interaction trees |
| `crane_real.h` | the `Real` class |
| `stm_adapter.h`, `crane-stm/` | the STM API and its implementation |
| `stats.h`, `count_rc.h` | measurement: event counters (`CRANE_STATS`), reference-count traffic (`CRANE_COUNT_RC=1` at extraction) |
