# Crane Base Library

Crane comes with a base library of mappings, and types for monadic effects. The library can be found [here](https://github.com/bloomberg/crane/tree/main/theories).

**Architecture note:** Most effect modules follow a shared-definitions pattern. A `*Defs.v` file contains the flavor-independent effect inductives and smart constructors, while flavor-specific files (e.g., `IO.v` for standard library, `IOBDE.v` for BDE) re-export the definitions and add C++ extraction mappings.

---

## Core

### `Extraction.v`

Declares the Crane ML module that provides the extraction plugin.

---

## Mappings

### `Mapping/Shared.v`

Defines common extraction mappings for boolean and basic types shared across library variants.

- **`bool`** — Extracted to C++ `bool` with `true`/`false` constructors
- **`sumbool`** — Extracted to C++ `bool`
- **`negb`, `andb`, `orb`** — Boolean operations (`!`, `&&`, `||`)
- **`void`** — Unit type for effects (with constructor `ghost`)
- **`PrimArray.array`** — Persistent copy-on-write arrays (`persistent_array<T>`)
- **`PrimArray.make`, `get`, `set`, `length`, `copy`** — Array operations

### `Mapping/Std.v`

Provides extraction mappings from Rocq types to C++ standard library types.

Imports and re-exports `Mapping/Shared.v`.

**Type mappings:**
- **`option`** → `std::optional<T>`
- **`prod`** → `std::pair<T, U>`
- **`fst`, `snd`** → `.first`, `.second`
- **`PrimString.char63`** → `char`
- **`PrimString.string`** → `std::string`
- **`PrimInt63.int`** → `int64_t` (with 63-bit masking for arithmetic operations)
- **`PrimFloat.float`** → `double`

### `Mapping/BDE.v`

Provides extraction mappings from Rocq types to Bloomberg's BDE library types.

Imports and re-exports `Mapping/Shared.v`.

**Type mappings:**
- **`option`** → `bsl::optional<T>`
- **`prod`** → `bsl::pair<T, U>`
- **`fst`, `snd`** → `.first`, `.second`
- **`PrimString.char63`** → `char`
- **`PrimString.string`** → `std::string` (via `bsl_string.h`)
- **`PrimInt63.int`** → `int64_t` (via `bsl_cstdint.h`, no masking)
- **`PrimFloat.float`** → `double`

### `Mapping/NatIntStd.v`

Maps Rocq's `nat` type to `unsigned int` with std library operations. Uses numeral folding (`Crane Extract Numeral nat => "%nu"`) to compile Peano chains into unsigned integer literals.

Imports and re-exports `Mapping/Std.v`.

**Warning**: This mapping is unsafe for serious use. `nat` is infinite while `unsigned int` is bounded; use for testing and prototyping only.

**Additional functions:**
- **`nat_of_int : int -> nat`** — Convert int63 to nat (with axioms)
- **`string_of_nat : nat -> string`** — Convert nat to string
- Defines literal constants `zero` through `one_hundred_fifty` as nat values

### `Mapping/NatIntBDE.v`

Maps Rocq's `nat` type to `unsigned int` with BDE library operations.

Imports and re-exports `Mapping/BDE.v`.

Same structure and warnings as `NatIntStd.v`, but uses BDE library functions (`bsl::max`, `bsl::min`, etc.).

### `Mapping/NInt.v`

Maps Rocq's `N` (binary natural numbers) and `positive` to `unsigned int` with native C++ arithmetic. Provides all `N` and `Pos` operations (add, sub, mul, div, comparisons, etc.).

Imports and re-exports `Mapping/Std.v`.

### `Mapping/NIntBDE.v`

BDE variant of `NInt.v`. Maps `N` and `positive` to `unsigned int` using BDE library functions.

Imports and re-exports `Mapping/BDE.v`.

### `Mapping/ZInt.v`

Maps Rocq's `Z` (binary integers) to `int64_t` with native C++ arithmetic. Uses numeral folding (`Crane Extract Numeral Z => "INT64_C(%n)"`) for large integer literals.

Imports and re-exports `Mapping/NInt.v`.

### `Mapping/ZIntBDE.v`

BDE variant of `ZInt.v`. Maps `Z` to `int64_t` using BDE library functions.

Imports and re-exports `Mapping/NIntBDE.v`.

### `Mapping/NatGMP.v`

Maps Rocq's `nat` to GMP arbitrary-precision integers (`mpz_class`). Useful when `unsigned int` overflow is a concern.

### `Mapping/NGMP.v`

Maps Rocq's `N` to GMP arbitrary-precision integers (`mpz_class`).

### `Mapping/ZGMP.v`

Maps Rocq's `Z` to GMP arbitrary-precision integers (`mpz_class`).

### `Mapping/Real.v`

Maps Rocq's `R` (axiomatized reals) to a C++ `Real` class wrapping `long double` (defined in `crane_real.h`).

Imports and re-exports `Mapping/ZInt.v`.

**Mapped operations:**
- Core field: `R0`, `R1`, `Rplus`, `Rmult`, `Ropp`, `Rinv`, `Rminus`, `Rdiv`
- Utility: `Rabs`, `Rsqr`, `Rmax`, `Rmin`
- Power/sqrt: `pow`, `sqrt`
- Trigonometry: `sin`, `cos`, `tan`, `asin`, `acos`, `atan`, `PI`
- Decisions: `Rle_dec`, `Rlt_dec`, `Req_EM_T`
- Coercions: `INR`, `IZR`, `IPR`

---

## Effect Definitions

All effect modules are built on interaction trees (ITrees). Each effect defines an inductive type representing its operations and smart constructors for invoking them.

Crane provides two ITree extraction modes. Use **erased mode** (the default) when your program simply runs effects — IO, STM, threads, etc. — and you never need to inspect the tree structure itself. This produces the most natural C++: monadic binds become sequential statements, and the ITree wrapper disappears entirely. Use **reified mode** when your Rocq code pattern-matches on `observe`, defines CoFixpoint-based servers or interpreters, or otherwise needs to traverse the ITree as a data structure. In reified mode the tree is preserved as a `std::shared_ptr<ITree<R>>` value that can be inspected, transformed, and eventually executed.

To select a mode, import one of the two modules (they are mutually exclusive):

```coq
From Crane Require Import Monads.ITree.          (* erased mode — default *)
From Crane Require Import Monads.ITreeReified.    (* reified mode *)
```

### `Monads/ITree.v` (Erased mode)

The default ITree extraction mode. `itree E R` extracts to just `R` — the monadic wrapper is completely erased. `bind` becomes sequential statements and `Ret` disappears. Effect events are dispatched via inline customs on the smart constructors.

Re-exports `ITreeBase.v` (shared library erasure directives).

- **`itree (E : Type → Type) (R : Type) : Type`** — Coinductive interaction tree
- **`bind`** — Monadic bind (erased to sequential statements)
- **`Ret`**, **`Tau`**, **`Vis`** — Constructors (erased in this mode)
- **`trigger`** — Trigger an effect
- **`hoist`** — Transform effect types in a tree

Supports monadic notation: `e1 ;; e2` for sequencing and `x <- c1 ;; c2` for binding.

### `Monads/ITreeReified.v` (Reified mode)

Alternative ITree extraction mode for programs that need to observe or traverse ITree structure — CoFixpoint servers, interpreters that pattern-match on `observe`, schedulers, etc.

Import this module instead of `Monads.ITree`.

- **`itree E R`** extracts to `std::shared_ptr<ITree<R>>`
- **`bind`** extracts to actual function calls (not sequential statements)
- **`Ret`/`Tau`/`Vis`** extract to constructors (not erased)
- **`observe`** extracts to method call for pattern matching on `Ret`/`Tau`/`Vis`
- Functions named `main` returning `itree E R` are extracted as `_main` with an automatic wrapper that calls `->run()`

### `Monads/IO.v` / `Monads/IOBDE.v`

IO effects for console and file operations. Shared definitions are in `IODefs.v`.

**Console effects (`consoleE`):**
- **`print (s : string)`** — Print string without newline
- **`print_endline (s : string)`** — Print string with newline
- **`get_line`** — Read line from standard input

**File effects (`fileE`):**
- **`read (path : string)`** — Read contents of a file
- **`write_file (path content : string)`** — Write content to a file
- **`append_file (path content : string)`** — Append content to a file
- **`file_exists (path : string)`** — Check if a file exists
- **`remove_file (path : string)`** — Remove a file

### `Monads/STM.v` / `Monads/STMBDE.v`

Software Transactional Memory effects. Shared definitions are in `STMDefs.v`. Both flavors use `stm_adapter.h` for the C++ implementation, backed by `crane-stm/`.

- **`TVar (A : Type) : Type`** — Transactional variable (axiom)
- **`newTVar {A} (a : A)`** — Create new transactional variable
- **`readTVar {A} (v : TVar A)`** — Read value from transactional variable
- **`writeTVar {A} (v : TVar A) (a : A)`** — Write value to transactional variable
- **`atomically {A} (t : itree stmE A) : itree ioE A`** — Execute STM transaction atomically
- **`orElse {A} (l r : itree stmE A) : itree stmE A`** — Alternative transaction
- **`retry {A}`** — Retry the current transaction
- **`check (b : bool)`** — Assert condition or retry
- **`getSTM {A} (v : vector A) (i : int)`** — Transactional vector access
- **`isEmptySTM {A} (v : vector A)`** — Transactional vector empty check
- **`modifyTVar {A} (a : TVar A) (f : A → A)`** — Atomically modify a variable

### `Monads/Thread.v` / `Monads/ThreadBDE.v`

Thread-based concurrency effects. Shared definitions are in `ThreadDefs.v`.

- **`thread : Type`** — Thread handle (axiom)
- **`spawn {A B} (f : A → B) (a : A)`** — Create and start a new thread (axiom)
- **`join (t : thread)`** — Wait for thread to complete
- **`sleep (d : int)`** — Sleep for milliseconds
- **`runConc {A} (c : itree concE A) : A`** — Execute a concurrent computation

The `concE` effect composes `threadE` (join, sleep) with `consoleE` (print operations).

### `Monads/Par.v` / `Monads/ParBDE.v`

Parallel computation effects using futures. Shared definitions are in `ParDefs.v`.

- **`future (B : Type) : Type`** — Future handle for async result (axiom)
- **`async {A B} (f : A → B) (a : A)`** — Spawn async task, returns `future B`
- **`get_thread {B} (t : future B)`** — Wait for task result (extracts to `.get()`)
- **`runPar {A} (c : itree parE A) : A`** — Execute a parallel computation

### `Monads/Clock.v` / `Monads/ClockBDE.v`

Clock/time effects. Shared definitions are in `ClockDefs.v`. All timestamps are `int` (int63) representing milliseconds.

- **`steady_now`** — Monotonic clock time
- **`system_now`** — Wall-clock time
- **`now`** — Alias for `system_now`

### `Monads/Dir.v` / `Monads/DirBDE.v`

Directory operations. Shared definitions are in `DirDefs.v`.

- **`create_directory (path : string) : bool`** — Create a directory
- **`remove_directory (path : string) : bool`** — Remove a directory
- **`list_directory (path : string) : list string`** — List directory contents
- **`current_path : string`** — Get current working directory

### `Monads/Env.v` / `Monads/EnvBDE.v`

Environment variable operations. Shared definitions are in `EnvDefs.v`.

- **`get_env (name : string) : option string`** — Get environment variable
- **`set_env (name value : string)`** — Set environment variable (POSIX `setenv`)
- **`unset_env (name : string)`** — Unset environment variable (POSIX `unsetenv`)

### `Monads/Path.v` / `Monads/PathBDE.v`

Filesystem path operations. Shared definitions are in `PathDefs.v`.

- **`canonical (path : string) : string`** — Canonicalize path
- **`relative (path : string) : string`** — Make path relative
- **`absolute (path : string) : string`** — Make path absolute
- **`is_directory (path : string) : bool`** — Check if path is a directory
- **`is_regular_file (path : string) : bool`** — Check if path is a regular file

### `Monads/TempFile.v` / `Monads/TempFileBDE.v`

Temporary file/directory creation. Shared definitions are in `TempFileDefs.v`.

- **`create_temp_file (prefix : string) : string`** — Create a temporary file, returns path
- **`create_temp_dir (prefix : string) : string`** — Create a temporary directory, returns path

---

## External Types

### `External/Vector.v` / `External/VectorBDE.v`

Defines a dynamic vector type. Shared definitions are in `VectorDefs.v`.

- **`vector (A : Type) : Type`** — Dynamic vector of type A
- **`emptyVec (A : Type)`** — Create empty vector
- **`get {A} (v : vector A) (x : int)`** — Get element at index
- **`push {A} (v : vector A) (a : A)`** — Append element
- **`pop {A} (v : vector A)`** — Remove last element
- **`size {A} (v : vector A)`** — Get vector length
- **`isEmpty {A} (v : vector A)`** — Check if empty
- **`assign {A} (v : vector A) (x : int) (a : A)`** — Set element at index

### `External/StringViewStd.v` / `External/StringViewBDE.v`

Defines a string view type for non-owning string references with axiomatic properties. Shared definitions are in `StringViewDefs.v`.

**Basic operations:**
- **`string_view : Type`** — Non-owning string view (extracts to `std::basic_string_view<char>`)
- **`empty (sv : string_view) : bool`** — Check if view is empty
- **`empty_sv : string_view`** — The empty string view
- **`sv_eq (sv1 sv2 : string_view) : bool`** — Equality check
- **`length (sv : string_view) : int`** — View length
- **`substr (sv : string_view) (i j : int) : string_view`** — Substring view from position i with length j
- **`sv_get (sv : string_view) (i : int) : char63`** — Character access (unchecked)
- **`sv_at (sv : string_view) (i : int) : char63`** — Character access (bounds-checked)
- **`sv_of_string (s : string) : string_view`** — Convert string to view
- **`contains (sv : string_view) (c : char63) : bool`** — Check if view contains character

**Axiomatic properties:**
- **`sv_eq_rel`** — Equivalence relation on string views
- **`empty_substr`** — Zero-length substring is always empty
- **`empty_length`** — View is empty iff its length is zero
- **`length_of_string`** — String view length equals string length
- **`substr_of_string_comm`** — Substring operations commute with string conversion
- **`contains_iff_exists_get`** — A view contains a character iff it appears at some valid position
- **`sv_get_substr`** — Characters in a substr match the original at offset positions
- **`length_substr`** — Length of a substr is bounded by the requested length
- **`length_substr_prefix`** — Prefix case: length of substr from 0
- **`contains_substr_prefix_false`** / **`contains_substr_prefix_true`** — Contains correctness for prefixes
- **`length_nonneg`** — Length is always non-negative

---

## C++ Runtime Headers

Crane includes C++ header files that support extracted code at runtime. These are located in `theories/cpp/`.

### `crane_itree.h`

C++ runtime for reified interaction trees. Defines the `ITree<R>` template class with `Ret`, `Tau`, and `Vis` variants, `observe()` for pattern matching, `run()` for execution, and `itree_bind` for monadic composition.

### `crane_real.h`

C++ `Real` class wrapping `long double`, used by `Mapping/Real.v`. Provides arithmetic operators, trigonometric functions, and conversion utilities.

### `stm_adapter.h`

Adapter header providing the `stm::` namespace API (`newTVar`, `readTVar`, `writeTVar`, `atomically`, `orElse`, `retry`) that STM extraction mappings target.

### `crane-stm/`

Full C++ implementation of Software Transactional Memory with transaction logs, control blocks, and conflict detection. This is the backend that `stm_adapter.h` delegates to.

### `persistent_array.h`

Copy-on-write persistent array implementation used by `PrimArray` extraction.
