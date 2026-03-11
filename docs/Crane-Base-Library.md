# Crane Base Library

Crane comes with a base library of mappings, and types for monadic effects. The library can be found [here](https://github.com/bloomberg/crane/tree/main/theories).

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

Maps Rocq's `nat` type to `unsigned int` with std library operations.

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

---

## Monad Definitions

### `Monads/ITree.v`

Defines the interaction tree monad, a coinductive type for representing effectful computations.

- **`itreeF (E : Type → Type) (R : Type) (itree : Type) : Type`** — Functor for tree nodes: return, tau step, or visible effect
- **`itree (E : Type → Type) (R : Type) : Type`** — Coinductive interaction tree over effect type E with result type R
- **`Ret {E : Type → Type} {R : Type} (x : R) : itree E R`** — Return value x
- **`Tau {E : Type → Type} {R : Type} (t : itree E R) : itree E R`** — Internal choice (tau step)
- **`Vis {E : Type → Type} {R : Type} {X : Type} (e : E X) (k : X → itree E R) : itree E R`** — Visible effect e with continuation k
- **`bind {E : Type → Type} {T U : Type} (u : itree E T) (k : T → itree E U) : itree E U`** — Monadic bind
- **`trigger {E : Type → Type} {T : Type} (e : E T) : itree E T`** — Trigger an effect
- **`hoist {E1 E2 : Type → Type} {R : Type} (t : ∀ X : Type, E1 X → E2 X) (tr : itree E1 R) : itree E2 R`** — Transform effect types in a tree

Supports monadic notation: `e1 ;; e2` for sequencing and `x <- c1 ;; c2` for binding.

### `Monads/IO.v`

Defines the IO monad for input/output operations.

- **`IO (A : Type) : Type`** — Type `itree iIO A` representing I/O computations
- **`print (s : string) : IO void`** — Print string without newline
- **`print_endline (s : string) : IO void`** — Print string with newline
- **`get_line : IO string`** — Read line from standard input
- **`read (s : string) : IO string`** — Read contents of file named s

### `Monads/IOBDE.v`

BDE variant of the IO monad with identical structure.

### `Monads/STM.v`

Defines the Software Transactional Memory monad for concurrent, atomic operations.

- **`STM (A : Type) : Type`** — Type `itree iSTM A` representing transactional computations
- **`atomically {A : Type} (t : STM A) : IO A`** — Execute STM transaction atomically
- **`retry {A : Type} : STM A`** — Retry the current transaction
- **`orElse {A : Type} (l : STM A) (r : STM A) : STM A`** — Alternative transaction
- **`check (b : bool) : STM void`** — Assert condition or retry
- **`getSTM {A : Type} (v : vector A) (i : int) : STM A`** — Get element from vector
- **`isEmptySTM {A : Type} (v : vector A) : STM bool`** — Check if vector is empty
- **`TVar (A : Type) : Type`** — Transactional variable of type A
- **`newTVar {A : Type} (a : A) : STM (TVar A)`** — Create new transactional variable
- **`readTVar {A : Type} (v : TVar A) : STM A`** — Read value from transactional variable
- **`writeTVar {A : Type} (v : TVar A) (a : A) : STM void`** — Write value to transactional variable
- **`modifyTVar {A : Type} (a : TVar A) (f : A → A) : STM void`** — Atomically modify a transactional variable

### `Monads/STMBDE.v`

BDE variant of the STM monad with similar structure to `STM.v`, using BDE library types.

**Differences from STM.v:**
- Uses `bsl::shared_ptr` instead of `std::shared_ptr` for TVar
- TVar operations (`readTVar`, `writeTVar`) extracted as standalone functions instead of member functions
- `orElse` extraction is commented out

### `Monads/Thread.v`

Defines the Conc monad for thread-based concurrency with cost tracking.

- **`Conc {z : int} (A : Type) : Type`** — Concurrent computation with cost z
- **`Cret {A : Type} (a : A) : Conc {0} A`** — Return value with zero cost
- **`Cbind {x y : int} {A B : Type} (c : Conc {x} A) (f : A → Conc {y} B) : Conc {x + y} B`** — Bind with cost addition
- **`Ceval {A : Type} (c : Conc {0} A) : A`** — Evaluate a zero-cost computation
- **`thread : Type`** — Thread type
- **`mk_thread {A B : Type} (f : A → B) (a : A) : Conc {1} thread`** — Create and run a new thread
- **`join (t : thread) : Conc {-1} void`** — Wait for thread to complete
- **`sleep (ms : int) : Conc {0} void`** — Sleep for milliseconds
- **`print_endline (s : string) : Conc {0} void`** — Print string with newline

Supports monadic notation via `ConcNotations`.

### `Monads/Par.v`

Defines the Par monad for parallel computation with cost tracking.

- **`Par (S : Type) {z : int} (A : Type) : Type`** — Parallel computation with cost z
- **`Pret {S : Type} {A : Type} (a : A) : Par S {0} A`** — Return value with zero cost
- **`Pbind {S : Type} {x y : int} {A B : Type} (p : Par S {x} A) (f : A → Par S {y} B) : Par S {x + y} B`** — Bind with cost addition
- **`runPar {A : Type} (p : ∀ S : Type, Par S {0} A) : A`** — Execute a zero-cost parallel computation
- **`thread (S : Type) (B : Type) : Type`** — Future type for parallel result
- **`mk_thread {S : Type} {A B : Type} (f : A → B) (a : A) : Par S {1} (thread S B)`** — Spawn async task
- **`get_thread {S : Type} {B : Type} (t : thread S B) : Par S {-1} B`** — Wait for task result

**Warning**: Current axioms allow getting the same thread twice, which is unsound.

Supports monadic notation via `ParNotations`.

---

## External Types

### `External/Vector.v`

Defines a dynamic vector type backed by the IO monad.

- **`vector (A : Type) : Type`** — Dynamic vector of type A
- **`emptyVec (A : Type) : IO (vector A)`** — Create empty vector
- **`get {A : Type} (v : vector A) (x : int) : IO A`** — Get element at index
- **`push {A : Type} (v : vector A) (a : A) : IO void`** — Append element
- **`pop {A : Type} (v : vector A) : IO void`** — Remove last element
- **`size {A : Type} (v : vector A) : IO int`** — Get vector length
- **`isEmpty {A : Type} (v : vector A) : IO bool`** — Check if empty
- **`assign {A : Type} (v : vector A) (x : int) (a : A) : IO (vector A)`** — Set element at index

### `External/VectorBDE.v`

BDE variant of the vector type with identical structure.

### `External/StringViewStd.v`

Defines a string view type for non-owning string references with axiomatic properties.

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
- **`sv_eq_rel : relation string_view`** — Equivalence relation on string views
- **`sv_eq_rel_equiv : equivalence string_view sv_eq_rel`** — String view equality is an equivalence relation
- **`empty_substr (sv : string_view) (i : int) : empty (substr sv i 0) = true`** — Zero-length substring is always empty
- **`empty_length (sv : string_view) : empty sv = true ↔ length sv = 0`** — View is empty iff its length is zero
- **`length_of_string (s : string) : length (sv_of_string s) = PrimString.length s`** — String view length equals string length
- **`substr_of_string_comm (s : string) (i j : int) : compare i j <> Gt → compare j (PrimString.length s) <> Gt → substr (sv_of_string s) i (sub j i) = sv_of_string (PrimString.sub s i j)`** — Substring operations commute with string conversion
- **`contains_iff_exists_get (sv : string_view) (c : char63) : contains sv c = true ↔ ∃ i, leb 0 i = true ∧ ltb i (length sv) = true ∧ sv_get sv i = c`** — A string_view contains a character iff that character appears at some valid position
- **`sv_get_substr (sv : string_view) (start len i : int) : leb 0 i = true → ltb i len = true → ltb (add start i) (length sv) = true → sv_get (substr sv start len) i = sv_get sv (add start i)`** — Characters in a prefix substr are exactly those in the corresponding positions of the original
- **`length_substr (sv : string_view) (start len : int) : leb 0 start = true → leb 0 len = true → length (substr sv start len) = if ltb (add start len) (length sv) then len else if leb start (length sv) then sub (length sv) start else 0`** — Length of a substr is bounded by the requested length
- **`length_substr_prefix (sv : string_view) (len : int) : leb 0 len = true → leb len (length sv) = true → length (substr sv 0 len) = len`** — Simpler axiom for prefix case: length of substr from 0
- **`contains_substr_prefix_false (sv : string_view) (n : int) (c : char63) : leb 0 n = true → leb n (length sv) = true → (∀ i, leb 0 i = true → ltb i n = true → sv_get sv i <> c) → contains (substr sv 0 n) c = false`** — If no position in [0, n) contains a character c, then contains returns false
- **`contains_substr_prefix_true (sv : string_view) (n c i : int) : leb 0 n = true → leb n (length sv) = true → leb 0 i = true → ltb i n = true → sv_get sv i = c → contains (substr sv 0 n) c = true`** — Conversely, if some position contains c, then contains returns true
- **`length_nonneg (sv : string_view) : leb 0 (length sv) = true`** — Length is always non-negative
