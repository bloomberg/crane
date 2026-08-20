# Reference Manual

This reference manual documents all Crane commands, configuration settings, extraction rules, and supported syntactic forms.
It is intended to be exhaustive, precise, and implementation-accurate.

---

## `Crane Extract Inductive`

Define how a Rocq inductive type should be mapped to C++.

### Syntax

```coq
Crane Extract Inductive <Rocq type> =>
  "<C++ type>"
  [ "<C++ term for Rocq constructor 0>"  "<C++ term for Rocq constructor 1>" ]
  "<C++ statements for pattern matching>"
  From "<library0>" "<library1>".
```

* **`<Rocq type>`**
  The name of the Rocq inductive type being mapped (e.g., `option`, `prod`, `list`).

* **`"<C++ type>"`**
  The C++ type expression that corresponds to the Rocq inductive type. This is a template string that may include type parameter placeholders (`%t0`, `%t1`, etc.) to represent polymorphic type arguments.

* **`[ "<C++ term for Rocq constructor 0>" "<C++ term for Rocq constructor 1>" ... ]`**
  A space-separated list of C++ expressions enclosed in square brackets, one for each constructor of the Rocq inductive type. Each expression defines how to construct a value of the C++ type corresponding to that Rocq constructor. These expressions may use constructor argument placeholders (`%a0`, `%a1`, etc.).

* **`"<C++ statements for pattern matching>"`**
  A C++ code block that implements pattern matching (case analysis) on values of this type. This should dispatch to the appropriate branch based on which constructor was used, binding constructor arguments to names specified by branch parameter placeholders (`%b0a0`, `%b0a1`, etc.) and executing the corresponding branch code (`%br0`, `%br1`, etc.).

* **`From ...` clause**
  A space-separated list of libraries/headers whose inclusion is required.  Crane will translate these to the corresponding `#include <...>` directives.

### Example: mapping Rocq's `option` type to `std::optional`

```coq
Crane Extract Inductive option =>
  "std::optional<%t0>"
  [ "std::make_optional<%t0>(%a0)"
    "std::nullopt" ]
  "if (%scrut.has_value()) {
     %t0 %b0a0 = *%scrut; %br0
   } else {
     %br1
   }"
  From "optional" "memory".
```

### Example: mapping Rocq's `prod` type to `std::pair`

```coq
Crane Extract Inductive prod =>
  "std::pair<%t0, %t1>"
  [ "std::make_pair(%a0, %a1)" ]
  "%t0 %b0a0 = %scrut.first;
   %t1 %b0a1 = %scrut.second;
   %br0"
  From "utility".
```

### Structure

Placeholders inside extraction templates provide access to type arguments,
constructor arguments, branch parameters, and the scrutinee.

### Placeholder Table

| Placeholder       | Meaning                                          |
| ----------------- | ------------------------------------------------ |
| `%t0`, `%t1`, ... | Type parameters to the inductive type            |
| `%a0`, `%a1`, ... | Constructor arguments                            |
| `%scrut`          | Scrutinee in a pattern match                     |
| `%b0a0`           | Name bound to the 0th argument of the 0th branch |
| `%br0`, `%br1`    | The branch for the 0th, 1st, ... constructor.    |
| `%elem`           | Element slot of a container carrying a `Boxed Element` clause (see below) |

### `Boxed Element` clause

Some C++ container types require a **complete** element type: they evaluate `sizeof`/`alignof` of the element at the point the container type is *named*, not merely when it is used (the immer containers behave this way). A Rocq inductive that is recursive *through* such a container — for example a `json` type with a field of type `list json` — would name the container with an incomplete element type, which does not compile. The `Boxed Element` clause lets a container mapping wrap its element in a pointer-sized indirection (a "box") **only at those recursive occurrences**, leaving every other element unwrapped.

#### Syntax

```coq
Crane Extract Inductive <Rocq type> =>
  "<C++ type using %elem>"
  [ "<C++ term for Rocq constructor 0>" ... ]
  "<C++ statements for pattern matching>"
  Boxed Element "<wrapper>"
  From "<library0>" "<library1>".
```

The clause appears after the pattern-matching block and before the `From` clause; as elsewhere, the `From` clause may be omitted.

* **`"<wrapper>"`**
  A C++ type template over `%t0` (the bare element type) that provides the indirection, e.g. `"immer::box<%t0>"`. The wrapper must be pointer-sized, copyable, and convert implicitly both to and from `%t0`, so that the constructor and pattern-matching templates are identical whether or not the element is boxed.

#### The `%elem` placeholder

With a `Boxed Element` clause, use `%elem` in place of `%t0` in the container's type and constructor templates wherever the stored element type appears. Crane resolves `%elem`, per element type, to:

* the wrapper applied to that element (`%t0` substituted with the element type) when the element is a generated inductive that recurses through this container, and
* the bare element type otherwise.

The decision is made per element type and is global: a given `<container> T` has one and the same C++ representation everywhere it occurs. Element types that can never be recursive through the container — scalars, custom-mapped types, function types, all-nullary (`enum class`) inductives, and non-recursive structs — are never boxed.

#### Example

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

Given `Inductive json := JList (elems : list json) | ...`, the recursive `list json` occurrence is emitted as `immer::flex_vector<immer::box<json>>`, while a non-recursive occurrence such as `list ascii` is emitted as `immer::flex_vector<char>` — unboxed.

#### Interaction with recursive fields

Crane normally wraps a constructor field that recurses through a container in `std::shared_ptr` (or, under `Crane Arena`, a raw region pointer) so that the field has a known size while the type is still incomplete. When the element is already boxed via a `Boxed Element` clause, that box breaks the cycle, so the outer indirection is redundant: Crane stores such a field **by value** instead. In the example above, `JList`'s field is emitted as `immer::flex_vector<immer::box<json>>` directly, not `std::shared_ptr<immer::flex_vector<immer::box<json>>>`.

---

## `Crane Extract Inlined Constant`

Map a Rocq constant to a literal C++ expression (i.e., no function call or wrapper).

### Syntax

```coq
Crane Extract Inlined Constant <Rocq definition name> => "<C++ expr>" From "<library0>" "<library1>".
```

* **`<Rocq definition name>`**
  The name of the Rocq constant or function being mapped (e.g., `fst`, `snd`).

* **`"<C++ expr>"`**
  A C++ expression that replaces calls to the Rocq constant. This expression may use argument placeholders (`%a0`, `%a1`, etc.) to reference the arguments passed to the constant.

* **`From ...` clause**
  A space-separated list of libraries/headers whose inclusion is required. Crane will translate these to the corresponding `#include <...>` directives.

### Examples

```coq
Crane Extract Inlined Constant fst => "%a0.first" From "utility".
Crane Extract Inlined Constant snd => "%a0.second" From "utility".
```

### Placeholder Table

| Placeholder       | Meaning                                          |
| ----------------- | ------------------------------------------------ |
| `%a0`, `%a1`, ... | Arguments of the constant                        |

---

## `Crane Extract Constant`

Provide a C++ implementation for a Rocq `Parameter`/`Axiom` (a constant with no
body — extraction has nothing to translate on its own). Crane generates a
static method whose body simply forwards to the given C++ name, applying it to
the constant's own parameters positionally: `return <C++ expr>(<param0>,
<param1>, ...);`. This is **not** a placeholder-substitution template like
`Crane Extract Inlined Constant` — you supply a callable C++ expression (a
function name, or something that can be called like one), not an arbitrary
expression using `%a0`/`%a1`.

Only applies to constants without a body; it has no effect if used on a
constant that Rocq can already extract from its definition.

### Syntax

```coq
Crane Extract Constant <Rocq definition name> [ "<id0>" "<id1>" ... ] => "<C++ callable>" From "<library0>" "<library1>".
```

* **`<Rocq definition name>`**
  The name of the Rocq `Parameter`/`Axiom` being mapped.

* **`[ "<id0>" "<id1>" ... ]`**
  Optional space-separated list of strings accepted by the grammar for parity
  with upstream Rocq extraction; currently unused by Crane's code generator
  for constants (it does not affect the generated forwarding call).

* **`"<C++ callable>"`**
  The name of a C++ function (or other callable expression) to invoke with the
  constant's arguments, in order. Not a `%a0`-style template.

* **`From ...` clause**
  Optional; a space-separated list of libraries/headers whose inclusion is
  required — Crane adds the corresponding `#include` directives.

### Example

```coq
Parameter foreign_inc : nat -> nat.
Crane Extract Constant foreign_inc => "foreign_inc_impl" From "foreign_inc_impl.h".
```

This generates (roughly):

```cpp
static uint64_t foreign_inc(uint64_t _x0);
// ...
uint64_t Module::foreign_inc(uint64_t _x0) {
  return foreign_inc_impl(_x0);
}
```

---

## `Crane Extract Foreign Constant`

Like `Crane Extract Constant`, but restricted to function-typed constants (it
errors if given a `Parameter`/`Axiom` whose type is a sort/arity rather than a
function type) and without a `From` clause. At the code-generation level it
currently produces the same forwarding-call body as `Crane Extract Constant`;
the practical differences are the missing `From` clause and the function-type
restriction, plus separate internal bookkeeping so it can't be redefined via
the other `Extract Constant` variants (and vice versa).

### Syntax

```coq
Crane Extract Foreign Constant <Rocq definition name> => "<C++ callable>".
```

### Example

```coq
Parameter native_checksum : nat -> nat.
Crane Extract Foreign Constant native_checksum => "native_checksum".
```

---

## `Crane Extraction`

Perform C++ extraction of a Rocq definition.
The extracted code will include all mappings currently in scope.

### Syntax 1

```coq
Crane Extraction "<output path>" <Rocq definition name>.
```

* **`"<output path>"`**
  The file path (relative or absolute) for the generated C++ files. If the path ends with `.cpp`, Crane will strip the extension. The command generates both `.h` and `.cpp` files at the specified location.

* **`<Rocq definition name>`**
  The name of the Rocq definition to extract (e.g., a function, module, or type).

#### Example

```coq
Crane Extraction "tokenizer" Tokenizer.
```

### Syntax 2

```coq
Crane Extraction <Rocq definition name>.
```

* **`<Rocq definition name>`**
  The name of the Rocq definition to extract. When no output path is specified, the extracted code is displayed in the editor's response window instead of being written to files.

#### Example

```coq
Crane Extraction Tokenizer.
```

### Related commands

* `Crane Recursive Extraction <name0> <name1> ...` — like Syntax 2, but extracts several definitions (and their dependencies) together, displayed in the response window.
* `Crane Separate Extraction <name0> <name1> ...` — extracts several definitions with the generated code split across one file per Rocq library, instead of a single monolithic file.
* `Crane Extraction Library <module>` — extracts an entire compiled Rocq library (`.vo`) to a corresponding C++ file, mirroring the module structure.
* `Crane Recursive Extraction Library <module>` — like `Crane Extraction Library`, but also recursively extracts every library that `<module>` depends on.
* `Crane Extraction TestCompile <name0> <name1> ...` and `Crane Extraction TestCompile "<output path>" <name0> <name1> ...` — like `Crane Extraction`, but additionally compiles the generated C++ with Clang (using the current BDE/StdLib settings) to check it builds, without producing a linkable artifact for you to keep. Useful as a quick correctness smoke test during development.

---

## `Crane Extraction Language`

Select the target language for extraction.

### Syntax

```coq
Crane Extraction Language C++.
```

Currently `C++` is the only supported language; the command exists for parity with upstream Rocq extraction and future extensibility.

---

## `Crane Extraction Inline` / `Crane Extraction NoInline`

Force specific constants to be inlined (or not inlined) at their call sites during extraction, independent of any custom C++ mapping.

### Syntax

```coq
Crane Extraction Inline <name0> <name1> ...
Crane Extraction NoInline <name0> <name1> ...
Crane Print Extraction Inline.
Crane Reset Extraction Inline.
```

* `Crane Extraction Inline` marks the given constants for inlining.
* `Crane Extraction NoInline` removes that marking.
* `Crane Print Extraction Inline` shows the constants currently marked for inlining.
* `Crane Reset Extraction Inline` clears all inlining marks set via these commands.

---

## `Set Crane StdLib`

Select the mapping set for standard types.

### Syntax

```coq
Set Crane StdLib "<name>".
```

* **`"<name>"`**
  The name of the standard library mapping set to use.

### Options

| StdLib Name | Meaning                                                                 |
| ----------- | ----------------------------------------------------------------------- |
| `"std"`     | Use C++ standard library types (e.g., `std::string`, `std::shared_ptr`) |
| `"BDE"`     | Use Bloomberg's BDE types (`bsl::string`, `bsl::shared_ptr`, etc.)      |

### Examples

```coq
Set Crane StdLib "std".
Set Crane StdLib "BDE".
```

Selecting `"std"` or `"BDE"` loads the appropriate predefined extraction mappings from the Crane Base Library.

---

## `Set Crane BDE Directory`

Required when working with BDE and performing compilation tests via:

```
Crane Extraction TestCompile
```

### Syntax

```coq
Set Crane BDE Directory "<path>".
```

* **`"<path>"`**
  The filesystem path to the BDE installation directory. This can be a relative path (e.g., `"./bde_install"`) or an absolute path (e.g., `"~/bde_install/"` or `"/usr/local/bde"`). Crane uses this directory to locate include paths, library files, auxiliary tools used by the BDE environment.

### Example

```coq
Set Crane BDE Directory "~/bde_install/".
```

---

## `Crane Benchmark`

Compare one or more observationally equivalent Rocq definitions across multiple
backends and compiler configurations. Every benchmarked definition must have
type `unit -> PrimString.string`.

Crane extracts each definition once per backend, builds the Cartesian product
of definitions and configurations, and runs every executable once. The command
stops if a build fails or if the programs produce different output. Only after
that check does Crane generate a performance report with
[hyperfine](https://github.com/sharkdp/hyperfine).

### Syntax

```coq
Crane Benchmark
  <function0> [As "<label0>"],
  <function1> [As "<label1>"],
  ...
On
  <backend0> [With "<flags0>"],
  <backend1> [With "<flags1>"],
  <backendN> [With "<flagsN>"].
```

* **`<function>`**
  A Rocq definition of type `unit -> PrimString.string`. Crane performs the
  required C++ or OCaml extraction automatically.

* **`As "<label>"`**
  An optional name used in the report. Without it, Crane displays the Rocq
  qualified name.

* **`<backend>`**
  The compilation backend to use.

* **`"<flags>"`**
  Optional flags passed directly to the backend compiler, such as `"-O3"` or
  `"-O3 -flto"`. Quoted arguments and backslash escaping are supported within
  the string.

### Backends

| Backend | Meaning                                    |
| ------- | ------------------------------------------ |
| `OCaml` | Use Rocq's OCaml extraction and `ocamlopt` |
| `C++`   | Use Crane's C++ extraction and `clang++`   |

### Example

```coq
Definition baseline (_ : unit) : string := run_baseline input.
Definition optimized (_ : unit) : string := run_optimized input.

Crane Benchmark
  baseline As "baseline",
  optimized As "optimized"
On
  C++ With "-O3",
  OCaml With "-O3".
```

This example builds four benchmarks. `baseline` and `optimized` must print
exactly the same result in all four builds.

---

## `Crane Extract Skip`

Exclude a Rocq symbol from extraction. Use this for axioms or primitives that are provided externally in C++ (e.g., by a native library). Crane will not emit a definition for the skipped symbol; references to it are assumed to link against your external implementation.

### Syntax

```coq
Crane Extract Skip <Rocq identifier>.
```

* **`<Rocq identifier>`**
  The name of the Rocq type, constant, or axiom to omit from generated C++.

### Example

```coq
Crane Extract Skip iSTM.
Crane Extract Skip iatomically.
```

---

## `Crane Extract Skip Module`

Exclude an entire Rocq module from extraction. Use this for modules containing axioms, proof terms, or internal implementation details that should not appear in the generated C++.

### Syntax

```coq
Crane Extract Skip Module <Rocq module>.
```

* **`<Rocq module>`**
  The qualified name of the Rocq module to omit from generated C++.

### Example

```coq
Crane Extract Skip Module Rdefinitions.RbaseSymbolsImpl.
Crane Extract Skip Module Random_axioms.
```

---

## `Set Crane Loopify` / `Crane Loopify`

Control the loopification optimization, which transforms recursive functions into iterative C++ using explicit stacks.

### Global flag

```coq
Set Crane Loopify.    (* Enable loopification for all eligible functions *)
Unset Crane Loopify.  (* Disable loopification (default) *)
```

When enabled, Crane automatically transforms eligible recursive functions (tail-recursive, tail-modulo-cons, and multi-recursive patterns) into `while` loops with explicit stack frames.

### Per-function control

```coq
Crane Loopify <function0> <function1> ...    (* Enable for specific functions *)
Crane NoLoopify <function0> <function1> ...  (* Disable for specific functions *)
Crane Reset Loopify.                         (* Reset all loopification settings *)
```

### Example

```coq
Set Crane Loopify.
Crane Extraction "my_module" MyModule.
```

### Checking what was loopified

`Set Crane Loopify Diagnostics` reports what the pass did with each recursive
function, and `Set Crane Loopify Strict` turns a function it could not
linearise into an error. See [Loopify coverage](loopify-coverage.md) for how
the outcomes are decided and which shapes remain out of reach.

---

## `Set Crane Arena` / `Crane Arena`

Control arena (region) allocation for recursive inductive types. In arena mode, an eligible recursive inductive's recursive fields are stored as raw pointers into a bump-allocated region instead of `std::shared_ptr`. The whole value is then destroyed in O(1) by dropping the region, with no per-node deallocation, no reference counting, and no iterative destructor.

Opt-in: arena values deep-copy on value-copy (a copy allocates into a fresh region), trading cheap structural sharing for cheap allocation and destruction.

### Global flag

```coq
Set Crane Arena.    (* Use arena allocation for all eligible recursive inductives *)
Unset Crane Arena.  (* Use the default shared_ptr representation (default) *)
```

### Per-inductive control

```coq
Crane Arena <ind0> <ind1> ...     (* Force arena allocation for specific inductives *)
Crane NoArena <ind0> <ind1> ...   (* Force the default representation for specific inductives *)
Crane Reset Arena.                (* Clear all per-inductive arena settings *)
```

* **`<ind>`**
  The name of a recursive inductive type.

For a given inductive, a per-inductive `Crane Arena`/`Crane NoArena` setting takes precedence over the global flag (and `Crane Arena` wins over `Crane NoArena` if both are set); without a per-inductive setting, the global `Set Crane Arena` flag applies.

### Eligibility

Arena allocation currently applies only to plain self-recursive value types. If an inductive selected for arena mode is coinductive or mutually recursive, Crane falls back to the default `shared_ptr` representation for that type and prints a warning; the rest of the extraction is unaffected.

### Generated code

When any type is extracted in arena mode, Crane automatically emits `#include "arena.h"` — the Crane runtime header providing `crane::arena` and the ambient-region helpers. Allocation sites allocate into the current ambient region, which a driver installs with a `crane::arena_scope` RAII guard around the code that builds arena values.

### Examples

```coq
Set Crane Arena.
Crane Extraction "my_module" MyModule.
```

```coq
Unset Crane Arena.
Crane Arena tree.          (* only [tree] uses arena allocation *)
Crane Extraction "trees" Trees.
```

---

## `Crane Extraction Implicit`

Declare that certain arguments of a constant, inductive, or constructor are implicit and should be dropped from the extracted C++ signature, mirroring Rocq's own implicit-argument mechanism for cases Crane cannot infer automatically.

### Syntax

```coq
Crane Extraction Implicit <Rocq identifier> [ <arg0> <arg1> ... ].
```

* **`<Rocq identifier>`**
  The constant, inductive, or constructor whose arguments are being marked.

* **`[ <arg0> <arg1> ... ]`**
  A space-separated list of argument positions (1-indexed integers) or argument names to treat as implicit.

### Example

```coq
Crane Extraction Implicit map [ 1 ].
```

---

## `Crane Extraction Blacklist`

Prevent Crane from using specific identifiers as generated file/module names, to avoid collisions with existing C++ headers or reserved names.

### Syntax

```coq
Crane Extraction Blacklist <name0> <name1> ...
Crane Print Extraction Blacklist.
Crane Reset Extraction Blacklist.
```

* `Crane Extraction Blacklist` adds identifiers to the blacklist.
* `Crane Print Extraction Blacklist` shows the current blacklist.
* `Crane Reset Extraction Blacklist` clears it.

### Example

```coq
Crane Extraction Blacklist String List.
```

---

## `Crane Extract Callback`

Register a Rocq definition as an ML/C callback target — a function that native (foreign) code can call back into. Used together with `Crane Extract Foreign Constant`-style FFI bridges.

### Syntax

```coq
Crane Extract Callback ["<label>"] <Rocq definition name>.
Crane Print Extraction Callback.
Crane Reset Extraction Callback.
```

* **`"<label>"`**
  Optional label used to name the callback entry point. Without it, Crane derives a name from the Rocq identifier.

* `Crane Print Extraction Callback` lists registered callbacks.
* `Crane Reset Extraction Callback` clears all registered callbacks.

---

## `Crane Print Extraction Foreign`

Show the constants currently registered via `Crane Extract Foreign Constant`.

### Syntax

```coq
Crane Print Extraction Foreign.
```

---

## `Crane Extract Void`

Register a Rocq axiom/constant as an uninhabited (void) type paired with a "ghost" term used to satisfy Rocq's syntax where a value is required but never actually produced/consumed at runtime. Both the void type and the ghost term are erased from the generated C++.

### Syntax

```coq
Crane Extract Void <Rocq void type> [ <Rocq ghost term> ].
```

* **`<Rocq void type>`**
  A constant already established (e.g., via an axiom) as an empty/uninhabited type.

* **`<Rocq ghost term>`**
  A placeholder term of that type used only to satisfy Rocq's type checker; it is never extracted.

### Example

```coq
Crane Extract Void MyEffect.void [ MyEffect.ghost ].
```

---

## `Crane Guard Compare`

Register a comparison-guard relationship between a function and a constructor, informing Crane's loopification/pattern-match analysis that calls to `<function>` should be treated as guarded by that constructor for termination/structural purposes.

### Syntax

```coq
Crane Guard Compare <Rocq function> => <Rocq constructor>.
```

* **`<Rocq function>`**
  Must be a plain constant (not an inductive or constructor).

* **`<Rocq constructor>`**
  The constructor used as the comparison guard.

---

## `Crane Show Extraction`

Display the C++ extraction of the term corresponding to the current proof state (e.g., while working inside a proof script). Useful for interactively inspecting how in-progress definitions will extract.

### Syntax

```coq
Crane Show Extraction.
```

---

## `Crane Extract Numeral`

Register a Peano-style or binary numeric inductive type for numeral folding. When registered, chains of constructors like `S(S(S(O)))` are folded into integer literals (e.g., `3u`) in the generated C++.

### Syntax

```coq
Crane Extract Numeral <Rocq inductive type> => "<format string>".
```

* **`<Rocq inductive type>`**
  The name of the Rocq inductive type to register (e.g., `nat`, `N`, `Z`). Must be an inductive type with a recognizable zero/successor pattern (for Peano types) or a binary numeric type.

* **`"<format string>"`**
  A C++ expression template where `%n` is replaced by the folded integer value.

### Placeholder Table

| Placeholder | Meaning                               |
| ----------- | ------------------------------------- |
| `%n`        | The folded integer value              |

### Examples

```coq
Crane Extract Numeral nat => "%nu".    (* nat: S(S(S(O))) → 3u *)
Crane Extract Numeral N => "%nu".      (* N: binary nat → unsigned literal *)
Crane Extract Numeral Z => "INT64_C(%n)".  (* Z: binary integer → INT64_C(42) *)
```

---

## `Crane Extract Monad`

Define how a Rocq monad should be mapped to a C++ monad type, and tell Crane which Rocq identifiers implement `bind` and `ret`. This enables correct translation of monadic notation and do-notation.

### Syntax

```coq
Crane Extract Monad <Rocq monad type> [ bind := <bind name> , ret := <ret name> ] => "<C++ monad type>".
```

* **`<Rocq monad type>`**
  The type constructor of the Rocq monad (e.g., `STM`).
* **`bind := <bind name>`**
  The Rocq identifier implementing monadic bind for this monad.
* **`ret := <ret name>`**
  The Rocq identifier implementing monadic return for this monad.
* **`"<C++ monad type>"`**
  The C++ monad type expression. Use `%t0` to refer to the result type parameter of the monad.

### Example

```coq
Crane Extract Monad STM [ bind := bind , ret := Ret ] => "%t0".
```
