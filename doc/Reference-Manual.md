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

Run performance benchmarks for a Rocq benchmark function using multiple compilers / optimization settings.
The benchmarked definition must have type `unit -> string` - it takes unit as input and returns a string result.
Crane will generate a report through [hyperfine](https://github.com/sharkdp/hyperfine), comparing runtime performance.

### Syntax

```coq
Crane Benchmark <Rocq benchmark function name> On
  <backend0> From "<file>" With "<flags>",
  <backend1> From "<file>" With "<flags>".
```

* **`<Rocq benchmark function name>`**
  The name of the Rocq definition to benchmark. This definition must have type `unit -> string`. The same definition should be extracted to the files specified in the benchmark entries.

* **`<backend>`**
  The compilation backend to use.

* **`"<file>"`**
  The path to the source file to compile and benchmark. This should be a file that was generated by extracting the Rocq definition specified earlier.

* **`"<flags>"`**
  Compiler flags to pass to the backend compiler (e.g., `"-O1"`, `"-O2"`, `"-O3"` for optimization levels). Since this is a string, multiple flags can be passed in this string, separated by spaces.

### Backends

| Backend | Meaning                                    |
| ------- | ------------------------------------------ |
| `OCaml` | Use Rocq's OCaml extraction and `ocamlopt` |
| `C++`   | Use Crane's C++ extraction and `clang++`   |

### Example

```coq
Definition benchmark : unit -> string :=
  fun _ => ToString.list_to_string (ToString.list_to_string string_of_nat)
    (TopSort.topological_sort_graph Nat.eqb
      [ (1, [2; 3])
      ; (2, [4])
      ; (3, [4; 5])
      ]).

Extraction "./top/benchmark/benchmark.ml" benchmark.
Crane Extraction "./top/benchmark/benchmark.cpp" benchmark.

Crane Benchmark benchmark On
  OCaml From "./top/benchmark/benchmark.ml" With "-O1",
  C++   From "./top/benchmark/benchmark.cpp" With "-O1",
  OCaml From "./top/benchmark/benchmark.ml" With "-O2",
  C++   From "./top/benchmark/benchmark.cpp" With "-O2",
  OCaml From "./top/benchmark/benchmark.ml" With "-O3",
  C++   From "./top/benchmark/benchmark.cpp" With "-O3".
```

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
