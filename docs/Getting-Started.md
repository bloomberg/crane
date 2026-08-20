# Getting Started

## Installation

Once you clone the repo, if you have [opam](https://opam.ocaml.org/) and [dune](https://dune.build/), you can run

```bash
opam install . --deps-only
```

To install OCaml (at least 4.14.0) and Rocq (at least 9.0.0, and below 9.1). You can then build and install the project by running

```bash
make build && make install
```

You will also need [Clang](https://clang.llvm.org/) 19 or higher to run the tests, and [clang-format](https://clang.llvm.org/docs/ClangFormat.html) for standard formatting.

To run the tests, use:

```bash
make test                    # Run all tests
make test-one TEST=list      # Run a single test
make test-folder FOLDER=basics  # Run one thematic folder
make test-list               # List the available test names
make format                  # Re-format the OCaml sources
make help                    # Show every target with a short description
```

To run the `Crane Benchmark` command, you will need to have [hyperfine](https://github.com/sharkdp/hyperfine) installed.

## Usage

Once you write your Rocq program, you can extract to C++:

```coq
Module Foo.

Fixpoint fac n :=
  match n with
  | 0 | 1 => 1
  | S n' => n * fac n'
  end.

End Foo.

Require Crane.Extraction.
Require Crane.Mapping.Std.
Crane Extraction "Foo" Foo.
```

(You can also extract a single function if you do not want to extract an entire module, which will just extract the function with all of its dependencies as opposed to this which extracts all the definitions in the module [and their dependencies].)

Now run:

```bash
rocq compile Foo.v && clang++ -c -std=c++23 -I<crane>/theories/cpp Foo.cpp -o Foo.o
```

This creates `Foo.h` and `Foo.cpp` from the Rocq file, then compiles the C++ to the object file `Foo.o` with Clang, ready to be linked to your own C++ file containing a `main` function for execution.

The `-I` is needed because generated code includes Crane's runtime headers — `small_vector.h` here, and depending on what you extract also `rc.h`, `crane_fn.h`, `lazy.h`, or `arena.h`. These are header-only and live in `theories/cpp` in the Crane checkout; they are not installed onto the system include path, so point `-I` at that directory (or copy the headers into your own project).
