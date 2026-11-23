# Getting Started

## Installation

Once you clone the repo, if you have [opam](https://opam.ocaml.org/) and [dune](https://dune.build/), you can run

```bash
opam repo add rocq-released https://rocq-prover.org/opam/released # Make the rocq packages repository available for 'opam install'
opam install . --deps-only
```

To install OCaml (5.4.1 or a later 5.4 release) and Rocq (9.1.0, or a later 9.1 release). You can then build and install the project by running

```bash
make build && make install
```

A flambda compiler is recommended, and CI uses one. The plugin needs no extra flags for it (`-O3` measured no faster). To create such a switch:

```bash
opam switch create crane-flambda --packages ocaml-variants.5.4.1+options,ocaml-option-flambda \
  --repos rocq-released=https://rocq-prover.org/opam/released,coq-released=https://coq.inria.fr/opam/released,default
eval $(opam env --switch=crane-flambda --set-switch)
opam install rocq-runtime.9.1.0 rocq-core.9.1.0 coq.9.1.0
opam install . --deps-only
```

You will also need [Clang](https://clang.llvm.org/) 22 or higher to compile the generated code (C++26, `-std=c++2c`) and to run the tests.

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

Write a Rocq file, say `Example.v`, that loads Crane, imports a mapping set,
and extracts a module:

```coq
From Crane Require Import Extraction Mapping.Std.

Module Foo.

Fixpoint fac n :=
  match n with
  | 0 | 1 => 1
  | S n' => n * fac n'
  end.

End Foo.

Crane Extraction "Foo" Foo.
```

Mappings are type-class instances that activate on `Import`, so import them
(`From Crane Require Import ...`); a bare `Require` loads a mapping file
without using it. `Mapping.Std` maps `option`, pairs, strings and Rocq's
primitive integers and floats to the C++ standard library. Here `nat` has
no mapping, so Crane generates a Peano `Nat` type; import
`Mapping.NatIntStd` instead to extract `nat` as `uint64_t` (bounded, so only
for values that fit). [Crane Base Library](Crane-Base-Library.md) lists the
mapping sets.

You can also extract a single definition instead of a module:
`Crane Extraction "fac" Foo.fac.` extracts the function with all its
dependencies.

Now run:

```bash
rocq compile Example.v && clang++ -c -std=c++2c -I<crane>/theories/cpp Foo.cpp -o Foo.o
```

This writes `Foo.h` and `Foo.cpp` (in the current directory unless
`Set Crane Extraction Output Directory` or `-output-directory` says
otherwise), then compiles the C++ to `Foo.o`, ready to be linked with your
own C++ file containing `main`.

The `-I` is needed because generated code includes Crane's runtime headers:
`small_vector.h` and `crane_fn.h` here, and depending on what you extract
also `rc.h`, `lazy.h`, `persistent_array.h`, `crane_string.h` and others.
They are header-only and live in `theories/cpp` in the Crane checkout
(`theories/cpp_bde` for BDE builds); they are not installed onto the system
include path, so point `-I` at that directory or copy the headers into your
project.

Next: the [Reference Manual](Reference-Manual.md) for every command and
option, and [Examples](Examples.md) for larger programs.
