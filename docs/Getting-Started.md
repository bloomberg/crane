# Getting Started

## Installation

Once you clone the repo, if you have [opam](https://opam.ocaml.org/) and [dune](https://dune.build/), you can run

```bash
opam install . --deps-only
```

To install OCaml (at least 4.14.0) and Rocq (at least 9.0.0). You can then build and install the project by running

```bash
make build && make install
```

You will also need [Clang](https://clang.llvm.org/) 19 or higher to run the tests, and [clang-format](https://clang.llvm.org/docs/ClangFormat.html) for standard formatting.

To run the tests, use:

```bash
make test              # Run all tests
make test-one TEST=list  # Run a single test
```

To run the `Crane Benchmark` command, you will need to have [hyperfine](https://github.com/sharkdp/hyperfine) installed.

## C++ extraction

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
rocq compile Foo.v && clang++ -c -std=c++23 Foo.cpp -o Foo.o
```

This command creates `Foo.h` and `Foo.cpp` files from the Rocq file, and then compiles the C++ to the object file `Foo.o` with Clang, ready to be linked to your own C++ file containing a `main` function for execution.

---

## Go extraction

Crane supports extracting Rocq programs to Go. The workflow is the same as C++ extraction, but you import `Crane.Mapping.GoStd` instead of `Crane.Mapping.Std`.

### Minimal example

```coq
(* Collatz.v *)
From Crane Require Extraction.
From Crane.Mapping Require GoStd.

Fixpoint collatz (n : nat) : nat :=
  match n with
  | O | S O => n
  | S (S _ as n') =>
    if Nat.even n
    then collatz (Nat.div2 n)
    else collatz (S (S (S (Nat.mul 3 n))))
  end.

Crane Extraction "collatz" collatz.
```

```bash
rocq compile Collatz.v   # produces collatz.go
go build collatz.go
```

### What `GoStd` provides

Importing `Crane.Mapping.GoStd` does two things:

1. Sets the extraction language to Go (`Crane Extraction Language Go`).
2. Registers standard mappings for the most common Rocq types:

| Rocq type        | Go type                      | Notes                              |
| ---------------- | ---------------------------- | ---------------------------------- |
| `bool`           | `bool`                       | `true` / `false` literals          |
| `unit`           | `struct{}`                   | `struct{}{}` for the value         |
| `option A`       | `*A`                         | `nil` for `None`                   |
| `prod A B`       | `struct{ fst A; snd B }`     | `.fst` / `.snd` projections        |
| `nat`            | (structural, via tagged struct) | Use `PrimInt63` for performance  |
| `PrimInt63.int`  | `int64`                      | 63-bit masked arithmetic           |
| `PrimFloat.float`| `float64`                    | Requires `math` import             |
| `PrimString.string` | `string`                  | `cat`, `get`, `sub`, `length`      |

### Representation of Rocq types in Go

**All-nullary inductives** (enums) become `type T int` with a `const (... = iota)` block:

```go
// Rocq: Inductive color := Red | Green | Blue.
type color int
const (
    Red   color = iota
    Green
    Blue
)
```

**General inductives** become a tagged-struct pair — a private impl struct holding a discriminant `_v int` and all constructor fields, plus a public pointer alias:

```go
// Rocq: Inductive nat := O | S (n : nat).
type natImpl struct {
    _v   int
    _c1_d0 nat   // S's argument
}
type nat = *natImpl

func O() nat           { return &natImpl{_v: 0} }
func S(a0 nat) nat     { return &natImpl{_v: 1, _c1_d0: a0} }
```

**Polymorphic types** use Go generics. Type variables are numbered `T1`, `T2`, … :

```go
// Rocq: Inductive list (A : Type) := nil | cons (x : A) (xs : list A).
type listImpl[T1 any] struct { _v int; _c1_d0 T1; _c1_d1 list[T1] }
type list[T1 any] = *listImpl[T1]
```

**Pattern matching** compiles to an immediately-invoked function expression (IIFE):

```go
// Rocq: match n with O => m | S n' => S (add n' m) end
(func() any {
    _scrut1 := n
    switch _scrut1._v {
    case 0:
        return m
    case 1:
        n_ := _scrut1._c1_d0
        return S(add(n_, m))
    }
    panic("unreachable")
})()
```

For all-nullary (enum) types the switch uses the constructor name directly:

```go
switch _scrut1 {
case Red:
    return true
default:
    return false
}
```

### Custom mappings for Go

You can override any Rocq type or constant with a Go expression using the same `Crane Extract` family of commands used for C++. The template placeholders are identical:

```coq
Crane Extract Inlined Constant Nat.add => "(%a0 + %a1)".

Crane Extract Inductive option =>
  "*%t0"
  [ "%a0" "nil" ]
  "func() any { if %scrut != nil { %b0a0 := %scrut; return %br0 } else { return %br1 } }()".
```

All mappings from `GoStd` can be overridden by re-issuing `Crane Extract` commands after importing `GoStd`.
