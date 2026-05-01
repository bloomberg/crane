# Crane Spreadsheet Demo

A small spreadsheet application: a Rocq-extracted kernel (formula AST,
copy-on-write sheet, fuel-bounded evaluator) driven by a Dear ImGui
front-end.

## Build

```bash
# From the project root:
./bin/spreadsheet/build.sh
./_build/spreadsheet/spreadsheet
```

The script runs `dune build` (which extracts `Spreadsheet.{h,cpp}` next
to this README via the local `dune` coq.theory) and then a CMake
configure + build that links the front-end binary.

CMake uses `FetchContent` to download Dear ImGui (v1.91.5) at configure
time, so no submodule setup is required.

System dependencies: `cmake`, GLFW 3 (`libglfw3-dev` on Debian/Ubuntu),
OpenGL development headers (`libgl-dev`), and a recent C++ compiler.

## Usage

* Click a cell and type a number to set a literal.
* Type `=A1+B2` or `=(A1+B1)*7` to enter a formula.
* Operators: `+ - * /`, parentheses, decimal integers, cell references
  in `<column letter><1-based row>` form (`A1`, `Z99`).
* Empty input clears the cell.
* Cycles, division-by-zero, and out-of-fuel show as `#ERR`.

## Architecture

* `theories/Examples/Spreadsheet/Spreadsheet.v` — the Rocq model
  (cells, expressions, sheet, fuel-bounded evaluator) and a handful
  of theorems about it (closed smoke value, empty/literal cells,
  self-cycle and division-by-zero diverge to `None`).
* `bin/spreadsheet/Spreadsheet.v` — extraction wrapper that re-imports
  the model and emits `Spreadsheet.h` / `Spreadsheet.cpp` next to the
  C++ sources via the local `dune` coq.theory.
* `bin/spreadsheet/formula.{h,cpp}` — recursive-descent parser that
  produces `Spreadsheet::Expr` values from typed strings.  Bounds-aware:
  refs outside the grid are rejected at parse time.
* `bin/spreadsheet/main.cpp` — GLFW + OpenGL3 + Dear ImGui front-end.
  Owns a single `Spreadsheet::Sheet`, mutates it via `set_cell`, and
  reads evaluated values via `eval_cell` every frame.

A regression test of the kernel lives at
`tests/basics/spreadsheet/spreadsheet.t.cpp`; it runs under
`dune build @tests/basics/spreadsheet/runtest`.
