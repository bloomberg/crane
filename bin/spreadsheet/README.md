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

The script runs three steps: a `dune build` of the Crane plugin and
theory dependencies, a direct `rocq compile` that produces
`_build/spreadsheet_gen/Spreadsheet.{h,cpp}` from the kernel, and a
CMake configure + build that produces the final ImGui binary.

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
  (cells, expressions, sheet, evaluator).  Crane extracts this to
  `Spreadsheet.h` / `Spreadsheet.cpp`.
* `bin/spreadsheet/formula.{h,cpp}` — recursive-descent parser that
  produces `Spreadsheet::Expr` values from typed strings.  Parsing is
  not part of the verified kernel.
* `bin/spreadsheet/main.cpp` — GLFW + OpenGL3 + Dear ImGui front-end.
  Owns a single `Spreadsheet::Sheet`, mutates it via `set_cell`, and
  reads evaluated values via `eval_cell` every frame.
