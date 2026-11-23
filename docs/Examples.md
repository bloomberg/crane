# Examples

The [`tests`](https://github.com/bloomberg/crane/tree/main/tests) directory
holds Rocq programs with the C++ Crane generates from them, committed beside
each source, and a C++ test driver (`*.t.cpp`) that runs it. The tests are
organized by theme:

- [`tests/basics`](https://github.com/bloomberg/crane/tree/main/tests/basics):
  functional programs (lists, trees, modules, functors, type classes).
- [`tests/monadic`](https://github.com/bloomberg/crane/tree/main/tests/monadic):
  effects (IO, STM, threads, interaction trees) and the `ST` monad
  (`st_arrays`, `st_array_helpers`, `st_quicksort`, `st_refs`).
- [`tests/regression`](https://github.com/bloomberg/crane/tree/main/tests/regression):
  regression tests for fixed issues, including the typed mapping tests
  (`typed_mapping_algebraic`, `typed_mapping_operations`,
  `typed_mapping_access`, `typed_mapping_selection`, `string_views`, ...).
- [`tests/wip`](https://github.com/bloomberg/crane/tree/main/tests/wip):
  known defects and experimental features, most with a comment in the `.v`
  file describing the failure.

`make test-list` lists every test; `make test-one TEST=<name>` extracts,
compiles and runs one.

## Larger examples

- [`theories/Libraries/ParseALot`](https://github.com/bloomberg/crane/tree/main/theories/Libraries/ParseALot):
  a verified lexing-and-parsing pipeline (a Verbatim++ lexer and a CoStar++
  parser) extracted to C++, built as the `Crane.Libraries.ParseALot` theory.
  [`libraries/parse-a-lot-bench`](https://github.com/bloomberg/crane/tree/main/libraries/parse-a-lot-bench)
  is its benchmark harness, comparing the extracted C++ with the OCaml
  extraction of the same source; its extraction computes the lexers' DFA
  tables at extraction time with [`Crane Bake`](Reference-Manual.md#crane-bake).
- [`theories/Examples/ConcurrentHashTable.v`](https://github.com/bloomberg/crane/blob/main/theories/Examples/ConcurrentHashTable.v):
  a concurrent hash table built on Crane's STM effects.
