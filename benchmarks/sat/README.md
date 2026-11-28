# SAT benchmark: a verified imperative ITree program, Crane C++ vs OCaml

A CDCL SAT solver written in Rocq as an ITree program over Crane's
`Global` arrays and references (`theories/Monads/Global.v`), extracted by
Crane to C++ and by stock extraction to OCaml, timed on DIMACS instances,
and proved sound against `Global`'s model.

## Layout

| File | Role |
|---|---|
| `Solver.v` | the solver, module `Solver`; entry point `Solver.solve_dimacs` |
| `SolverCrane.v` | Crane extraction (`Set Crane Loopify`) to `out/SatBench/solver.{h,cpp}` |
| `SolverOcaml.v`, `sat_rt.ml` | stock OCaml extraction to `out/solver_ml.ml`: the tree erased (`itree E R` is `R`, `bind` is application), `Global` arrays as OCaml arrays, the arena reference as an OCaml reference, `nat` as `int` |
| `solver_main.cpp`, `solver_main.ml` | drivers: read the file's bytes, call `solve_dimacs`, print `names[r mod 8]`, `r / 8` (conflicts) and the time of that call |
| `Cnf.v` | formulas in the solver's encoding: `lit_true`, `satisfies`, `lits_below` |
| `DimacsSpec.v` | the accepted DIMACS language, `dimacs bs F`; `Solver.parse` proved sound, complete and deterministic against it |
| `Abstract.v` | the abstract solver state the proofs reason about |
| `Sem.v` | relational semantics of the solver's effects through `Global`'s handler; `safe`, its rules, and the bridge to `Global.interp` |
| `Inv.v` | invariants of the abstract state (trail, levels, reasons, watches, first-UIP analysis, capacities) and their preservation |
| `Repr.v` | which abstract state a pair of `Global` stores holds; one rule per kind of write |
| `SolverSpec.v` | one `safe` specification per solver function, from `lit_value` to `search` |
| `SolverMain.v` | loading, model check, `run`, and the top-level theorem `solve_dimacs_correct` with its model-level corollary `solve_dimacs_model` |
| `build.sh` | dune-extract and check the proofs, compile into `build/` |
| `run.sh` | time each build on each `inst/*.cnf`, median of `REPS` (default 3), write `results.csv` |
| `summarize.py` | markdown table and geomean slowdown from `results.csv`; asserts the builds agree on answers and conflict counts |
| `check_bad.sh`, `inst_bad/` | malformed and edge-case DIMACS files with expected answers (`inst_bad/expected.txt`), run on every build including the ASan/UBSan one |
| `gen.py` | instance generator: uniform random 3-SAT, pigeonhole PHP(n+1, n) |
| `inst/` | the suite: php7, php8, r100_2, uf150_{1,2,3,4,6,7,8}, uf175_{3,4} |

`dune` declares the `SatBench` theory, output in `out/`. It is not part of
the test suite.

```
./build.sh            # solver_cpp.exe, solver_cpp_checked.exe (ASan/UBSan), solver_ml.exe
./check_bad.sh        # edge cases, every build
REPS=5 ./run.sh       # timings -> results.csv
python3 summarize.py
```

## The solver

- Encoding: variable `v` has literals `2v` and `2v+1`; a value is 0
  (unassigned), 1 (true) or 2 (false).
- State (`Solver.state`), all `Global` arrays of `nat` unless noted:
  - the clause arena, in a `Global.ref`: one record `[len; lits...]` per
    clause, a clause named by its offset; it moves to storage twice as
    large when a learnt clause does not fit;
  - per literal, a watch list of clause offsets (`wdata`, an array of
    arrays) with its length (`wlen`) and capacity (`wcap`), moved to
    storage twice as large (+4) when full;
  - per variable: `assigns`, `level`, `reason` (offset + 1, 0 for none),
    `phase`, `stamp`, `seen`;
  - `trail` and `trail_lim` (capacity `nvars`) and `learnt` (capacity
    `nvars + 1`), with their lengths in `misc`;
  - `misc`: queue head, conflicts, restart limit, conflicts since restart,
    and the lengths above.
- Algorithm: two-watched-literal propagation, first-UIP learning,
  non-chronological backjumping with phase saving, decisions on the
  unassigned variable with the latest conflict stamp (linear scan),
  geometric restarts (limit x1.5 from 100), no clause deletion.
- Loops over a known count recurse on that count; `propagate`,
  `next_seen` and `analyze_loop` take fuel and `search` a step budget.
  Out of fuel is `Solver.out_of_fuel`, a `failwith`: C++ throws and OCaml
  raises, and the drivers print UNKNOWN.  With Loopify every loop is a
  C++ `while` loop.
- `solve_dimacs fuel budget bytes nbytes` reads the bytes into a list,
  parses them with the pure, tail-recursive `parse`, sizes the arena for
  the formula, loads its clauses, searches, and checks a model against the
  parsed formula.  The variable count is the largest variable the formula
  mentions, not the header's.
- Result `code + 8 * conflicts`: 1 SAT (model checked), 3 SAT but the check
  failed (never observed), 0 UNSAT, 2 out of budget, 4 not a DIMACS CNF
  file.

## What is proved

`SolverMain.solve_dimacs_correct`: from any pair of `Global` stores in
which `bytes` holds the file `bs`, `solve_dimacs` is `safe` (`Sem.v`): no
reachable configuration performs an access `Global`'s handler rejects, the
program's only failure is "out of fuel", and every finished run returns
`r` with `answer bs r`.  `solve_dimacs_model` restates this for the
two-layer `Global.interp` itself: every run of the model either fails with
`Error "out of fuel"` or returns `r` such that

- `r mod 8 = 4` exactly when `bs` is not a DIMACS CNF file
  (`DimacsSpec.dimacs`);
- `r mod 8 = 1` only if the formula `bs` spells is satisfiable;
- `r mod 8 = 0` only if it is unsatisfiable.

The model fails on every out-of-range array index and every missing cell,
so this also says that no access is ever out of bounds; the extracted code
does not check indices (C++ `operator[]` on a span, OCaml `-unsafe`).
Termination is not claimed: the budget turns a long search into answer 2.

Structure: one specification per function carries, together, the safety
invariant `SI`, `Core None` (the structure of the trail, levels and
reasons, on every input) and `Inv (Some val)` for every model `val` of the
formula, so memory safety and UNSAT soundness come from one pass.  SAT
soundness needs only the model check against the parsed formula.  The
proofs rest on the axiom `eq_rect_eq` (for `inj_pair2`); `Print
Assumptions` also lists the primitive `PrimString.string`, the type of the
failure message.

Trusted: Crane's extraction and C++ runtime, OCaml extraction and
`sat_rt.ml`, and that machine integers do not overflow (the drivers pass
fuel 2^62 / 2^61 and a budget of 2^58, at most one conflict per step).

## Methodology

- Only the `solve_dimacs` call is timed (`steady_clock`,
  `Unix.gettimeofday`), parsing included; extraction, compilation and
  reading the file are not.
- C++: `scripts/compile-std.sh` (clang, libc++, `-std=c++2c`), `-O2`.
- OCaml: 5.4 flambda, `ocamlopt -O3 -unsafe -inline 200`.
- Every build gives the same answer and the same conflict count on every
  instance, so the search is identical.
