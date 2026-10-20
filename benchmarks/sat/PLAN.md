# SAT benchmark: Crane vs. OCaml extraction of direct-style ITrees

Status: working prototype with preliminary numbers. Staging steps 1–3 are
done: fuel-outs abort, `vec` is a record, **SAT soundness is proved**
(`SolverSat.v`, `solve_sat_sound`) and **UNSAT soundness is proved**
(`SolverUnsat.v`, `solve_unsat_sound`). Both rest only on the axiom
`eq_rect_eq`. Memory safety (step 4) and I6 (step 5) remain.
Branch: `joom/refactor`.

## Goal

Show that Crane's erased ("direct style") ITree extraction is much faster
than stock OCaml extraction of the same ITree program, on a realistic
workload: a CDCL SAT solver whose mutable state is all accessed through ITree
events. Then make the solver trustworthy, ideally with a full correctness
proof in Rocq.

## Starting points that were considered

- `~/ParaCDCL`: a 1.9k-line dependently typed CDCL development. It builds
  under Rocq 9.0 with deprecation warnings only. It is not usable as a
  benchmark:
  - variables are `string`s;
  - partial assignments are functions `V -> option bool`;
  - the top-level algorithm is built with tactics and closed with `Qed`.

  Extracted, it is a chain of closures. `src/rproof.v` (resolution proofs) may
  still be useful for the proof work.
- `~/SATurne`: a small list-based splitting procedure, `resolve`, that
  enumerates *all* solutions, so it is exponential by construction. It also
  builds under Rocq 9.0. `src/Proof.v`, a verified resolution-proof checker,
  is a candidate for the certificate fallback (see below).

Decision: write our own solver directly in `itree vecE`.

## Layout

| File | Role |
|---|---|
| `SatVec.v` | `vec A`, a phantom-typed record around a `loc := nat`, and the `vecE` effect: `VMake n x`, `VGet v i`, `VSet v i x`, `VLen v`, `VPush v x`, `VShrink v n`, `VAbort site`; smart constructors `vmake`/`vget`/.../`vabort` via `embed` |
| `VecSem.v` | Layer 0: relational heap semantics `step`, finite runs `runs`, partial-correctness `wp`, and the rules for `Ret`, `bind` and each event |
| `SolverSat.v` | SAT soundness: the input spec `encodes`/`satisfies`, the frame invariant, `check_model_spec`, and `solve_sat_sound` |
| `SolverRepr.v` | Layer 1: the abstract state `astate`, `repr` (heap ↔ abstract state, separation as one `NoDup`), and a `wp` rule per event in abstract terms |
| `SolverInv.v` | Layer 2: the invariants `Core`/`Wch`/`Seen0` (against a fixed model `val`), their preservation lemmas, and the first-UIP analysis invariant `AInv` |
| `SolverUnsat.v` | Layer 3: `wp` specs for every solver function, the initialization glue, and `solve_unsat_sound` |
| `Solver.v` | the CDCL solver, module `Solver`, entry point `Solver.solve` |
| `CraneVec.v` | Crane mappings: `vec` → `satbench::vec<T>`, events → method calls, `vabort` → `satbench::abort<T>(site)` |
| `sat_vec.h` | `satbench::vec<T>`: `shared_ptr<std::vector<T>>`, so vectors are reference-semantics handles; `abort` throws `out_of_fuel`, which the driver reports as UNKNOWN |
| `SolverCrane.v` | `Set Crane Loopify. Set Crane SharedVariant. Crane Extraction "solver" Solver.` || `OcamlNat.v` | native-int realizers for the `nat` ops used (so OCaml doesn't pay for Peano arithmetic) |
| `SolverOcaml.v` | stock OCaml extraction of `Solver.solve` (real ITree, lazy `Go`/`RetF`/`TauF`/`VisF` nodes) |
| `vec_impl.ml`, `itree_run.ml` | OCaml growable arrays; the cheapest possible ITree interpreter (force, handle event, continue; no `interp`) |
| `SolverOcamlDirect.v`, `direct.ml` | control: stock OCaml extraction with the tree erased by hand (`itree E R := R`, `bind m k := k m`, events → direct `Vec_impl` calls) |
| `solver_main.cpp`, `dimacs.h`, `solver_main.ml`, `solver_direct_main.ml`, `solver_main_common.ml` | DIMACS drivers |
| `gen.py` | instance generator: uniform random 3-SAT (`rand3 n ratio seed out`), pigeonhole PHP(n+1,n) (`php n out`) |
| `build.sh` | dune-extract, then compile everything into `build/` |
| `run.sh` | time every binary on every `inst/*.cnf`, median of `REPS` (default 3), write `results.csv` |
| `summarize.py` | markdown table and geomean slowdowns from `results.csv`; asserts all builds agree |
| `inst/` | the current suite: php7, php8, r100_2, uf150_{1,2,3,4,6,7,8}, uf175_{3,4} |

`dune` declares the `SatBench` theory with output going to `out/`. It is not
part of the test suite; build it with `dune build benchmarks/sat`.

## Solver design (`Solver.v`)

- Encoding: variable `v` has literals `2v` (positive) and `2v+1` (negative).
  - `lneg`: flip the low bit.
  - Variable values: 0 = unassigned, 1 = true, 2 = false.
  - `lit_value` returns the same codes for a literal.
- State: a record of `vec` handles:
  - `clauses : vec (vec nat)` is the DB. Input clauses are `[0, norig)`.
    Invariant: a reason clause has its implied literal at position 0.
  - `watches : vec (vec nat)`, per literal: the clauses watching it at
    position 0 or 1.
  - Per variable: `assigns`, `level`, `reason` (clause index + 1, 0 = none),
    `phase`, `stamp`, `seen`.
  - `trail`, `trail_lim`.
  - `misc`: 0 = queue head, 1 = conflicts, 2 = restart limit,
    3 = conflicts since restart.
- Algorithm:
  - two-watched-literal propagation (`prop_watch`, `find_watch`, `copy_rest`,
    `propagate`);
  - first-UIP learning (`analyze_lits`, `next_seen`, `analyze_loop`,
    `finish_learnt`);
  - non-chronological backjumping (`backtrack`/`unassign`) with phase saving;
  - decisions: the unassigned variable with the latest conflict stamp, found
    by linear scan (`pick`; VMTF-like);
  - geometric restarts (limit ×1.5, starting at 100);
  - no clause deletion.
- Loops: every loop is a `Fixpoint` on a `fuel : nat` argument (the driver
  passes 2^61/2^62). Running out of fuel performs `vabort site` (numbered
  1–15), which has no semantics, so an aborted run has no result and
  carries no proof obligation. C++ throws and OCaml raises; the drivers
  catch it and print UNKNOWN. `search` uses a separate step `budget`. With Loopify, all
  16 fixpoints become `while (true)` loops in C++. Without Loopify the C++
  overflowed the stack: the by-value `shared_ptr` argument blocks tail calls
  under the Itanium ABI.
- Input: a flat `vec nat` of `[len, lits...]*`, built by the driver, so no
  list conversion is needed on either side.
- Input validation: `solve` first checks, in Rocq, that `ninput <= |input|`
  and that `input[0, ninput)` is a list of length-prefixed clauses whose
  literals are all `< 2 * nvars` (`valid_clauses`/`valid_lits`), and
  answers 4 otherwise. The solver body is `run`. `solve_wp` (SolverSat.v)
  lifts any property of `run` on validated input to `solve` on any input.
- Result: `code + 8 * conflicts`, where `code` is:
  - 1: SAT, with the model checked in Rocq by `check_model` against every
    clause of the caller's `input` vector (not the database, whose clauses
    propagation reorders in place);
  - 3: SAT, but the model failed that check (never observed);
  - 0: UNSAT;
  - 2: out of budget;
  - 4: invalid input (rejected by the validator).

## Methodology

- Only the `solve` call is timed: `steady_clock` in C++, `Unix.gettimeofday`
  in OCaml. Extraction, compilation, parsing and input construction are
  excluded.
- C++: `scripts/compile-std.sh` (Homebrew clang, libc++, `-std=c++2c`),
  `CRANE_CPP_OPTIMIZATION=O2` by default. `build/solver_cpp_O3.exe` was built
  by hand for the O3 comparison.
- OCaml: 5.4.1 `ocamlopt -unsafe -inline 200` (default switch, no flambda),
  plus flambda `-O3 -unsafe -inline 200` builds from a separate opam switch,
  `sat-flambda` (compiler + ocamlfind only), producing `*_fl.exe`.
- Machine: Apple M4 Pro (14 cores); every run is single-threaded.
- Correctness cross-checks:
  - every build gives the same answer *and the same conflict count* on every
    instance, so the search is identical;
  - SAT models are checked in Rocq;
  - z3 (`z3 -dimacs`) agrees on all UNSAT instances checked (r50_1, r100_2,
    php6, php7).

## Preliminary results (not for publication)

Quick grid: 4 instances (php7, r100_2, uf150_2, uf150_3). Median of 3 runs
for C++ and the erased OCaml, a single run for the ITree builds. Geomean
slowdown relative to Crane C++, with the range in parentheses:

| | vs Crane C++ `-O2` | vs Crane C++ `-O3` |
|---|---|---|
| OCaml ITree (stock extraction + interpreter) | 83.2× (78–90) | 82.6× (79–88) |
| …same, flambda `-O3` | 81.1× (76–87) | 80.4× (77–85) |
| OCaml, ITree erased by hand | 6.3× (6.2–6.5) | 6.2× (6.2–6.3) |
| …same, flambda `-O3` | 3.6× (3.5–3.8) | 3.6× (3.4–3.7) |

Example absolute times (C++ `-O2` / OCaml ITree): php8 0.52s / 44.7s;
uf150_1 0.27s / 21.6s.

Reading:
- `-O3` adds nothing over `-O2` for the C++.
- About 13–14× of the gap is reifying and interpreting the tree; flambda
  can't remove it.
- The remaining 3.5–6× is the residual C++ vs OCaml cost on the
  already-erased program. That combines the shape of the extracted OCaml
  (closures for every `nat` match and every bind, `reSum` dictionaries) with
  the OCaml runtime (polymorphic `Obj.t` arrays, the write barrier on stores,
  tagged ints).
- If the write-up needs those two parts separated, the next control is a
  hand-written OCaml solver.

## Environment notes and gotchas

- **`effect` keyword.** The refactor branch didn't build on OCaml ≥ 5.3,
  where `effect` is reserved. CI pins 4.14, so it was never noticed. The
  identifier was renamed to `effect_` in `src/{core_effects.ml,.mli,
  move_check.ml, pipeline_trace.ml,.mli, recursion_plan.ml, extract_env.ml}`.
  The rename is uncommitted and probably wants its own commit.
- `make build` fails on `theories/Libraries/ParseALot` (needs CoLoR, which
  isn't installed). It is irrelevant here: `dune build theories/Monads
  theories/External theories/Mapping` is enough.
- **Stale plugin outside dune.** `rocq c`/`coqc` run by hand load the *stale
  opam-installed* plugin (`rocq-crane.plugin` 2bd18a0-dirty), because Rocq
  puts `~/.opam/default/lib` first on its ML path, whatever `OCAMLPATH` says.
  This causes anomalies (`Not_found` in `Libobject.load_object`) or unknown
  commands. Build through dune (which uses `-boot`) or reinstall the plugin.
- **`vectorE` copies.** Crane's own `External/Vector.v` maps `vector` to a
  plain `std::vector` *value*, so a vector passed to a function is copied and
  mutations aren't shared. That's why this benchmark has its own handle-based
  `vecE`.
- `%t0` in an inlined-constant template for a `Context {E} ...` smart
  constructor is the erased effect parameter (rendered as `void`). Use
  deducing helpers such as `make_vec(n, x)`.
- A Rocq definition named `main` makes Crane emit `int main()`.
- `Set Crane SharedVariant` is a no-op here: the C++ output is byte-identical,
  because no recursive inductive appears at runtime. It is kept on anyway.
- `Set Crane Reuse` and `Set Crane NonAtomicRc` are effectively no-ops too.
  They were tried and the variant files deleted.
  - Reuse: byte-identical output, and it is disabled under Loopify anyway.
  - NonAtomicRc: adds only `#define CRANE_NON_ATOMIC_RC 1` and
    `#include "rc.h"`; the function bodies are identical.
  - Timings (median of 5) are within noise of the baseline.
  - The atomic refcount traffic that *does* exist is in our own `sat_vec.h`
    `shared_ptr`, which these flags don't touch.

## Known issues to fix in the implementation

1. ~~**Fuel-out defaults are unsound.**~~ Fixed: every fuel-out is
   `vabort site`.
2. ~~**Result overflow on the OCaml side.**~~ Fixed in the drivers: the step
   budget is 2^58 (at most one conflict per step), so
   `code + 8 * conflicts < 2^62`.
3. **`shrink` semantics differ.** `satbench::vec::shrink` uses `resize`, which
   *grows* when `n > len`; `Vec_impl.shrink` is a no-op then. All current
   calls have `n ≤ len`. The proof's semantics should only define
   `n ≤ len`.
4. **Unchecked indexing.** `get`/`set` are unchecked on both sides (C++
   `operator[]`, OCaml `-unsafe`). Out-of-bounds is undefined behaviour in
   C++. The proof must establish in-bounds access, or the header should
   assert in debug builds. With well-formed input every access is believed
   in bounds (argument in "Stage 4 plan"), but this is not yet proved.
5. ~~**The drivers do not validate input.**~~ Partly fixed: `solve`
   validates the flat encoding in Rocq (code 4), so out-of-range literals and
   malformed length prefixes can no longer reach the solver. Still open:
   `nvars` comes from the driver unchecked (`p cnf -1 0` makes both drivers
   allocate until killed), and the lenient parsers can produce a different
   formula than the file (the SATLIB `%`/`0` trailer becomes an empty clause;
   junk tokens are skipped in C++; an unterminated last clause is dropped).
   Stage 4 moves parsing into Rocq. Original text: `read_dimacs` (`dimacs.h`) and
   `solver_main_common.ml` never check literals against the `p cnf` header.
   A literal with `|x| > nv`, a missing header (`nv = 0`), or a final clause
   without its terminating `0` produces input outside `encodes`/the
   well-formedness precondition. The solver then indexes `assigns`/`watches`
   out of bounds: undefined behaviour in C++ and memory-unsafe in OCaml
   built with `-unsafe`. The theorems do not cover this, because stuck runs
   satisfy every `wp` vacuously. Fix: reject such files in both drivers
   (exit with an error, don't print UNKNOWN). This is the first item of
   stage 4.

## Tuning ideas

- **Decisions:** replace the linear scan in `pick` with a binary heap or a
  VMTF queue in `vec`s.
- **Clause deletion:** add it, e.g. by LBD or by activity, with periodic DB
  reduction.
- **Cheaper handles:** `satbench::vec` copies an *atomic* `shared_ptr` on
  every clause visit (`s.clauses.get(ci)`). A non-atomic handle
  (`crane::rc`?) or a raw-pointer handle into an arena would cut refcount
  traffic. Check whether Crane can bind such reads by `const&`.
- **Restarts:** Luby restarts instead of geometric.
- **Bigger instances:** a larger suite, e.g. SATLIB uf200/uuf200 or SAT
  Competition "easy" instances, for the final numbers.
- **Final run:** `REPS=5`, on a quiet machine.

## Stage 1–2 log (2026-10-20)

- **`vec` as a record, not a definition.** With `Definition vec A := loc`,
  stock OCaml extraction unfolds `vec int` and `vec Obj.t` to the same
  `int`, leaves out the `Obj.magic` between them, and the realized
  `'a Vec_impl.t` then fails to typecheck. `Record vec A := mk_vec { vloc :
  loc }` stays a type constructor of its own. Both extractions now map it
  with `Extract Inductive`.
- **Side effect on the C++.** Under an `Extract Inductive` mapping, Crane
  passes `satbench::vec` by `const&` rather than by value. That removes
  `shared_ptr` refcount traffic on every call: about 5–12% faster on the
  suite (single runs, load ≈ 17), with identical answers and conflict counts.
  The `O3` binary and any published numbers need a rerun.
- **Crane bug found (not fixed).** A *nullary* inlined constant of type
  `itree E unit` in tail position of a void function is treated as pure
  and dropped: an argument-less `vabort` became a bare `return;`. Giving
  `vabort` a `site` argument avoids it. The likely culprit is the
  `CPPglob … ci_inline` case of `cofix_wrap` in `src/gen_functions.ml`.
  Needs a regression test.
- **Proof of SAT soundness.**
  - `solve_sat_sound`: if `solve` finishes with `r mod 4 = 1` from a heap
    where `input` holds an encoding of `F` (`encodes xs ninput 0 F`), then
    `F` has a model.
  - Only axiom: `Eqdep.Eq_rect_eq.eq_rect_eq` (via `inj_pair2`, when two
    reads of one cell are compared).
  - The search-side obligation is a frame: every write goes to a location
    other than `input`, `clauses` and `watches`. The cells of the last two
    only ever hold such handles, and `assigns` stays a nat cell. One
    `*_fr` lemma per loop, each proved by the `fr_go` stepping tactic.
- **Limitation of untyped cells.** A cell is `{A : Type & list A}`, and
  `existT nat ys = existT (vec nat) ws` cannot be refuted (`vec nat` might
  be `nat`), so typing never separates locations: every separation fact
  must be an explicit disequality. A type-code universe as in
  `theories/Monads/STMonad.v` (cells indexed by a code, `V : T -> Type`,
  here just `nat` and `vec nat`) would fix this and remove the axiom, at
  the price of re-stating `step` over codes.
- **`theories/Monads/STMonad*.v` as a reference.** It has a functional
  handler into `stateT` via `interp_state`, and equational
  `interp_st_{ret,vis,tau,trigger,bind}` lemmas under `≅`/`≈`. It has no
  Hoare layer and no proofs about looping programs, which is what the
  solver needs, so `runs`/`wp` stay. If the result should be stated in
  that style, an adequacy lemma `runs h t r h' ↔ interp_vec t h ≈ Ret (h',
  r)` can bridge the two.

## Stage 3 log (2026-10-20)

- **Result.** `solve_unsat_sound`: if `solve` finishes with `r mod 4 = 0`
  from a heap where `input` holds `encodes xs0 ninput 0 F`, then no valuation
  satisfies `F`. `Print Assumptions` shows only `Eqdep.Eq_rect_eq.eq_rect_eq`,
  the same as `solve_sat_sound`. About 3.2k lines across `SolverRepr.v` (650),
  `SolverInv.v` (1380) and `SolverUnsat.v` (1195). `Solver.v` is unchanged, so
  the extractions and benchmark numbers are unaffected.
- **Heap representation: kept untyped cells.** A type-code universe would only
  separate `nat` cells from `vec nat` cells. Nearly all the separation Stage 3
  needs is between cells of the *same* type: clause vs. clause, clause vs.
  `assigns`, watch list vs. clause. So it would have cost a rewrite of
  `VecSem.v`/`SolverSat.v` and bought little, except removing the axiom.
  Instead `repr` carries one `NoDup` over `[input; clauses; watches]`, the nine
  field locations, every clause handle and every watch handle. Each write then
  changes exactly one component of the abstract state (`repr_fset`,
  `repr_dset`, `repr_wset`, `repr_cpush`, ...). Vectors outside that list (the
  learnt clause while it is built, a clause while `load` reads it) are scratch
  cells, and `keeps` says that state writes leave them alone.
- **Abstract state.** `astate` holds clause handles and contents, watch
  handles and contents, and the nine fields as a function `fv : fld -> list
  nat`, so one lemma per event kind covers all nine fields. Nested `fset`s
  are not convertible to a single `fset`, and there is no funext. Results of
  loops that write several fields (`unassign`, analysis) are therefore stated
  as field-wise agreement (`unas`, `only_sn`, `bt_rel`), not as equations.
- **Fixing a model instead of an abstract CDCL system.** The proof fixes a
  `val` with `satisfies val F` and shows that `search` never answers 0 and
  `load` never answers false. "Entailed by `F`" becomes "true under `val`", so
  no resolution proofs or transition system are needed. ParaCDCL's `rproof.v`
  went unused. Resolution steps in the analysis become: the marked variable
  `val` disagrees with is either the one being popped (then its reason clause
  has another `val`-true literal) or stays marked.
- **Surprise: the plan was wrong about I6.** It claimed a reported conflict is
  all-false whatever I6 says. `prop_watch` never reads `c[1]`'s value: for
  unit/conflict it assumes `c[1] = fl`. When re-homing, `vset c 1 ck; vset c k
  fl` overwrites `c[k]` instead of swapping, which is a permutation only if
  `c[1] = fl`. So soundness needs watch membership. With duplicate literals
  (allowed in the input, e.g. `[a, b, a]`) a clause can sit in one watch list
  twice. The invariant is therefore a count: `cnt watches[l] ci ≤
  expect db ci l`, with `≤` so the stale region of an in-place compaction
  needs no exact bookkeeping. It is proved for the *logical* list
  `ws[0,j) ++ ws[i,n)` during `prop_watch`. The `ck ≠ fl` fact needed when
  pushing onto `watches[ck]` follows from `ck` not being false while `fl` is.
- **Invariants actually used (`Core`).** DB true under `val`; values ≤ 2;
  trail lists exactly the assigned variables, once each, all true; the level
  of a trail position is `count_le lim k` (the number of decisions at or
  before it), with `lim` sorted; `lim ≤ qhead ≤ |trail|`; reasons have their
  literal at 0 and every other literal false and *earlier on the trail*;
  reason-less literals are decisions (`k ∈ lim`) or before the first
  decision; level-0 literals are true under `val`. `qhead ≥` the last
  decision is what guarantees a conflict clause has a current-level literal,
  so `pathC ≥ 1` in the first analysis round.
- **Analysis (`AInv`).** Marks are counted over trail *positions*, `cntm`, so
  the trail's NoDup makes "the variable at position k" a bijection.
  `pathC = cntm marks base (index+1)`; every current-level mark is at a
  position ≤ `index`; lower-level marks are exactly the learnt literals.
  `next_seen` never saturates at 0 because a marked position ≥ `base` is
  below `index`. When `pathC ≥ 2` the popped literal is above `base`, so
  `i_dec` gives it a reason (`reason_exists`). When `pathC ≤ 1` the
  remaining marks are all learnt (`ainv_final`), so `finish_learnt` clears
  every mark.
- **Gotcha: never `cbn in *` with heaps in context.** `cbn` unfolds `upd`
  chains of concrete heaps and runs for minutes: one `cbn in *` in
  `finish_learnt_sp` made the file take over 9 minutes instead of seconds. Keep `cbn` restricted to
  named constants (`fvs` = `cbn [fv fset dset wset cpush wpush fld_eqb ...]`)
  or to specific hypotheses. Also `lvar`, `lneg`, `lval`, `lset` are
  `simpl never` in `SolverInv.v`, so use the `lset_cons*` rewrite lemmas.
- **Gotcha: section variables.** Lemmas in a `Section` only take the section
  hypotheses they use (`ainv_init` takes no `val`/`Core`, `finish_learnt_sp`
  no `now`/`Core`). Use `eapply` or `About` before applying them positionally.
- **Still trusted / not proved:** memory safety (step 4: in-bounds indices,
  live handles; stuck runs currently satisfy every `wp` vacuously); the
  "2WL implies" half of I6 (step 5); bounds of `nat` values below 2^62; and
  everything in Layer 4.

## Stage 4 plan: memory safety

Goal: with well-formed input, no run of `solve` gets stuck. Every event it
performs has a `step`, so in-bounds indexing and live handles are guaranteed
by the semantics `sat_vec.h`/`vec_impl.ml` are trusted to implement. Today
the theorems are partial correctness only: a run that would index out of
bounds simply has no `runs` derivation and satisfies every `wp` vacuously.

**Precondition (to state and use).** `wf_input xs0 ninput nvars F`:
`encodes xs0 ninput 0 F`, and every literal of `F` is `< 2 * nvars`. Also
`ninput <= length xs0`, which `encodes` already implies for the positions
it reads. Duplicate and complementary literals within a clause stay allowed;
the soundness proof already handles them.

**Step 0: drivers (known issue 5).** Make both DIMACS readers reject
literals with `|x| > nv`, a missing header, and an unterminated last clause,
so that every input the solver sees satisfies `wf_input`. Rebuild with
`./build.sh` and rerun the cross-check (same answers and conflict counts).

**Step 1: a safety judgement.** Add to `VecSem.v` something like
`safe h t Q`: coinductive, or inductive over finite prefixes. Every reachable
`Vis e k` has some `x, h'` with `step h e x h'`, except `VAbort`, which is
allowed (it is the intended give-up). Every finished run satisfies `Q`.
Derive the same rules as for `wp` (`ret`, `bind`, `conseq`, one per event,
each now with an obligation that the step exists: index `< length`, `n <=
length`, handle allocated at the right type). Option: replace `wp` by
`safe` entirely, since a total-correctness-minus-termination `wp` subsumes
the current one, and re-run the existing proofs through it. Decide by
checking how much of `SolverRepr.v`'s event lemmas changes: they already
receive the bound (`i < length xs`) as a *hypothesis* from `wp_vset`, and
would instead have to *prove* it.

**Step 2: the extra invariants.** All are cheap on top of `Core`/`Wch`/`AInv`:
- the vector lengths are fixed: `assigns`, `level`, `reason`, `phase`,
  `stamp`, `seen` have length `nvars`; `watches` and `hwl`/`wl` have length
  `2 * nvars`; `misc` has length 4;
- every database literal is `< 2 * nvars`: input clauses by `wf_input`;
  learnt literals because each is the negation of a trail literal, and
  trail literals come from clauses or from `lit_of v _` with `v < nvars`;
- every watch-list entry is `< |db|`, and every watched clause has length
  `>= 2`. Both follow from `Wch` (`expect` is 0 otherwise);
- `phase` values are in `{1, 2}` (written from `assigns` of assigned vars;
  initially 2), so `lit_of` gives a literal of `v`.
  This one is cosmetic, since `lit_of` works for any value.

**Step 3: per-access obligations (checklist).** Each should be discharged
by facts already proved in Stage 3 or by step 2:
- `lit_value`, `enqueue`, `unassign`, `analyze_lits`, `finish_learnt`: `lvar l
  < nvars` for literals from clauses or the trail;
- `vget (watches s) l`, `attach`: `l < 2 * nvars`;
- `prop_watch`: `ws[i]` with `i < n = |ws|` (guard); `clauses[ci]` with `ci <
  |db|` (watch entries); `c[0]`, `c[1]` with `|c| >= 2` (watched); `c[k]` for
  `2 <= k < len` (`find_watch`); `vset ws j` with `j <= i < n`; `vshrink ws j`
  and `copy_rest` with `j <= |ws|`;
- `propagate`: `trail[qh]` guarded by `qh < |trail|`; `misc[QHEAD]`;
- `backtrack`: `trail_lim[lvl]` guarded by `lvl < dl`; `vshrink trail lim`
  with `lim <= |trail|` (`i_limq`, `i_qtr`); `vshrink trail_lim lvl`, with
  `lvl < dl`;
- `next_seen`: `trail[i]` with `i <= index < |trail|`. The `index - 1`
  saturation never matters, because a marked position `>= base` lies below
  `index` (`AInv`, `ainv_pop`);
- `analyze_loop`: `clauses[r - 1]` with `r >= 1` when `pathC' >= 2`
  (`reason_exists`) and `r - 1 < |db|` (`i_rsn`). The conflict index comes
  from `conflict`;
- `learn`: `vset learnt 0` (length 1 after `vmake 1 0`); `finish_learnt`'s
  `learnt[best]`, `learnt[1]` with `1 < best < len`;
- `search`: `phase[v]` with `v < nvars` from `pick`; `misc[1..3]`;
- `load`, `read_lits`, `check_model`, `clause_sat`: input positions in range
  by `encodes`. `c[0]` for unit clauses, length 1;
- `solve`: `vset m RLIMIT` with `|m| = 4`; `fresh_vecs` pushes `2 * nvars`
  handles (this needs the `length W' = n` fact that `fresh_vecs_sp` does not
  currently state).

**Step 4: theorem.** `solve_safe`: under `wf_input` (and `h0 input = xs0`),
`safe h0 (solve ...) (fun _ _ => True)`. Ideally combine the three results
into one statement: safe, and on termination the answer is correct for both
SAT and UNSAT.

**Out of scope for stage 4 but worth noting:** `nat` values stay below 2^62
(drivers' budgets; the conflict and stamp counters are bounded by the
budget), and the `shrink`/`resize` difference (known issue 3), which is
harmless once `n <= length` is proved for every shrink.

**Cheap empirical check, any time:** build `sat_vec.h` with bounds
assertions, or `-fsanitize=address,undefined`, and run the suite. Also run
a few malformed files to confirm the step-0 driver checks fire.

## Correctness proof sketch

Target theorem, for well-formed input encoding CNF `F` over `nvars`
variables (every literal `< 2*nvars`, length prefixes consistent with
`ninput`):

> If `solve fuel budget nvars input ninput`, run from a heap where `input`
> holds the encoding, terminates with result `r`, then:
> - `r mod 4 = 1` ⇒ the final assignment satisfies `F`;
> - `r mod 4 = 0` ⇒ `F` is unsatisfiable;
> - (optional) `r mod 4 ≠ 3`;
> - and no event along the run is stuck (in-bounds indices, live handles).

This is partial correctness plus memory safety. Termination is not needed:
`search` is budgeted, and an exhausted budget answers 2.

### Layer 0: semantics of `vecE`

`vec` is an axiom, so give the events a **relational** heap semantics rather
than a handler function. A heap is a finite map from locations to
`{A : Type & list A}`. A handler would need decidable type equality to answer
`VGet {A}`; a relation fixes `A` by the pattern.

- Make `vec A` a definition (`vec A := loc`, `loc := nat`) instead of an
  axiom. Both extractions override it anyway (Crane:
  `Extract Inlined Constant vec`; OCaml: `Extract Constant vec`), so the
  extracted code is unchanged. Check this.
- `step : heap -> vecE X -> X -> heap -> Prop`, one rule per event:
  - `VMake` allocates a fresh location;
  - `VGet`/`VSet` require `i < length xs`;
  - `VShrink` requires `n ≤ length xs`.
- `runs : heap -> itree vecE R -> R -> heap -> Prop` is inductive over
  finitely many `RetF`/`TauF`/`VisF` unfoldings, using `observe`.
- Derive a small Hoare/WP logic over `runs`:
  - rules for `Ret`, `bind` (including the `ITree.bind` unfolding lemmas from
    the ITree library) and each event;
  - a frame rule over disjoint locations;
  - a **safety** judgement: every reachable event has a `step`.

  Alternatively, phrase it as `interp` into `stateT heap (failT ...)` and
  reason with `eutt`. The relational version avoids type casts and is likely
  simpler.

### Layer 1: representation / abstraction

An abstraction relation `repr h s σ` relates a heap and a `state` record to
an abstract solver state `σ`:

- `σ` contains the clause DB `list (list lit)`, the original clause count
  `norig`, an assignment as a partial map, the trail as a list of
  `(lit, level, reason)`, the queue head, the watch lists `lit -> list nat`,
  and the `seen`/`stamp`/`phase` contents.
- Separation: all `state` handles are distinct, every clause vector is
  distinct from every other vector, and every watch vector is distinct (from
  each other and from the clause vectors). `fresh_vecs` and the freshness of
  `VMake` establish this.
- The key aliasing fact used by `prop_watch`: when it pushes onto
  `watches[ck]`, `ck ≠ fl` (`ck` is not false, `fl` is), so that vector is
  not the `ws` being iterated.

### Layer 2: invariants on `σ`

- **I1, well-formedness.** Literals `< 2*nvars`. Stored clauses of length ≥ 2
  have pairwise-distinct variables. Learnt clauses have this by construction
  (`seen`); input clauses need a precondition, or I1 is relaxed for them and
  only the 2WL invariant depends on it.
- **I2, trail consistency.**
  - The trail lists exactly the assigned literals, each variable once, all
    true under `assigns`.
  - `trail_lim` is strictly increasing and bounded by `|trail|`; `level[v]`
    is the decision segment of `v`'s position.
  - `qhead ≤ |trail|`.
- **I3, reasons.** `reason[v] = ci + 1` ⇒ clause `ci` has `v`'s trail
  literal at position 0, and every other literal is false and earlier on the
  trail (so its level is ≤ `level[v]`). Decisions and level-0 units have
  reason 0.
- **I4, entailment.** Every DB clause is entailed by `F = DB[0, norig)`.
  Learnt *units* are not stored: their literal sits on the trail at level 0
  and is covered by I5.
- **I5, level-0 entailment.** Every level-0 trail literal is entailed by
  `F`.
- **I6, watched literals (only for "never BADMODEL" and completeness).**
  - Every stored clause of length ≥ 2 occurs in `watches[c0]` and
    `watches[c1]`, and nowhere else.
  - For trail positions `< qhead`: if a watched literal is false, the other
    watched literal is true, or every non-watched literal is false and the
    other watched literal is true (the standard 2WL invariant with respect to
    the propagation queue; cf. IsaSAT).

~~UNSAT soundness needs only I1–I5 plus local facts.~~ Wrong: see the Stage 3
log. `prop_watch` never reads the value of `c[1]`; it relies on `c[1]` being
the literal just made false. So UNSAT soundness also needs the *membership*
half of I6, in counting form (`Wch`): a clause occurs in `watches[l]` at most
as often as it has `l` at position 0 or 1. The "2WL implies" half is still
only needed for "never BADMODEL" and completeness.

### Layer 3: per-function specifications (WP style)

- **`lit_value`, `decision_level`:** pure readers of `σ`.
- **`enqueue l r`:** requires `l` unassigned; extends the trail at the
  current level; preserves I2. It preserves I3 if `r` is a valid reason, and
  I5 if the level is 0 and `l` is entailed.
- **`find_watch`:** returns the first index ≥ 2 holding a non-false literal,
  or none.
- **`copy_rest`:** the slice-move lemma.
- **`prop_watch`.** Loop invariant on `(i, j)`:
  - the watch list is `ws[0, j) ++ ws[i, n)`, as a multiset, minus the
    clauses re-homed to other lists;
  - each processed clause is satisfied, re-homed, unit (and enqueued with a
    valid reason, with the implied literal at position 0), or the returned
    conflict;
  - the returned conflict is all-false under the current assignment;
  - the clause swaps preserve the clause *as a set*, so I4 holds.
- **`propagate`:** preserves I1–I5. It returns an all-false clause, or 0
  with `qhead = |trail|` (and with I6, no unit or false clause is pending).
- **`unassign`, `backtrack lvl`:** restore I2 and I3 for the prefix up to
  `trail_lim[lvl]`; set `qhead := lim`. Phases are irrelevant to soundness.
- **First-UIP analysis** (`analyze_lits`, `next_seen`, `analyze_loop`,
  `finish_learnt`). Loop invariant over the current resolvent `R`:
  - `R` is the current-level marked literals not yet resolved, plus
    `learnt[1, len)`;
  - `R` is entailed by the DB, obtained by resolving the conflict clause with
    reason clauses (each step uses I3 and the I4 entailment of the reason);
  - every literal of `R` is false;
  - `seen` marks exactly the variables of `R` plus the already-resolved
    current-level variables, which are cleared as they are popped;
  - `pathC` is the number of current-level literals in `R`;
  - `index` is above every marked current-level trail position.

  Safety: `next_seen` finds a marked variable before running off the trail,
  so the `index - 1` saturation never hits 0 while `pathC > 0`. On exit,
  `p` is the UIP; the learnt clause `¬p ∨ learnt[1..]` is entailed, which
  gives I4. Its other literals are below the current level, and
  `finish_learnt` puts one of maximal level at position 1, returns that
  level, and clears `seen`.
- **`learn`:** after `backtrack bt`, the learnt clause is unit, with `¬p`
  unassigned and every other literal false. Storing and attaching it
  preserves I4 and I6 (`c0` unassigned, `c1` false at the highest remaining
  level). Enqueueing `¬p` with that reason satisfies I3. If the clause is
  unit, the enqueue is at level 0 and preserves I5 (entailed by I4 reasoning
  on the resolvent).
- **`pick`:** returns 0 ⇒ every variable is assigned; otherwise it returns an
  unassigned variable.
- **`search`.** Invariant: I1–I5 (and I6).
  - `Ret 0` only on a conflict at level 0. Every literal of the conflict
    clause is false at level 0, so its complement is entailed by I5, and the
    clause itself is entailed by I4. Hence `F ⊨ ⊥`.
  - `Ret 1` when no conflict remains and every variable is assigned.
  - Restarts are `backtrack 0`.
- **`load`:** establishes `DB = F` with `norig` input clauses, I2–I5 at
  level 0 (unit input clauses are enqueued with reason 0, and are entailed
  trivially), and I6 for attached clauses. It returns false only on an empty
  input clause or a unit whose literal is already false (`F` contains `l` and
  `¬l`), both of which make `F` unsat.
- **`check_model`:** now walks the caller's `input`, not `DB[0, norig)`.
  It returns true only if every clause there has a true literal. Decoding
  `assigns` (unassigned → false) gives a valuation satisfying `F`. Proved
  as `check_model_spec`. Together with the frame (`input` is never written),
  it gives the SAT half; no solver invariant is involved.

### Layer 4: what stays trusted

- Crane's translation and the C++ toolchain. Crane is unverified; the theorem
  is about the Rocq program.
- That `sat_vec.h` and `vec_impl.ml` implement `step`. Points to audit:
  shared handle aliasing, fresh allocation on `make`, `shrink` only for
  `n ≤ len` (see known issue 3), and `uint64_t`/OCaml `int` versus `nat`.
- Bounding all `nat` values below 2^62 (fuel, budget, counters, `4 *
  conflicts`). Each needs a small lemma, or the driver chooses bounds.

### Staging (suggested)

1. ✅ Fix known issue 1 (fuel-outs abort). `vec` is a record (not a
   definition, see the log). Extractions are unchanged except the abort sites
   and, in C++, `const&` handle parameters.
2. ✅ Layer 0 semantics and WP rules, the `check_model` spec and the frame
   invariant, which give **SAT soundness** (`SolverSat.v`).
3. ✅ Layer 1 plus I1–I5 (and watch membership), and the specs for `enqueue`,
   `propagate`, `backtrack`, `analyze`, `learn`, `search` and `load`, which
   give **UNSAT soundness** (`SolverRepr.v`, `SolverInv.v`, `SolverUnsat.v`).
4. Memory safety: all events in bounds, all handles live. See
   "Stage 4 plan" below.
5. Optional: I6, which gives "never BADMODEL" (completeness of propagation).

Prior work to borrow structure from:
- Fleury, Blanchette, Lammich, *A verified SAT solver with watched literals
  using Imperative HOL* (CPP 2018), part of IsaSAT;
- Blanchette, Fleury, Lammich, Weidenbach, *A verified SAT solver framework
  with learn, forget, restart, and incrementality* (JAR 2018);
- Oe, Stump, Oliver, Clancy, *versat* (SAT 2012).

A clean route is to refine the imperative code to an abstract CDCL
transition system (Propagate / Decide / Conflict / Backjump / Learn /
Restart), prove soundness once for the abstract system, and prove a
simulation from Layer 1. ParaCDCL's `rproof.v` and CDCL transition specs
might be reusable for the abstract layer.

### Fallback: certified UNSAT without verifying the solver

Have `learn` log each learnt clause to a `vec` (a DRUP-style trace), and
check the trace with a *verified* RUP checker in Rocq: each clause follows
by unit propagation from `F` plus the earlier clauses, and the trace ends in
the empty clause. SATurne's verified resolution checker (`src/Proof.v`) is a
possible base. Together with the `check_model` SAT half, this certifies
every answer, with much less proof effort. The checker can be extracted with
Crane as a second benchmark.
