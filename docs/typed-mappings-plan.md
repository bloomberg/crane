# Typed Custom Mappings: implementation plan

**Design:** `docs/typed-mappings-design.md` (normative semantics).  
**Branch:** `typed-mappings`, forked from `main` at `b54509ddc`.  
**Status:** plan; milestones are checked off in this file as they land.

This plan turns the design into ordered, independently landable milestones,
grounded in the code at `b54509ddc`. It records where the code forces a
mechanical choice the design leaves open, and what is deliberately deferred.

## 1. What the code looks like today

The facts below come from a survey of the pinned commit; file references are
relative to the repository root.

**Mappings are untyped text keyed by GlobRef.** Commands in
`src/g_extraction.mlg` (`Crane Extract Inductive/Inlined Constant/Constant/
Numeral/Skip/Monad/Void`, `Crane TriviallyCopyable`) fill `Summary.ref` tables
in `src/base/table.ml` through `superglobal` libobjects, so they are persisted
in `.vo` files and activate on `Require` (not `Import`). The main table is
`customs : GlobRef -> (string list * string)` (one string per reference: a type
template for an inductive, a term template for a constant), plus
`custom_matchs`, `ref_imports` (headers), `inline_table`, `boxed_wrappers`,
`custom_drains`, `numeral_table`, and two `TriviallyCopyable` sets (one of them
keyed by C++ head *strings*, so declaring `prod` marks every `std::pair`).
There are about 940 mapping declarations (656 in `theories/`, 211 in `tests/`,
70 in `benchmarks/` and `libraries/`). About 40 modules read the tables directly
through `is_custom`/`find_custom`/`is_inline_custom` (roughly 300 call sites).

**Templates.** `src/cpp_ir/foreign_template.ml` parses the hole vocabulary
(`%tN %aN %ret %result %scrut %brN %bIaJ %elem %ty`) into four memoized
categories; drains (`%yield`) and numerals (`%n`) have their own mini-syntaxes.
Several modules still inspect template text directly (`calls.ml:301` regex for
`%aN`, `ctor_args.ml:154`, `lambda_params.ml:178`, `inductives.ml:2084`,
`demands.ml:177`, `table.ml:3817`, `cpp_integer_range`).

**Mapped types stay structured until late.** Lowering turns a mapped type into
`Type.Entity_application (g, tys, vals)` (`core_to_cpp/types.ml:213`); it only
becomes `Type.Foreign` (opaque text pieces with typed holes) in
`Cpp_passes.Erasure.instantiate_foreign` (`erasure.ml:~680-814`), pipeline pass
`"foreign"`. That seam is where a structured mapped type can be produced
instead of text.

**Printing is textual.** `pp_cpp_type` (`emit/print.ml:432-640`) prints
`Const t` as `"const " ^ t`, `Pointer t` as `t ^ "*"`, `Reference (Lvalue, t)`
as `t ^ "&"`, and `Foreign` by splicing text. `Const (Pointer t)` therefore
prints pointer-to-const. `Method_value` adapters hard-code `"const T &"`
(`print.ml:780`).

**Parameter mode is a type shape.** The single decision point is
`Core_to_cpp.Ownership.wrap_param_by_ownership` (`core_to_cpp/ownership.ml:
178-192`): `Reference (Lvalue, Const t)` when lent and borrowed, else `t`. A
custom inductive is lent unless an enum or a "custom scalar" (a hard-coded C++
word list); a custom type constant is always by value. At least six sites
recover the mode by pattern-matching the type shape
(`core_to_cpp/ownership.ml:16`, `ownership_ir/move_check.ml:371`,
`cpp_passes/return_moves.ml:14`, `control_to_cpp/tail.ml:68-104`,
`cpp_passes/constraints.ml:89`, `functions.ml:910`). `Callable_abi.passing`
(`Owned | Borrowed | Forwarded`) sits beside the signature and is matched in six
places. Lifted helpers (`lifting.ml:271-296`) bypass the wrapper.

**Ownership.** `src/core_plan/ownership.ml` is a bool-per-parameter fixed
point; custom constants are skipped (no callee flags), so an argument passed to
a mapped constant is assumed only read. Region ownership is derived from the
declared C++ type (`functions.ml:1442-1449`), not from the flag.

**Call sites rebuild types from Core.** `gen_call_args`
(`application.ml:163-430`) takes each argument's expected type from the
callee's Core type; `Call.params`, `crane::fn` signatures and concepts are all
canonical. Argument passing also happens in control lowering (frames, loop
continues), `Tail` shadows, `Frame_storage`, `Lambda.forwarded`, and
`Shared_args`.

**Rocq side.** The plugin never resolves type classes or decodes Rocq data
today (it only queries `Typeclasses.is_class`/`class_info`). Rocq 9.1 provides
`Typeclasses.instances_exn`, `all_instances`, `Class_tactics.resolve_one_typeclass`,
`Reductionops.nf_all`, `Pstring.to_string`. `driver/benchmark.ml:68-134`
(`validate_subject`) is the best existing template for reading a constant and
checking its type. Mappings are consulted *during* Rocq-to-Core translation and
dependency collection (`extract_env.ml:419-456`, `extraction.ml:1351,1521,2092`),
so discovery must finish before `mono_environment`.

## 2. Decisions the code forces

**D1. Two-stage discovery.** Type-class resolution needs a concrete type, but
dependency collection needs to know *which heads are mapped* before it walks
bodies. So:
1. At extraction `init`, enumerate the instances of `TypeMapping` and
   `OperationMapping` (`Typeclasses.instances_exn`) and record each instance's
   *head*: the head GlobRef of `T`, or the referenced declaration in
   `Ref source`. A head with a new-style instance is treated as mapped by the
   same predicates the legacy tables answer (`is_custom`, body skipping).
2. When a concrete instantiation is first needed (lowering a mapped type or
   call), resolve the dictionary for that instantiation, `nf_all` it while
   keeping `Ref` arguments unreduced, decode it, validate it, compile it, and
   cache it by (head, instantiation) in a `State.Extraction` cell.
Ambiguity: for a concrete instantiation, try every recorded instance with that
head; if more than one unifies, report all candidates. Instance priority is
never consulted.

**D2. Strings in descriptors are `PrimString.string`.** Primitive strings
normalise to `Constr.String` leaves and decode with one `Pstring.to_string`;
`Strings.String.string` would need a new constructor-chain decoder. Mapping
files already use `PrimString`.

**D3. Compile into the existing seams, keep legacy consumers working.** A
compiled type mapping is stored in a new table (not `customs`). The
roughly 300 legacy call sites keep asking `is_custom g`; that predicate
answers true for a new-style head too, and the places that need *content*
(type spelling, constructor templates, match templates, headers, copy cost,
lending) get a typed query that consults the compiled plan first and the legacy
table second (design §22.5). Lowering keeps producing
`Entity_application (g, ...)`; `Erasure.instantiate_foreign` turns a new-style
head into a *structured* CppIR type built from the compiled `TypeExpr`, never
into text. The `Foreign` path stays for legacy mappings.

**D4. The parameter mode becomes explicit data.** A view parameter
(`std::span<T>`) breaks every site that reads the mode off the type shape. The
mode is therefore recorded in `Callable_abi` (extending `passing` to carry
ownership, access and representation, plus the physical form and the
conversion needed at call sites), and the six shape-matching sites read it
from there. This is done before any view is introduced, with no change in
generated code.

**D5. Activation.** New standard instances are `#[export]`, so they activate
on `Import`, as the design requires. About 200 tests reach today's mappings
with a bare `Require` (no `Import`); they keep working while those mappings
are legacy. When a standard mapping file migrates (M7), its users get an
`Import` in the same commit. Until then nothing changes for them.

**D6. Declarator printer first.** The printer fix is independent and needed by
every later milestone, so it lands first, with no change to any existing
output except where today's output is wrong.

## 3. Milestones

Each milestone ends with a gate: `make build`, the milestone's own tests, the
affected test folders, and, at the milestones marked **full suite**, one full
`make test` compared with `main`. Generated outputs are regenerated and
committed in the milestone that changes them. Every new user-visible behaviour
gets a regression test under `tests/regression/` (or `tests/monadic/` for ST).

### M1. Declarator-correct C++ types (design §5.5, phase 1)
- Rewrite `pp_cpp_type` around a declarator hole so `Const`, `Pointer` and
  `Reference` bind at the right level: `Const(Pointer T)` is `T* const`,
  `Pointer(Const T)` is `const T*`, references wrap the declarator.
- Replace the textual `"const T &"` in the `Method_value` adapter with a
  structured type.
- Unit-test the printer on the design's list (`T*`, `const T*`, `T* const`,
  `T*&`, `T* const&`, `const T*&`, `const std::shared_ptr<T>&`,
  `std::span<const T>`, `std::span<T>`).
- Expect no change in existing generated output (no current type reaches the
  printer as `Const (Pointer _)` except through `Foreign` text). **Full suite.**

### M2. Descriptor library and discovery (design §§5-11 data, §10, phase 2)
- Add `theories/Mapping/Descriptor.v` with every inductive and record of the
  design (`Declaration`, `Cpp.TypeExpr`, models, views, components,
  constructors, numerals, `TypeMapping`, operation types, `OperationMapping`),
  constructors and records only.
- Add `src/base/mapping_descriptor.ml` (or a new directory `src/mapping/`
  placed so `scripts/check-module-deps.sh` accepts it, after `base/` and
  before `rocq_to_core/`): the OCaml mirror of the descriptor types, the
  decoder from normalised `EConstr` terms, and validation (design §19).
- Discovery as in D1: head registration at `init`, lazy per-instantiation
  resolution with ambiguity detection, `State.Extraction` cache.
- Tests: a golden mapping file using only constructors and records (§24.2);
  import selection with two incompatible mapping modules (§24.1: A only, B
  only, both = ambiguity naming both); every descriptor validation error of
  §24.12 that is checkable at this stage.

### M3. Type mappings in the pipeline (design §§4, 6, 8, 9, phase 3)
- Compiled type plans: components and `StoredComponent` substitution, copy,
  access, value and lifetime models, constructor mappings (build, test,
  projections), release plans.
- `Erasure.instantiate_foreign`: new-style heads become structured CppIR
  types.
- Typed queries replacing direct reads where content matters: lending
  (`core_lent_by_reference`, `names_value_inductive`), copy cost
  (`is_trivially_copyable_type`, `copies_cheaply`, `worth_moving_ref`,
  `boxes_field`), constructor and match lowering
  (`construction.ml`, `match.ml`, `inductives.ml`), headers
  (`get_custom_imports`).
- Lifetime validation: raw pointer + `NativeRAII` rejected.
- Tests: a new-style mapping of a small user inductive (algebraic interface,
  build and match), an abstract new-style type, copy-model-driven passing
  (`BitCopy` by value, `DuplicateValue` by `const&`, `CopyComponents` both
  ways).

### M4. Operation mappings (design §11, phase 4)
- Discovery of `OperationMapping (Ref source)`; binding named arguments to the
  retained runtime binders after erasure; `%arg(name)` holes alongside `%aN`.
- Compiled contracts (`InputUse`, `ResultSpec`, `OperationFact`, purity) with
  the validation rules of §19.6.
- Lowering a call to a new-style operation through the existing inline-call
  path (template expansion at the `"foreign"` seam), with single evaluation of
  each argument in source order (§11.9), replacing the text-based counting in
  `Shared_args` for new-style operations.
- Feed `Take`/`RetainsArgument` into the ownership fixed point as callee
  flags for mapped operations (today they have none).

### M5. Explicit parameter modes and the access fixed point (design §12, phase 5)
- D4 first: carry the mode in `Callable_abi`, switch the six shape-matching
  sites and `Move_check` to it. No output change. **Full suite.**
- Then the access/representation lattice beside ownership
  (`src/core_plan/access.ml`): uses from mapped operations, direct calls,
  locals, constructors and projections; summaries per generated function.
- Physical parameter selection (§12.5) for new-style types without views:
  canonical read / write-through / replace / take forms from the access model
  (§6.6).
- Call sites: thread the callee's planned mode into `gen_call_args`, control
  lowering, `Tail`, `Frame_storage` and `Shared_args`.
- First-class functions keep canonical ABIs (§12.9).

### M6. ST arrays and references without views (design §13, phase 7 first half)
This milestone fixes the reported bug.
- `STArray` as `shared_ptr<vector<A>>`, `MutableHandle HandleByConstReference`,
  `NoViews`, `NativeRAII`; `newArray`/`newListArray` via `make_shared`;
  `readArray` (`Read`), `writeArray` (`Write`), `getElems` (`Read`) contracts.
- `STRef` likewise (design §13.13).
- Tests: a helper that reads and writes one cell extracts as its own function
  taking `const std::shared_ptr<std::vector<T>>&` (no inlining); `swapArray`
  likewise; the `outer -> middle -> writeArray` chain; mixed requirements
  (retain gives by value, replace gives `&`); `nat` and `bool` arrays; the
  test-only raw-pointer mapping (§24.8); LSan on `st_*` and `union_find`.
- Rewrite `st_quicksort` and `union_find` to use separate per-operation
  functions instead of one unfolded batch, now that helpers can take arrays.
  **Full suite.**

### M7. Views (design §7, §12.7-12.8, §14, phase 6 and phase 7 second half)
- `ReadViews` / `ReadWriteViews`, `MaterialiseView` / `BorrowOnly`, view
  selection for `Read`/`Write`, canonical bypass, declared conversions at call
  sites, owner provenance for borrowed results, `InvalidatesElementBorrows`
  vs `InvalidatesViews`.
- The `vector<bool>` decision (design §14.9): recommended option 1, a Crane
  array-storage wrapper in `theories/cpp/` whose `bool` instantiation stores
  addressable elements, so one span-enabled `STArray` mapping is valid for
  every element type.
- Span-enabled `STArray`: `swapArray` takes `std::span<T>`.
- String views: a new-style `PrimString.string` mapping with a
  `std::string_view` read view and the operations of §14.2-14.5.
- Tests of §24.4, §24.5, §24.6, §24.7. **Full suite.**

### M8. Standard mappings, interfaces, and deprecation (design §§15-17, 20, 22, phase 8)
- Migrate `Std.v` (`option`, product, string, int63, float) and then the number
  mappings to descriptors, file by file, adding `Import` where users relied on
  bare `Require` (D5). Each file migrates in its own commit with its outputs.
- Numeral descriptors replace `Crane Extract Numeral` for migrated types.
- Compiled interfaces (§20): record the selected instance and physical ABI of
  every mapped head a unit uses beside `claim_extracted_unit`; a consumer that
  resolves differently gets a mismatch diagnostic.
- Exact-number mapping example (`cpp_int`, §16) as a test, not a default.
- Deprecation warnings for the legacy commands only once a migrated equivalent
  exists for every standard use.

## 4. Deliberately deferred

- `RegionOwned` lifetime implementation (a `runST`-owned region); M6 uses
  `NativeRAII` with `shared_ptr` and documents that cycles are not collected.
- Migrating the roughly 870 mapping declarations outside `Std.v` and the number
  mappings (BDE, Real, monad mappings, test-local mappings). They keep working
  through the legacy path.
- View ABIs for first-class function values (§12.9 future work).
- `ExplicitAccess` / `ExactParameter` / `UnsafeVerbatim` are decoded and
  validated (with the diagnostics the design requires) but no standard mapping
  uses them.

## 5. Risks

- **Discovery cost.** Resolving instances per instantiation could be slow on
  large programs; the per-(head, instantiation) cache bounds it, and heads
  without instances cost one table lookup.
- **Normalisation losing `Ref` identity.** `nf_all` would unfold the declaration
  inside `Ref d`. The decoder must stop at `Ref` (reduce the descriptor with a
  strategy that does not unfold `Ref`'s argument, or read the argument before
  reducing).
- **Mode threading touches ownership-critical code** (frames, `Tail`,
  `Move_check`). M5 lands the explicit-mode refactor alone, behind a full suite
  with no output change, before any new mode exists.
- **Legacy/new coexistence.** A head mapped both ways is an error (design
  §22.5) unless a migration option allows the new one to win; tests cover it.

## 6. Findings during implementation

- **M1.** The assumption that no type reached the printer as `Const (Pointer _)`
  was wrong: `Const (Reference _)` was used to mean reference-to-const (the
  `v()`/`lazy_cell()` accessors, erased `std::any` parameters) and
  `Const (Pointer _)` to mean pointer-to-const (the loopify receiver
  `_loop_self`). Those producers now build `Reference (Lvalue, Const t)` and
  `Pointer (Const t)`, and `CRANE_CHECK_IR` rejects `Const (Reference _)`. Once
  the receiver was typed `Pointer (Const T)`, passes that chose borrowed-shadow
  rewriting by matching `Pointer _` started rewriting it; they now use
  `Tail.borrowed_pointer_shadow`, which excludes the receiver *by name*. M5's
  explicit parameter modes (D4) must replace that name test with data.
- **M5 (first part, D4).** The mode is `Cpp_ir.Param_mode.t`
  (`src/cpp_ir/param_mode.ml`, type in `grammar.ml`): ownership
  (`Owned | Borrowed | Forwarded`), form (`By_value | By_const_value |
  By_const_reference | By_forwarding_reference | By_reference`) and role
  (`Value | Receiver`). `By_reference` exists only so that reading a
  declaration back (`Param_mode.spelled`) is total; no producer plans it.
  It is recorded in `Callable_abi.modes` (replacing `passing`) and, by
  parameter name, in a `modes` field of `Function`, `Method` and `Lambda`
  (local fixpoints; closures record none). `Region.Local_passing` keeps
  only ownership, because it is decided before the lambda's form is.
  Loopify's receiver gets `Param_mode.receiver`, and Tail's shadows are a
  `Tail.Shadow.t` whose `hold` (`Value | Through_pointer | Receiver`)
  replaces the name test. `Move_check.check_modes` checks recorded modes
  against declared types, both after lowering and before printing, and
  `param_modes` reports a parameter with no recorded mode where one is
  read. Two listed sites are not parameter-mode readers: `return_moves.ml`
  reads only local declarations, and `constraints.ml` derives the C++ value
  category of a name, a property of its declared type. Constraints now
  reads a parameter's mode where one is recorded; locals, constructors and
  closures still use their declarations. Frame captures are locals, so
  their mode is `spelled` from the declaration.
- **M2.** Descriptor field positions count from 0 after the family parameters.
  `Crane Show Mapping` and `Crane Check Mapping ... Selects | Unmapped | Fails
  With` are the test hooks; `CRANE_TRACE_MAPPINGS=1` traces discovery.
- **Infrastructure.** `scripts/loopify-census.sh` fails on a rerun in an
  existing worktree (stale `_build/census`: dune does not rebuild a sibling
  `.vo` after the script deletes it); `rm -rf _build/census` before `make test`.

## 7. Progress

- [x] M1 declarator-correct types
- [x] M2 descriptor library and discovery
- [ ] M3 type mappings in the pipeline
- [ ] M4 operation mappings
- [ ] M5 explicit parameter modes and access fixed point
- [ ] M6 ST arrays and references without views
- [ ] M7 views
- [ ] M8 standard mappings, interfaces, deprecation
