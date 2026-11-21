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
- **M3.** A plan is compiled once per mapped head (`Base.Mapping_plan`),
  from the instance resolved at the head applied to fresh named variables,
  one per binder of its arity; a type argument of a use stands for the
  variable it instantiates. So a component's logical type must be one of the
  head's parameters (`KnownType A`, `SourceType A`, or a `FieldType` declared
  at one): a closed component type (`KnownType nat`) and an instance for one
  particular instantiation (`TypeMapping (T nat)`) are refused with a
  diagnostic for now. `is_custom`/`to_inline` answer true for a mapped head
  and its constructors, so the ~300 legacy call sites, body skipping and kind
  inference need no edit; the content readers in `Table` (`find_custom*`,
  `inline_custom_text`, `find_custom_match`, `find_custom_ctor_templates`,
  `imports_of`) consult the plan first. Constructor and match templates are
  compiled into the legacy hole vocabulary (`%stored(x)` becomes `%tN`, the
  views become one `if (test) { binders %brI } else ...` template), so
  construction and match lowering are unchanged; `%tmpN` is refused there.
  For the text-reasoning heuristics, a head's `find_custom` is its canonical
  type in legacy spelling; the type itself is structured in
  `Erasure.instantiated_type`. A structured type no longer names its head,
  so instantiation records the head (`note_instantiated`) and its headers are
  added to the unit's imports (per extraction, not per unit). The
  `constexpr` fixed-point check re-runs the pass after instantiation, so
  `is_literal_type` must read a mapped head as its structured type before
  instantiation too. Release plans (`DrainWith`) and value/lifetime models
  are compiled but not yet consumed; `WithBody` builds compile to a legacy
  block template (`%result = init; body`) and are untested.
- **M4.** The binders of an operation's type are classified as
  `Extraction.flag_of_type` classifies them
  (`Mapping_discovery.operation_binders`): logical binders and `Crane
  Extraction Implicit` positions are erased, informative type schemes are
  type parameters (their order is the `%tN` numbering), class-typed binders
  are instances (passed apart from the runtime arguments, so not `%aN`), and
  the rest are the retained runtime binders (`%aN`). The contract binds its
  arguments to those one to one; a named Rocq binder must carry the
  argument's name (an anonymous one accepts any), which catches a swapped
  list. Core's call arguments are not the Rocq binders: type parameters
  *and proofs* are gone, instances stay, so the callee flags fed to
  `Escape.passed_to_owned` are indexed by `call_binders` (an index over all
  binders gave the `Take` to the wrong argument). Like M3, the plan
  (`Base.Mapping_operation`) is compiled into the legacy vocabulary:
  `%arg(x)` is the `%aN` of `x`'s binder, `%stored(c)` the `%tN` of the type
  parameter `c` is stored at in the first argument type (source order), then
  the result type (searched inside, so a monadic result counts), declaring
  `c`; a component whose type argument there is not a type parameter of the
  operation is refused, and so are `%tmpN` and an instance for one
  instantiation. Legacy lowering took a call's arity to be one past the
  last `%aN`, so a trailing `Ignore` argument would have been applied to the
  result: `Table.inline_custom_arity` gives the retained count. Single
  evaluation is in `Shared_args`: each argument that is not free to repeat
  is bound ahead of the call in order (an unspliced one is evaluated as a
  statement), and one bound by value and spliced once is passed as
  `std::move` of its temporary so a `Take` still gets an rvalue. "Pure" for
  an `Ignore` argument is `free_to_repeat` (a local, literal or field):
  any other computation is evaluated and discarded. `Region` counted an
  unspliced argument as evaluated zero times, which `CRANE_CHECK_IR`
  rejects as an unplanned read; it now counts one per argument and passes
  the borrowed ones as `inspected`, so `Read`/`Write`/`Ignore` arguments are
  never moved. Deferred: result specs and facts other than
  `RetainsArgument` are compiled but not consumed (borrow provenance, fresh
  identity, invalidation); `Replace` is treated as borrowed (its `T&` mode is
  M5); single evaluation covers only calls a statement evaluates
  unconditionally, the same limit as the legacy pass (a call under a
  conditional or short-circuit is left as written); the alignment of
  `Extraction Implicit` binders with Core's arguments is assumed (dropped,
  like proofs) and untested; holes inside C++ string literals are still
  substituted when compiling (validation skips them).
- **M5 (second part).** The lattice is `Core_plan.Access` (access
  `Unused < Read_access < Write_access < Replace_access`, representation
  `Preferred < Canonical`), beside `Ownership`, summarised per generated
  function (innermost first, aligned with the ownership flags) and settled
  to a fixed point over every function of the program
  (`Program_facts.parameter_access`); `CRANE_TRACE_ACCESS=1` prints the
  summaries. Uses: a mapped operation's argument as its `InputUse` says
  (a `Take` reads unless a `WritesComponent` fact names it), a direct call's
  argument as the callee's summary says, a local bound to a parameter as it
  is (`let y := x`) as that parameter; anything else (constructor argument,
  returned, matched, passed to a legacy mapping, a closure, a partial
  application) is a canonical read. Ownership stays where it was: `Owned`
  is still the ownership flag, so a `Take` beside a `Replace` is by value.
  Physical selection (`Access.physical`, read by
  `Core_to_cpp.Ownership.wrap_param_by_ownership`) only departs from the
  canonical read form for a borrowed parameter of a typed-mapped type:
  `Replace_access` is `T&` (`replace_form`, or `explicit_replace`), and
  `Write_access` is the access model's write-through form (`T&` for
  `MutableValue`, the read form for a handle, `explicit_write` for
  `ExplicitAccess`; `ExactParameter` falls back to the read form). So for
  `MutableHandle` only a replacement changes the signature; the write chain
  is visible only for a mutable value. Without views, the representation
  dimension decides nothing yet; it is computed for M7.
  First-class functions (§12.9): a function named anywhere other than as
  the head of a saturated call is *pinned*, and so is a function generated
  as a method. A pinned function's mutable-reference forms become a copy
  by value (`Param_mode.copied`), which its body may write or replace, and
  its callers read its summary capped at `Read_access`. So no adapter is
  generated: the function itself keeps the canonical ABI (the design's
  adapters would let direct calls keep `T&`; not needed by anything yet).
  Under a closure (a lambda or a local fixpoint body) a parameter is a copy
  the closure holds, so a use there is capped at a read too; lambdas and
  local fixpoints keep canonical forms.
  Call sites: rather than rebuilding each argument passing site
  (`gen_call_args`, control lowering, `Frame_storage`), a lowered pass
  `in_place_args` (after `shared_args`) reads the callee's *planned* modes
  (`Callable_abi.modes`, `By_reference` now has a producer) and an
  operation's `in_place` arguments (a `Replace`, or a write whose
  write-through form is `T&`, computed in `Mapping_operation`), and passes
  a variable the caller declares writable as it is; anything else (a call's
  result, a `const&` parameter, a closure's copy, a match binding) is
  materialised as `crane::writable(e).ref()` (`theories/cpp/writable.h`, a
  temporary that lives to the end of the full expression). Because it runs
  on the final lowered body, loops and frames are covered by the same pass.
  `Shared_args` no longer moves an in-place argument's temporary. `Tail`
  gets a fourth shadow hold, `In_place`: a `By_reference` parameter's loop
  shadow is a `T&` to it, so a loop rebinds the caller's object instead of
  copying it into a value. A frame (`Frame_storage`) holds an in-place
  parameter by value, as each recursive call's materialised argument would
  be. Semantics to keep in mind: the recursive and the loop lowering of the
  same self-recursive `Replace` differ in which reseats reach the caller's
  slot (the loop's do, a recursion's inner calls write temporaries); both
  are within the contract ("may replace").
- **M6.** `STArray` and `STRef` are typed mappings in `STMonad.v`
  (`std::shared_ptr<std::vector<A>>` and `std::shared_ptr<A>`,
  `MutableHandle HandleByConstReference`, `NoViews`, `NativeRAII`); the
  legacy `Crane Extract Inductive STArray` and the `Inlined Constant`s of
  the eight operations are gone. `newListArray` and `getElems` call
  `theories/cpp/crane_st.h` (`crane::st::new_list_array`, `elems`, and
  `extent` for `hi - lo + 1`), templated on the list type so the header
  does not name a unit's `List`. What the ST operations needed of M3/M4:
  - A definitional class (ITree's `ReSum`, behind `-<`) unfolds to its
    method's type, so `whd_all` hid it and the instance binder was taken
    for a runtime argument; `is_class_type` now reads the head before
    reducing too.
  - `%stored(c)` at a type family parameter applied to terms (`V idx`)
    is the type variable `V` (extraction drops its term arguments).
  - A call's `%tN` are the kept dictionaries' type arguments first, then
    the type parameters, so `%stored` is offset by the instance binders
    whose class Crane does not skip (`Mapping_discovery.is_kept_instance`,
    told the skipped classes by `Table` through `skipped_class`);
    `STRefClass T` counts, `ReSum` does not.
  - A type mapping's `Parameter i` counted every binder of the head, but
    a use's C++ type arguments are its type parameters only: `STRef` is a
    class projection (`T`, the `STRefClass T` instance, `S`, `A`), so
    `A` is type argument 2, not 3. `Mapping_plan.components` is now the
    type-argument position; `component_binders` keeps the binder position,
    which `Mapping_operation` uses to find the component in a Rocq type.
  - The index `idx` of each operation is `Crane Extraction Implicit`:
    it only selects `V idx`, and passing it as an `Ignore` argument
    evaluated it as a discarded statement (`nat_idx::zero();`).
    `check_for_remaining_implicits` now skips a mapped operation's own
    body and its own implicit positions at a call to it (the lowering
    already drops them).
  - `Param_mode.disagreement` refused a pointer-declared parameter that
    is not the receiver; a raw-pointer mapping's canonical type is one,
    so only "a receiver must be a pointer" remains.
  Results: a helper that reads and writes a cell, `swapArray` (no longer
  unfolded in `st_arrays`), and every link of an `outer -> middle ->
  writeArray` chain take `const std::shared_ptr<std::vector<T>>&`;
  `regrow` (a test-local `Replace`) gives `std::shared_ptr<...>&`; a
  helper that returns an array, or passes it to one that does, takes it
  by value (`tests/monadic/st_array_helpers`). Known limit: returning an
  array through `Ret` keeps it `const&` and copies at the return, because
  `Ret` is a legacy mapping whose argument is only read, and a tuple
  construction is a read by design (`Escape`); making a pass-through
  legacy template transparent to escape would change unrelated outputs.
  `vector<bool>`: with no views a `bool` array is a `std::vector<bool>`
  read and written through the handle (proxy references convert), which
  is correct; the addressable-storage decision stays with M7's spans.
  The raw-pointer alternative (`tests/regression/typed_mapping_raw_array`,
  a `RawArray` axiom, `RegionOwned`): read and write take `std::vector<T>*`
  by value at every level, `Replace` takes `std::vector<T>*&`;
  `ExternallyOwned` and `ManualShared` are accepted, `NativeRAII` refused.
  `st_quicksort` keeps `partition` and `swapArray` as functions (only the
  `rec` body is unfolded: its `call` pushes onto the stack `rec`'s mapping
  declares), `union_find` extracts `make_ST`, `find_ST`, `union_ST`,
  `same_ST`, `run_ST` separately; their proofs are about the section
  definitions and were unaffected. No test reached `STMonad` by a bare
  `Require` (D5): every user imports it. Leaks: LSan and `leaks` both hang
  on this macOS machine, so the check is an allocation counter (global
  `operator new`/`delete`) around a second run of each test's `main`:
  the committed outputs before M6 leave 6 (`st_arrays`), 4
  (`st_quicksort`), 8 (`union_find`) allocations live per run, 0 now for
  `st_arrays`, `st_refs`, `st_fibonacci`, `st_quicksort`, `union_find`,
  `st_array_helpers`. `shared_ptr` does not collect cycles; the ST API's
  element types (`V idx`, no recursive types) cannot build one, so no
  cycle test exists. A type alias whose body is an event type applied to
  a type-level lambda (`Definition E := STEvent nat unit (fun _ => nat)
  +' ...`) crashes alias planning (`method_registry not initialized`,
  `Entities.alias_template_kinds`); pre-existing, the test uses
  `Notation` instead.
- **M7.** Views are compiled into the plan (`Mapping_plan.views`: view
  type, `from_canonical` with `%value` as `%a0`, `read_from_write` and the
  `MaterialiseView` construction with `%view` as `%a0`). Physical
  selection (`Access.physical ~view_allowed`) gives a borrowed,
  `Preferred` read the read view and a `Preferred` write the writable
  view; `view_allowed` is true only for generated functions that are not
  pinned (lambdas, local functions and methods keep canonical forms). The
  mode is `Param_mode.By_view (kind, head)`, declared at the view type
  (spelled `By_value`); `Param_mode.invalidates_views` records whether the
  callee may invalidate a view of its argument. An operation argument
  declared `Read`/`Write` of a type with the matching view is given the
  view: `Mapping_operation.argument.view` carries the conversions compiled
  into the operation's own vocabulary (`%tN` of the call), and such an
  argument is never `in_place`.
  Call sites: a lowered pass `view_args` (after `in_place_args`, before
  `foreign`) reads the callee's planned modes or the operation's argument
  views and converts with the declared conversions only (12.7): canonical
  -> `view_from_canonical`, same view -> as is, writable -> read via
  `read_from_write`; widening a read view is an error. A conversion over a
  generated callee needs the argument's component types: from the
  variable's declared type, a call's `yields`, or, where neither is known
  (a structured binding), read back from the value with
  `crane::template_argument_t<decltype(e), j>` (`template_argument.h`,
  included by a mapping whose view conversions name a component). A
  template that places `%a0` twice is given a variable: a non-free value is
  bound ahead of the statement (`_viewN`), except in a `while` condition.
  View results (12.8): a borrowed-view result passed straight to a view
  position stays a view (its temporaries live to the end of the full
  expression); bound by `shared_args` as `auto _onceN` it stays a view and
  any temporary it was taken of is bound ahead too; anywhere else it is
  materialised, or refused when `BorrowOnly`. Invalidation (7.8): the
  access requirement gains `invalidates` (an `InvalidatesViews` fact,
  `Replace`, `OpaqueUse`, joined across calls); a variable passed as a view
  beside an argument that may invalidate it is passed as a view of a copy
  bound ahead of the statement (read view, materialisable) or refused.
  Validation refuses `InvalidatesViews` on an argument given as a view (a
  resize must be `WriteCanonical`/`Replace`, 13.8).
  `InvalidatesElementBorrows` is recorded and distinguished but has no
  consumer: no canonical-borrow result outlives its full expression (an
  operation's result is bound by value), so no element borrow can be held
  across a write.
  Access changes needed by views: a use under a closure is now `Canonical`
  as well as capped (a closure may outlive the call, and a capped write
  through a handle would otherwise pass as a read view); the continuation
  of a bind in a sequential monad (`Effects.declaration_mode`) is not a
  closure, so ST helpers written with `;;` keep views; summaries start at
  the least requirement (a recursive call met before its callee's summary
  used to count as a canonical read, which made every recursive helper
  canonical); a body that is one fixpoint applied to the parameters (a
  section `Fixpoint`) is walked as the function itself, its free uses of
  the parameters not closure captures (`union_find`'s `find_ST`).
  `vector<bool>`: option 1. `crane::array_storage<T>`
  (`theories/cpp/array_storage.h`) is a fixed-size, non-copyable array of
  addressable `T`, `bool` included; `STArray` is
  `std::shared_ptr<crane::array_storage<A>>` with `std::span<const A>` /
  `std::span<A>` views, both `BorrowOnly`; `crane_st.h`'s `elems` takes a
  read span. Results: `swapArray` takes `std::span<T>`; `bump`,
  `middle`/`outer`, `flip` (bool) `std::span<T>`; `peek`, `sum_from`
  `std::span<const T>`; `write_and_refill` (Write + `WriteCanonical`)
  `const std::shared_ptr<...>&`; `pick`/`write_then_pick` by value,
  `regrow_then_write` `&`; loopified tail and non-tail recursion keep the
  view out of loop variables and frames (`st_array_loops`). `partition`
  (`st_quicksort`) stays by value: its array is captured by a real
  closure (`for_each_with`'s callback).
  Strings: `Std.v` is split into `StdCore.v` (everything but strings) and
  the legacy string block; `StringView.v` exports `StdCore` and maps
  `PrimString.string` as a typed `std::string` with a `std::string_view`
  read view (`MaterialiseView std::string{%view}`), with `length`, `cat`,
  `get`, `sub` (`crane_string.h`, total as in Rocq; `sub` returns an
  owner). A typed and a legacy mapping of one head cannot coexist (22.5),
  so the standard `Std.v` string mapping is untouched and migrates with
  M8; no existing test imports `StringView`, so no existing output
  changed except the ST users (`st_arrays`, `st_array_helpers`,
  `st_quicksort`, `union_find`, `unit_accum_local_fix`: canonical type
  `array_storage`, reads/writes through spans, helpers taking spans).
  Memory safety: ASan (use-after-free detection works; a report hangs the
  process at exit on this machine, so runs use `symbolize=0`; leaks not
  checked) is clean on `string_views`, `structural_spans`,
  `st_array_helpers`, `st_array_loops`, `st_arrays`, `st_quicksort`,
  `st_refs`, `st_fibonacci`, `union_find`.
  Not done: a borrowed view held in a variable other than a `shared_args`
  binding is materialised rather than kept within its owner's proven
  lifetime; view ABIs for first-class functions (12.9, deferred); a string
  literal passed as a view is spelled `std::string_view{std::string("...")}`.
- **M8 (partial).** Migrated to typed descriptors, each with `Import`
  added to the tests that reached it by a bare `Require` (D5, 219 files,
  plus `recursive_library_datatypes/Lib.v`, which reached `option` only
  through `Src`'s legacy mapping): `StdCore.v` (`option`, `prod`,
  `fst`/`snd`, `int63`, `float`, `char63` and their primitives), `Std.v`
  strings (M7's typed `std::string` mapping; `StringView.v` now only
  re-exports `Std`), `NatIntStd.v`, `NInt.v`, `ZInt.v`, `NatGMP.v`,
  `NGMP.v`, `ZGMP.v`; their `Crane Extract Numeral`s are numeral
  descriptors. What the migration needed of the pipeline:
  - Match templates: a binder whose field is declared at a type parameter
    is spelled `const %tN&` (as the legacy option template was), a
    recursive field (`S n`) as the canonical type, a field of another
    mapped inductive (`Npos p`) as that mapping's closed canonical type,
    else `auto`; owned projections likewise. A pair or tuple whose single
    constructor projects `std::get<j>(%scrut)` for every field is matched
    by a structured binding, so `Foreign_template.structured_binding` still
    lets an owned scrutinee be taken apart by value (the design's
    `%scrut.first` would have lost that).
  - A name several retained binders share identifies none and is read as
    anonymous: every binder of a primitive (`PrimInt63.add`) is `x`.
  - `Shared_args`: for a `PureOperation` none of whose computing
    arguments may have an effect, only the arguments its text repeats are
    bound ahead (and dropped ones evaluated), as legacy did; the rest stay
    in place. Binding every computing argument ahead (M4) turned each
    `a * b + c * d` into named temporaries. Evaluation order is observable
    only through effects; an argument "may have an effect" only when it
    calls a non-pure operation mapping. A legacy mapping declares nothing
    and is taken as pure, as legacy lowering took it: treating it as opaque
    (22.2) bound every `s.length()` of `External.StringViewStd` ahead of
    the int63 arithmetic around it (`tokenizer`). `typed_mapping_operations`'
    effectful legacy `tick` keeps its repeated argument bound and its
    ignored one as a statement; order across the others is the legacy one.
  - A match tests constructor views in the order `AlgebraicInterface`
    lists them, the last untested (documented in `Descriptor.v`): a view's
    test may assume the earlier ones failed. `positive` lists `xH`, `xI`,
    `xO` and tests `== 1`, then oddness, as the legacy template did.
  - A module type's concept spells a typed head through its legacy text,
    so `M`'s members inside its arguments are `typename M::t` (a `Plain`
    structured type had lost that).
  - `is_literal_type`: a typed head is literal as its copy model says
    (`BitCopy`; `CopyComponents` of literal components); after
    instantiation `External (s, _)` naming the canonical type of a plan
    that duplicates or retains (`mpz_class`, `std::string`) is not (it was
    taken for a literal, giving `static constexpr mpz_class`).
  - `PeanoNat.Nat.add` &c. are the same constants as `Nat.add` (an
    `Include`): mapping both is an ambiguity, so only `Nat.*` and
    `PeanoNat.Nat.eq_dec` are mapped. A test-local legacy override of a
    now-typed operation is a conflict (22.5); `validated_pump_delivery_trace`
    dropped its five `PeanoNat` overrides (four identical, `modulo` without
    Rocq's zero guard).
  GMP numerals are gmpxx's exact `(n_mpz)` literal (`IntegerToken "("
  "_mpz)"`): legacy `mpz_class(%n)` could not hold 2^63 or more, which
  `numeral_wrap_gmp` overrode with a legacy `Crane Extract Numeral`; the
  override is gone (a legacy numeral on a typed head is silently ignored,
  `get_numeral_info` asks the typed plan first; it should be refused as a
  22.5 conflict). `typed_mapping_golden` checks `list nat` as unmapped
  instead of `nat`.
  Numerals: `Mapping_plan.numerals` compiles the descriptor;
  `Table.get_numeral_info` answers from it first (`typed` carries the
  cases), the format is the emitter's (`IntegerToken p s` is `p%ns`,
  `DecimalConstructor c` is `c("%n")`), converters are the descriptor's
  (found per extraction by resolving each head's instance without caching
  its plan, `Mapping_plan.numeral_converters`), and
  `Numeral_literal.typed_value` evaluates a constructor term by the
  actions (`Identity`/`Negate` read the field's own type's descriptor, or a
  binary `positive` where it has none), with no constructor name known to
  the plugin. Validation adds 19.7 rules 3-5: a successor/double action's
  field is of the mapped type, an identity/negate field of another
  inductive, the emitter's text is a numeric-literal wrapper or a
  qualified name, converters return the mapped type, one case per
  constructor.
  Output changes, reviewed: an optional or pair of by-value components is
  passed by value (design 15.2; legacy passed `const&`, and a pair holding
  a legacy custom type such as `Real` is by value too, since a legacy
  custom type constant reads by value); some functions returning one
  became `constexpr`; a function that only reads a string takes
  `std::string_view`, one that keeps or concatenates it `const
  std::string&` instead of a moved-from copy; `get` is
  `crane::string_get`; `positive` constructor chains fold into literals (`3u` for
  `(2u * 1u + 1u)`); option/pair headers are included per extraction.
  `cat` reads both strings canonically and is spelled `+`: through views
  (M7) every link of a chain allocated a string of its own and each
  argument was wrapped in `std::string_view{...}`, where `a + b + c`
  appends to one temporary; `string_views` changed accordingly. Still
  worse than legacy: a string literal passed as a view is
  `std::string_view{std::string("...")}`, and a view of a parameter read by
  `length` is spelled `(std::string_view{s}).size()`.
  Compiled interfaces (`Base.Mapping_interface`, design 20): when an
  extraction finishes, the unit records (a `superglobal` libobject beside
  `claim_extracted_unit`) every head it compiled a type or operation plan
  for, with the selected instance and a digest of the compiled plan
  (canonical type, components, copy, access, value and lifetime model,
  views, constructor plans, release; an operation's template, argument
  uses/forms/views, result, facts, purity, headers; references by kernel
  name). An extraction that includes the unit's header checks each entry
  before lowering and refuses a different instance, a different ABI, or no
  typed mapping (`tests/regression/typed_mapping_interface`: `Use` agrees,
  `Mismatch` is refused unmapped and with the other instance). The check
  covers every recorded head, not only those the consumer uses.
  Exact numbers (16): `tests/regression/typed_mapping_exact_numbers` maps
  `nat` to `boost::multiprecision::cpp_int` (`DuplicateValue`, `const&`
  parameters, `DecimalConstructor`, a 21-digit literal, 25!); arithmetic
  results are wrapped in `cpp_int(...)` so no expression template outlives
  its operands. `scripts/compile-boost.sh` puts Boost on the system
  include path (stub when absent).
  Not done, and why no deprecation warning yet: BDE mappings (`BDE.v`,
  `NatIntBDE.v`, `NIntBDE.v`, `ZIntBDE.v`, `Monads/*BDE*`; BDE is
  installed here, `~/Library/bde_install`, and its tests run), `Shared.v`
  (`bool`, `sumbool`, `unit`, `PrimArray`), `Real.v`, `DequeList.v`,
  `AsciiChar.v`, `External/*`, the monad mappings (IO, STM, threads, ITree
  events: effectful operations) and every test-local mapping remain
  legacy, and `Crane Extract Monad/Skip/Void` have no typed counterpart, so
  a migrated equivalent does not exist for every standard use and the
  legacy commands are not deprecated.
- **M8 (second pass).** Migrated, each with its outputs: `Shared.v`
  (`bool`, `sumbool` as BitCopy `bool`, `true`/`left` tested first;
  `negb`/`andb`/`orb`; `unit` as `std::monostate`; `PrimArray` as
  `persistent_array<T>` read by const reference), `AsciiChar.v`, `Real.v`,
  `DequeList.v` (`list` as `std::deque`, nil tested first, the tail an
  owned copy `%ret(%scrut.begin() + 1, %scrut.end())`), `BDE.v`,
  `NatIntBDE.v`, `NIntBDE.v`, `ZIntBDE.v` (generated from their Std
  counterparts with the `bsl` spellings; BDE strings have a
  `bsl::string_view` read view). What it needed of the pipeline:
  - 22.5: a legacy `Crane Extract Numeral` on a typed head is refused when
    mappings are discovered (`typed_mapping_abstract`, `Bead`).
    `Crane TriviallyCopyable` needs a legacy mapping of its head, so on a
    typed head it already met the `customs` conflict.
  - A string literal taken as a read view is the view of the literal
    (`View_args.literal_view`, CppIR `Literal (Characters _)`):
    `std::string_view("...")`, with the length where the literal holds a
    NUL. The read view of a type with literals must be constructible from
    a literal and a length (documented on `ViewSpec`). A global's
    initialiser gets only this rewrite. A string literal holding a NUL is
    printed `std::string("a\000b", 3)` everywhere (it was truncated).
  - An operation's binders carry the evar map of the fresh instance they
    were read from: a universe-polymorphic primitive (`PrimArray.get`)
    failed to resolve.
  - A recursive field's match binder is spelled `%ty`, the matched value's
    type, not the canonical type, and a projection's `%ret` is the field's
    type: a deque read at an erased instantiation
    (`any_cast<std::deque<crane::obj>>`) binds its tail at that type.
    A custom match whose scrutinee is cast to an erased instantiation
    spells its type arguments `auto`, so a borrowed head is `const auto&`.
  - A `bsl::pair` whose projections are `%scrut.first`/`%scrut.second` is
    matched by a structured binding, as `std::pair` with `std::get`.
  Output changes, reviewed: a match on `unit` opens no block; `Real` is not
  moved and pairs of reals are bound by const reference; BDE outputs pass
  options' payloads and pair fields by const reference and strings that
  are only read as `const bsl::string&`/`bsl::string_view` (as Std);
  `bool_dec_bde` now Imports `Mapping.BDE` and is extracted in the BDE
  flavour it is compiled with; deque tails are written
  `std::deque<T> x = std::deque<T>(b, e)` (was direct initialisation) and
  heads `const T&` (was `const auto&`). Worse, recorded: `AsciiChar`'s
  eight bit bindings lost `const` (an owned projection binds a plain
  local).
  Not migrated, and why: `External/*` (`StringViewStd`/`BDE` map an
  axiomatised `string_view` whose operations are already views; `Vector`
  maps a mutable `std::vector` mutated through ITree events, which needs
  a `MutableHandle` model and the event mapping below), the monad
  mappings (IO, STM, threads, ITree events): their events are
  `Crane Extract Inductive E => ""` constructor templates of an indexed
  event family run by `Crane Extract Monad`, and the design has no typed
  counterpart for an event family, a monad, `Skip` or `Void` (design 22
  covers only Inductive, Inlined Constant and TriviallyCopyable); their
  smart constructors could become `EffectfulOperation`s, but the event
  constructors they embed would stay legacy, so nothing is gained until
  events have a descriptor. Hence no deprecation warning: a typed
  equivalent does not exist for every standard use (`Crane Extract
  Monad/Skip/Void/Skip Module` and event families have none), and every
  test-local legacy mapping still works through the legacy path.
- **Infrastructure.** `scripts/loopify-census.sh` fails on a rerun in an
  existing worktree (stale `_build/census`: dune does not rebuild a sibling
  `.vo` after the script deletes it); `rm -rf _build/census` before `make test`.
  Deleting `_build/default/tests` alone leaves dune believing the copied
  sources exist (coqdep: `z_int/ZIntTest.v: No such file or directory`);
  delete `_build/.db` and `_build/.digest-db` with it.

## 7. Progress

- [x] M1 declarator-correct types
- [x] M2 descriptor library and discovery
- [x] M3 type mappings in the pipeline
- [x] M4 operation mappings
- [x] M5 explicit parameter modes and access fixed point
- [x] M6 ST arrays and references without views
- [x] M7 views
- [ ] M8 standard mappings, interfaces, deprecation
  - [x] `Std.v`: `StdCore` (option, prod, int63, float, char63) and strings
  - [x] number mappings: `NatIntStd`, `NInt`, `ZInt`, `NatGMP`, `NGMP`,
        `ZGMP`, with numeral descriptors
  - [x] compiled interfaces (`typed_mapping_interface`)
  - [x] exact-number example (`typed_mapping_exact_numbers`, cpp_int)
  - [x] BDE mappings (`BDE.v`, `NatIntBDE`, `NIntBDE`, `ZIntBDE`)
  - [x] `Shared.v` (bool, sumbool, unit, PrimArray), `Real.v`,
        `DequeList.v`, `AsciiChar.v`
  - [ ] `External/*`, monad mappings (`Monads/*`, `*BDE` included):
        event families and `Crane Extract Monad/Skip/Void` have no typed
        counterpart in the design (see 6, M8 second pass)
  - [x] refuse a legacy `Crane Extract Numeral` on a typed head (22.5)
  - [x] a string literal passed as a view without `std::string(...)`
  - [ ] deprecation warnings: blocked, no typed equivalent for event
        families, monads, `Skip`, `Void`
  - [ ] full suite and corpus re-extraction after the second pass (not
        run: `/tmp/crane-vellvm-perf/quiet-ok` absent)
