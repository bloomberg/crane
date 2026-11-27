# The Crane compiler pipeline

This document describes how the plugin turns a Rocq declaration into C++:
the intermediate languages, the stages between them, the checks at each
boundary, and the switches a developer can turn on. It describes the code as
it is. The authoritative pass order is
[`unit_tests/pipeline_manifest.expected`](../unit_tests/pipeline_manifest.expected),
printed from the pass lists the driver runs; a test fails when the two
disagree.

The user-facing side of typed mappings and `Crane Bake` is in the
[Reference Manual](Reference-Manual.md#typed-mappings); the image format of
a baked constant is described in `theories/cpp/crane_bake.h`.

## Overview

Crane starts from elaborated, kernel-checked Rocq terms. It never reads
surface Gallina.

```text
Rocq source
  -> Rocq elaboration and kernel checking
Rocq kernel terms (PCUIC)
  -> extraction                        Rocq_to_core.Extraction
Core (extracted)
  -> Core passes                       Core_passes.Phase.optimize
Core (optimized)
  -> freeze                            Core_passes.Phase.freeze
Core (frozen)
  -> normalize passes                  Core_passes.Phase.normalize
Core (normalized)
  -> whole-program analysis            Driver.Program_facts.analyze_program
       recursion plan, ControlIR       Core_plan.Recursion, Core_to_control.Lower_control
       ownership and access summaries  Core_plan.Ownership, Core_plan.Access
  == split into units (separate extraction: one per library)
  -> per-unit analysis and planning    Driver.Program_facts, Driver.Target_plan,
                                       Core_plan.Elaborate, Core_plan.Callable_abi
  -> typed lowering                    Emit.Files.generate_ahead, Core_to_cpp.Lower_decl,
                                       Core_to_cpp.Lower_expr, Core_to_cpp.Coerce
       ControlIR -> CppIR              Control_to_cpp.Lower, Control_to_cpp.Loopify
       ownership                       Ownership_ir.Region
CppIR (Lowered)
  -> finishing                         Cpp_passes.Pipeline.finish
CppIR (Resolved), in the unit program  Cpp_passes.Unit_program
  -> assembly, scheduling, naming      Emit.Leaf_plan, Emit.Files, Cpp_ast, Unit_plan.Cpp_names
CppAST
  -> printing and layout               Emit.Print, Emit.Layout
.h and .cpp text
  -> Clang (-std=c++2c), outside Crane
```

Three kinds of boundary appear, and only the first introduces a new grammar:

1. Language changes: Rocq terms to Core, Core to CppIR (with ControlIR as an
   intermediate for control), CppIR to CppAST to text.
2. Invariant-strengthening phases over one grammar: Core's
   `extracted`/`optimized`/`frozen`/`normalized` (`Core_passes.Phase`), and
   CppIR's `Lowered`/`Resolved`.
3. Side artifacts that describe a program without replacing it:
   `ProgramFacts`, `TargetPlan`, callable plans, the representation, position,
   recursion, ownership and access plans, and compiled typed mappings.

The source tree follows the same order. `src/` uses `(include_subdirs
qualified)`, so `src/core_passes/dedup.ml` is `Core_passes.Dedup`, and each
directory may use only the directories before it in this list:
`core`, `control_ir`, `cpp_ir`, `base`, `core_passes`, `rocq_to_core`,
`core_plan`, `core_to_control`, `unit_plan`, `ownership_ir`, `cpp_ast`,
`cpp_passes`, `control_to_cpp`, `core_to_cpp`, `emit`, `driver`.
`scripts/check-module-deps.sh` enforces it (see section 10).

## 1. Entry, mapping discovery and dependency collection

The vernacular commands are parsed in
[`g_extraction.mlg`](../src/g_extraction.mlg). The driver,
[`driver/extract_env.ml`](../src/driver/extract_env.ml), resolves the
requested references or modules, collects their dependencies from Rocq's
global environment and extracts them (`simple_extraction`, `full_extraction`,
`separate_extraction`, `extraction_library`). Legacy custom mappings and
options are already registered in [`base/table.ml`](../src/base/table.ml).

Before anything is collected, `init` runs
`Base.Mapping_discovery.discover`: it enumerates the active instances of the
typed mapping classes `TypeMapping` and `OperationMapping`
(`theories/Mapping/Descriptor.v`) and records each under its head (the head
of `T` in `TypeMapping T`, the referenced declaration in
`OperationMapping (Ref d)`). An instance is active once the module exporting
it is imported. Then `Base.Table.check_typed_mapping_conflicts` refuses a
head mapped both by an instance and by a legacy `Crane Extract ...` or
`Crane Extract Numeral` command. A head with a typed mapping counts as mapped
for dependency collection, so its body is not extracted. Section 7 covers
what happens to a typed mapping after discovery.

Separate extraction also fixes the module order used for includes, and
`Base.Mapping_interface.check` compares the typed mappings recorded by the
units whose headers this unit includes against this extraction's own
resolution, so that import order cannot silently give a header two
signatures.

## 2. Rocq to Core

[`rocq_to_core/extraction.ml`](../src/rocq_to_core/extraction.ml) erases
propositions, proofs, universes, type arguments and configured implicits,
reconstructs ML-style type schemes with unification metavariables, and builds
Core declarations. Each extracted object gets a `Core.Signature.t`: one
`Runtime` or `Erased of Erasure_reason.t` entry per source argument.
Extraction also records facts the backend cannot recover from Core alone
(promoted type-class carriers, higher-kinded parameter positions, instance
shapes) in `Base.Table`.

Core is the namespace [`src/core/`](../src/core/). The families are defined
together in `core/grammar.ml`, which is private: `core/core.ml` is the
namespace's interface and exports only the families, so a constructor the
grammar keeps private (a metavariable cell, a global use, a recursive group)
is built only through its family's module.

| Module | Contents |
| --- | --- |
| `Core.Type` | `Arrow`, `Global_app`, `Variable`, `Variable_app` (higher-kinded), `Meta` (reconstruction cell), `Hole`, `Open` (immutable unsolved annotation), `Erased`, `Unknown`, `Axiom`, `String` |
| `Core.Expr` | `Bound_variable`, `Apply`, `Lambda`, `Let`, `Global` (a `Core.Global_use` with its instantiation), `Construct`, `Tuple`, `Match`, `Fixpoint`, `Cofixpoint`, `Coerce`, `Boxed_value`, `Lambda_group_barrier`, `Numeral`, primitive literals (`UInt63`, `Float64`, `String`, `Persistent_array`), `Erased_value`, `Axiom_value`, `Runtime_error` |
| `Core.Pattern`, `Core.Match` | patterns; match branches as records |
| `Core.Extracted` | making and solving metavariables, which exist only until freeze |
| `Core.Decl` | `Inductive`, `Type_alias`, `Value`, `Recursive_group` (nonempty by construction) |
| `Core.Inductive` | packets, kinds (`Inductive`, `Coinductive`, `Record`, `Type_class`) |
| `Core.Signature`, `Core.Schema` | argument signatures; a constant's type scheme with its source binder layout |
| `Core.Recursion` | top-level recursive definitions, members, local recursive groups |
| `Core.Record` | record and type-class fields |
| `Core.Module` | module types, signatures, structures, functors, applications |
| `Core.Program`, `Core.Interface` | a whole program's structures and signatures, by module path |
| `Core.Occurrence` | the identity of a node, which plans key their answers by |
| `Core.Fingerprint` | digests of a program, to check two readers saw the same one |
| `Core.Scheme` | the three numberings of type variables (Rocq binder, Core scheme variable, C++ template parameter) as distinct types |

## 3. Core phases

[`core_passes/phase.mli`](../src/core_passes/phase.mli) wraps a
`Core.Program.t` in a phantom-indexed `'phase program`. The only way to
obtain a `normalized program`, which every backend entry point takes, is
`optimize`, then `freeze`, then `normalize`.

- **optimize** runs the `core` pass list: `modutil` (beta/iota, inlining,
  pruning), `shared_variants`, `dedup`, `specialize`, `knot` (well-founded
  recursion tied directly), `fix_shape`, `fresh_occurrences`, `local_types`,
  `ir_check` ([`core_passes/check.ml`](../src/core_passes/check.ml)).
- **freeze** checks structural invariants and removes every `Meta`: a solved
  one becomes its solution, an unsolved one an immutable `Core.Type.Open`.
- **normalize** runs the `normalize` pass list: `eta_expand`,
  `let_lambdas`, `spines` (canonical application spines; numerals folded to
  `Core.Expr.Numeral` by `Core_passes.Numeral_literal`), `normalize`
  ([`core_plan/normalize.ml`](../src/core_plan/normalize.ml): names calls and
  splices recursive partners, recorded in `Core_passes.Splices`), and the
  `canonical` check.

Shared utilities live in [`base/core_util.ml`](../src/base/core_util.ml) and,
for Core and CppIR types, [`base/type_util.ml`](../src/base/type_util.ml).

## 4. Whole-program analysis

`Driver.Program_facts.analyze_program` reads the normalized program before
it is split into units and returns:

- throwing definitions (`Core_plan.Structure`);
- parameter ownership ([`core_plan/ownership.ml`](../src/core_plan/ownership.ml),
  [`core_plan/escape.ml`](../src/core_plan/escape.ml)) and reuse candidates;
- parameter access ([`core_plan/access.ml`](../src/core_plan/access.ml)):
  what each parameter of each generated function does with its value, a
  point of the lattice `Unused < Read_access < Write_access <
  Replace_access` joined with a representation (`Preferred < Canonical`),
  computed as a least fixed point over the program from typed operation
  contracts (`InputUse`), direct calls and everything else (a canonical
  read). A function named as a value is pinned to canonical forms.
  `CRANE_TRACE_ACCESS=1` prints the summaries;
- recursive groups ([`core_plan/recursive_groups.ml`](../src/core_plan/recursive_groups.ml))
  and partner closure parameters;
- the recursion plan ([`core_plan/recursion.ml`](../src/core_plan/recursion.ml)):
  per group, no recursion, tail or non-tail, and the strategy `No_loop`,
  `Tail_loop`, `Modulo_cons`, `Frame_stack`, or `Suspended` (corecursion
  under a lazy constructor);
- the program's ControlIR
  ([`core_to_control/lower_control.ml`](../src/core_to_control/lower_control.ml)).

**ControlIR** ([`src/control_ir/`](../src/control_ir/)) is a function's
control as implemented, before any C++: `Loop`, `Continue`, `Continue_into`
(tail modulo cons), `Resume` and `Entry` (frame machines), `Return`, with
non-control terms left as Core. Loop lowering reads the recursion plan, the
ControlIR and the unit's effect operations as one value,
`Core_to_control.Loop_facts.t`, a field of the unit's context.

## 5. Per-unit analysis and planning

`print_structure_to_file` plans a unit completely before generating any of
it. The stages and their steps, as in the manifest:

| Stage | Steps | What it decides |
| --- | --- | --- |
| `plan` | `analyze_program`, `plan_target`, `record_kinds` | `Driver.Program_facts.t` (custom references used, higher-order projections, effect elaboration via `Core_plan.Effects`) and `Driver.Target_plan.t` (the unit's configuration, inductive kinds and why they differ from extraction's); the decided kinds are written into the structure |
| `unit` | `non_atomic_rc`, `reset_demands`, `cross_file_qualification` | per-unit configuration: whether `NonAtomicRc`/`SingleThreaded` are withheld because the unit runs on several threads |
| `represent` | `template_kinds` | kinds of inductive and alias template parameters |
| `layout` | `prepare`, `plan_names`, `plan_referenced_names`, `plan_field_names`, `plan_pointer_fields`, `plan_unmerged_wrappers`, `plan_concept_prerequisites`, `plan_scopes`, `plan_promoted_inductives`, `plan_accessors`, `plan_nested_structs`, `plan_instance_promoted_types`, `elaborate_calls`, `plan_callables`, `decide_callables` | `Core_plan.Module_plan` (C++ names of modules, globals and constructor fields, pointer fields, wrappers, scopes, accessors, nested structs); call elaboration; one callable plan per generated function and method |
| `elaborate` | `plan_foreign_callables` | callable plans for globals the unit calls but does not declare |

The main artifacts:

- **ProgramFacts** ([`driver/program_facts.mli`](../src/driver/program_facts.mli)):
  observations, no decisions.
- **TargetPlan** ([`driver/target_plan.mli`](../src/driver/target_plan.mli)):
  backend decisions as a value: inductive kinds, template-parameter kinds,
  layout, names, pointer fields, callable plans.
- **Call elaboration** ([`core_plan/elaborate.mli`](../src/core_plan/elaborate.mli)):
  every global application walked once, in its lowered context, with each
  argument's role (dictionary, regular, past arity) and its instantiation,
  keyed by `Core.Occurrence`. Match kinds
  ([`core_plan/match_kind.mli`](../src/core_plan/match_kind.mli)) are
  recorded by the same walk.
- **Callable plans** ([`core_plan/callable_abi.mli`](../src/core_plan/callable_abi.mli)):
  a callee's C++ template head in final order, each parameter tagged with its
  origin (a scheme variable, a dictionary, a deduced callable), and each
  parameter's mode, `Cpp_ir.Param_mode.t`: ownership, physical form
  (`By_value`, `By_const_value`, `By_const_reference`,
  `By_forwarding_reference`, `By_reference`, or `By_view` of a typed
  mapping's view), role, and whether the callee may invalidate views. The
  form follows from ownership, access and the mapped type's access model.
  Calls map an instantiation onto the head by identity, never by position.
- **Representation plan** ([`core_to_cpp/representation_plan.mli`](../src/core_to_cpp/representation_plan.mli)):
  whether each binder of a region holds a value or a box (`crane::obj`),
  decided from the region's Core body.
- **Position plan** ([`core_to_cpp/position_plan.mli`](../src/core_to_cpp/position_plan.mli)):
  the C++ type each Core coercion (`Coerce`, `Boxed_value`,
  `Lambda_group_barrier`) is lowered against.

Nothing is installed globally for readers to find. Each stage reads the
unit's context, [`Unit_plan.Context.t`](../src/unit_plan/context.mli): the
unit's configuration, the callable plans decided so far, the module layout,
pointer fields, loop facts and standard-library spellings. The driver
threads [`Driver.Accumulated_plan`](../src/driver/accumulated_plan.mli) from
unit to unit of a separate extraction: a unit starts from what the earlier
ones decided (`for_next_unit` drops the per-unit layout and callable plans)
and its context is built from it (`context`).

Under `CRANE_CHECK_IR` the plan and the callables are each computed twice
(the callables in reversed order) and must agree.

## 6. Lowering: Core to CppIR

`Emit.Files.generate_ahead` walks the structure in the order it will be
rendered and generates every declaration either file writes, before either
file is opened. [`emit/entities.ml`](../src/emit/entities.ml) decides which C++
declarations a Core declaration becomes;
[`core_to_cpp/lower_decl.ml`](../src/core_to_cpp/lower_decl.ml) and the
generators `Functions`, `Inductives`, `Records`, `Instances` and `Concept`
build them. Bodies are lowered by one module per form: `Expr`, `Stmts`,
`Lambda`, `Application`, `Construction`, `Match`, `Effects` and
`Local_functions`. They recurse through `core_to_cpp/knot.ml`;
[`core_to_cpp/lower_expr.ml`](../src/core_to_cpp/lower_expr.ml) ties the knot
and exposes the entry points the generators call.
`core_to_cpp/lowering_state.ml` holds the lowering context, split into an
input part (set by the generator, read-only during lowering), a lexical part
(extended and restored per scope) and a threaded part.

### 6.1 Typed lowering

Every form module returns a `Cpp_ir.Typed.t`: the lowered expression and its
`Value_type.t`, one of

- `Typed t`: exactly the nameable type `t`;
- `Closure arrows`: a lambda's own, unnameable type, with its argument
  grouping;
- `Function_name (g, arrows)`: a global function named as a value;
- `Never`: an abort, which fits every slot;
- `Deduced reason`: a type only C++ knows, for one of a closed list of
  reasons (`Foreign_text`, `Runtime_helper`, `Generic_lambda`,
  `Requirement`, `Untranslated`, `Unannotated`).

`Cpp_ir.Typed.t` is private: a lowering module can only build one with a
type. Every form also takes a non-optional slot (`Core_to_cpp.Slot.slot`)
whose `Slot_type.t` says what the position asks of the value:

| Slot type | Position |
| --- | --- |
| `Exactly t` | a declared type: a parameter's value type, a variable, a field, a loop variable, a frame field, a return type (`Any` where the slot is erased) |
| `Template_parameter t?` | a type C++ deduces: an inline mapping's `auto`, a callee's own type variable |
| `Forwarded` | a forwarding reference `F&&` |
| `View (view, head)` | a typed mapping's view of the type headed so |
| `Free` | an `auto` variable or a discarded value |
| `Join` | the return type of the lambda being lowered, decided from the values it returns |

`Slot_type.of_param` turns a parameter's `Param_mode.t` into its slot.
Statement-producing lowering writes into a `Core_to_cpp.Destination.t`
(`Return`, `Return_void`, `Assign`, `Discard`, and two adapting forms)
rather than taking a continuation. A declaration whose type C++ deduces is
`Declare_deduced (value type, binder)`, which records the type lowering
knows and prints as `auto`; `Coerce` and `Declare_deduced` exist only in the
lowered phase, by the grammar's GADT index.

A Rocq arrow chain is one C++ group, `crane::fn<R(A, B)>`, wherever a value
of its type is declared, and a type variable instantiated at it is spelled
the same way (`id2<crane::fn<uint64_t(bool, uint64_t)>>`), so a value
crosses no regrouping by passing through a polymorphic function. Where a
declaration writes arrows around a type variable (`B -> A -> B` at a
function `B`), its own arrows are one group and the variable's the next
(`Cpp_ir.Types.arrow_site`, `Declared_at`). A call may write a type
argument the way its expected result groups it (`twice`'s step at
`A := nat -> nat` is `crane::fn<F(F)>`, so a call filling it writes
`(nat -> nat) -> (nat -> nat)`); its instantiation is then read once,
`Calls.grouped_instantiation`, and every type derived from it is spelled
at that grouping: each argument's slot (`Calls.grouped_parameter`, in
`Calls.argument_position`, shared by lowering and both plans), a
constructor's fields and type arguments, a global's eta adapter
(`Coerce.declared_cpp`). A box holds a callable at its Core spelling and
is regrouped to the slot after recovery.

**Typed fit.** Under `CRANE_CHECK_IR`, `Core_to_cpp.Typed_checks.fit`
checks every value lowering puts in a destination (`Destination.finish`) or
an argument slot: by `Coerce.decide` it needs no adapter, and its type is
related to the slot's. A pair that fails is a type reconstruction defect
(the C++ is right, but a value type or a slot is synthesised wrong) or a
missing coercion (the C++ is wrong). A pair is let through in two ways, and
anything else fails extraction:

- by structure, whatever declaration it is in (`Typed_checks.known_class`),
  for the open defect classes whose relation between the two types is crisp
  enough to say the slot is a spelling C++ resolves to the value's type:
  `event` (an event family named unapplied against the family applied to an
  index), `carrier` (a higher-kinded carrier applied, `app(M)<A>`, against a
  type whose trailing type arguments are `A`), `itreeF` (the observation of
  an interaction tree against the tree, or an alias of a tree's type),
  `promoted` (two types that agree once every member of an instance or a
  class, and every promoted variable, is taken as undecided: an associated
  type written on one side and resolved on the other). Only
  an `unrelated` verdict is classified; a pair that needs an adapter never
  is. `CRANE_PROBE` logs each as `typed-fit-class <kind> <pair>`;
- by name, an entry of
  [`unit_tests/typed_fit_allowlist.txt`](../unit_tests/typed_fit_allowlist.txt)
  keyed by (library, declaration, position, verdict, from, into), for the
  classes not yet recognised by structure. The list may only shrink. Open
  (81): erased 40, callable 12, other 9, carrier 7 (carriers not of the
  `app(M)<A>` shape -- `Functor_M<...>`, an instance struct -- or whose
  callable argument is grouped otherwise), promoted 5,
  tvar 5, stateT 2, and one loopify-census pair.

Generated programs meet the same defects as the test suite under other
declarations, so a class recognised by structure no longer depends on the
suite having met it; a new kind of pair still fails. Fixed classes (Ephyra
round 24): a match in expression position is an immediately invoked lambda
whose branches return to the lambda's own result (`Match.iife_return`),
never to the enclosing function's (a match as an argument, a callee, or a
case-of-case scrutinee); a partial application eta-expanded around its
hoisted arguments is typed as the closure, not the callee's codomain
(`Calls.record_call_sig`, `Application.eta_fun`); a methodified callee's
receiver binds its struct's variables, so a parameter naming one is
deduced, not written (`Application.gen_call_args`); an over-application
yields what is left of the callee's type after its declared arrows and the
outer call's arguments, read through a function alias such as `st A := nat
-> A * nat`, also where the inner call is kept as a constant
(`Calls.record_call_sig`). Ephyra round 25: a call that fills its callee's
declared parameters is written as the call, not eta-expanded to the arrows
its instantiation adds, so its result is the callable the written type
argument spells (`Application.eta_fun`); an argument at a forwarding
reference is built at the grouping of its parameter at the written type
arguments (`Calls.parameter_at_written`); a constructed argument whose
annotation unfolds a function alias the parameter writes is built at the
parameter (`Types.regrouped_through_aliases`); a `let` in argument
position is written against the slot as its body would be; an argument of
a local function or an applied local fixpoint is generated with its
parameter, not the enclosing result, as the return type in force.
Ephyra round 28: a typed mapping whose C++ type is one of its components
(`sig A P` is `A`) is read as that component by `Coerce` and by the join
(`Coerce.aliases_in`, `Match_types.declared_at`); an over-application
counts the arguments of every call between the declared call and the
outermost, and an application's arrows are dropped through a function
alias (`Type_util.strip_arrows_through_aliases`); a returned value a
substitution rebuilds keeps the type it was recorded at
(`Lowering_state.carry_returns`); a typed-mapped type carries no term
arguments, and a custom constructor is built at its slot where the slot
regroups its annotation through an alias; every argument of a call is
built at its parameter at the call's grouping (above), also a
methodified callee's, a nested call's lambdas are planned so, and a type
argument takes its expected result's grouping whatever namespaces the two
are written in; an undeclared immediately invoked lambda is typed as what
it returns (`Match_types.value_iife_typed`); a call given fewer arguments
than it declares reads none of its variables off its position.

### 6.2 The single coercion

Every adapter between a value and its slot (boxing, unboxing, erasing a
callable, eta-expanding a global, regrouping a curried callable, recovering
a boxed result, converting a carrier, naming a closure for a template
parameter) is one decision. `Core_to_cpp.Coerce.decide` is a total function
of the value type and the slot type, returning a `Coercion.decision`
(`Regroup`, `Name`, `Eta`, `Box`, `Deep_box`, `Unbox`, `Erase`, `Recover`,
`Convert`, `Container_cast`, or `Then` of two). `Coerce.into_slot` builds the
result as an `Expr.Coerce (coercion, value)` node whose `Coercion.plan`
carries everything its expansion reads; the adapter's text is not built
during lowering. A lowering reader that needs the value under an adapter
uses `Cpp_ir.Typed.head`.

Only `core_to_cpp/coerce.ml` builds the adapter vocabulary
(`Function_value`, `Erase_callable`, `Box`, `Any_cast`, `Tolerant_any_cast`
and `Erasure`'s box/unbox helpers) during lowering, and
`cpp_passes/coercions.ml` expands it; `scripts/check-module-deps.sh` fails
on any other builder in `core_to_cpp/` or `control_to_cpp/`.

### 6.3 Regions, ownership and control

Each region (a function, method, local fixpoint, lambda, or let in
expression position) is lowered from plans made over its Core body: the
representation and position plans, and **OwnershipIR**
([`ownership_ir/region.mli`](../src/ownership_ir/region.mli)): how each read
uses its variable (move, copy, borrow), how closures capture, frame storage,
allocation sites, reuse arms, loop-turn moves.
[`ownership_ir/final_path.mli`](../src/ownership_ir/final_path.mli) lets a
frame machine move a loop invariant on its single final activation. Lowering
follows these plans and, under `CRANE_CHECK_IR`, checks what it emits against
them.

Control is lowered during generation:
[`control_to_cpp/lower.ml`](../src/control_to_cpp/lower.ml) turns each
planned ControlIR loop into a CppIR loop, using the Loopify transforms
(`control_to_cpp/tail.ml`; `control_to_cpp/tmc.ml` with
[`control_to_cpp/reuse_cursor.ml`](../src/control_to_cpp/reuse_cursor.ml);
`control_to_cpp/frame.ml`).
[`control_to_cpp/loopify.ml`](../src/control_to_cpp/loopify.ml) lowers the
local fixpoints inside a loop and records each function's outcome for
`Set Crane Loopify Diagnostics`. A recursive group is lowered once all its
members are generated.

### 6.4 CppIR

**CppIR** ([`src/cpp_ir/`](../src/cpp_ir/)) is the structured C++ program:
types, expressions, statements, templates, concepts, structs, namespaces,
declarations. All families are indexed by phase (`cpp_ir/grammar.ml`):

- `Cpp_ir.Lowered` may still owe decisions, each a constructor of the closed
  list `Cpp_ir.Representation_obligation.t` (an unexpanded coercion, an
  unspellable type, an unsettled callable constraint, an unresolved cast, a
  free type variable, an uninstantiated mapping, an undecided capture or
  `constexpr`, ...).
- `Cpp_ir.Resolved` cannot represent any of them.

Lifted helpers and per-declaration results are recorded in the unit program
under stable ids (`Cpp_passes.Unit_program.owner`: a source
`Base.Entity_id.t` or a `Base.Generated_entity_id.t`).

## 7. Typed mappings in the pipeline

A typed mapping is data, read once and compiled once:

1. **Resolution** (`Base.Mapping_discovery`). Lazily, per instantiation:
   every recorded instance with the head is tried by unification; none means
   unmapped, more than one is an ambiguity error naming all of them
   (instance priority is never consulted). The one that applies is decoded
   (`Base.Mapping_decode`, which keeps the argument of `Ref` unreduced),
   validated (`Base.Mapping_validate`) and cached for the extraction.
   `CRANE_TRACE_MAPPINGS=1` reports the discovered heads and every resolved
   descriptor.
2. **Compilation.** `Base.Mapping_plan` compiles a `TypeMapping` once per
   head, from the instance applied to fresh variables: the canonical C++
   type as a structured CppIR type (never text), components, copy, access,
   value and lifetime models, views, constructor build templates and the
   match template built from the constructor views, release plan, numerals.
   `Base.Mapping_operation` compiles an `OperationMapping` once per
   operation: its `ArgumentSpec`s bound to the retained runtime binders in
   source order, `%arg(x)` and `%stored(c)` compiled into the
   `Cpp_ir.Foreign_template` hole vocabulary, and the contract (input uses,
   result, facts, purity).
3. **Analysis.** Access summaries (section 4) read operation contracts;
   ownership reads `Take` and `RetainsArgument`; copy cost and by-value
   reads come from the copy model and read style
   (`Mapping_plan.copies_cheaply`, `read_by_value`), replacing the legacy
   `Crane TriviallyCopyable` table for typed heads.
4. **Lowering and finishing.** A typed head stays an
   `Entity_application` until the `foreign` pass, which writes its compiled
   C++ type. An operation call is lowered by the inline-call path; then
   `shared_args` evaluates every retained argument once, in source order,
   `in_place_args` materialises an argument a callee writes or replaces
   in place when it is not a variable the caller may write
   (`crane::writable(e).ref()`), `view_args` converts an argument taken as a
   view with the mapping's declared conversions (and materialises or refuses
   a borrowed view that escapes its owner), and `deduced_literals` builds a
   string literal as the mapped string object where C++ would deduce
   `const char*`.
5. **Interfaces.** When an extraction finishes,
   `Base.Mapping_interface.record` stores, in the `.vo`, the instance and a
   digest of the physical ABI of every typed head it compiled; a later
   extraction including that unit's header checks them (section 1).

Legacy mappings (`Crane Extract Inductive`, `Crane Extract Constant`,
`Crane Extract Inlined Constant`, `Crane Extract Monad`, ...) take the same
inline path but carry no contract: an inlined constant is opaque to the
access and ownership analyses.

## 8. Finishing: Lowered to Resolved

[`cpp_passes/pipeline.ml`](../src/cpp_passes/pipeline.ml) exposes one
function, `finish : check_control:control_check -> Unit_plan.Context.t ->
Cpp_ir.Lowered.Decl.t -> Cpp_ir.Resolved.Decl.t`, so no intermediate state is
nameable. `Cpp_passes.Unit_program.finish` runs it exactly once per
declaration id, inside `Emit.Files.generate_ahead`, then installs the
program. The passes, in order:

1. Before the seam: `control` (a check: under `CRANE_CHECK_IR` what was
   emitted must be what control lowering recorded), `coercions` (expands
   every `Coerce` node into its adapter, innermost first, discharging
   `Unlowered_coercion`), `local_closures`, `constants`, `temporaries`,
   `shared_args`, `in_place_args`, `view_args`, `deduced_literals`,
   `simplify`, `depth` (flattens initialisers nested deeper than Clang
   parses), `return_moves`, `constraints`.
2. `materialise`: the `Cpp_passes.Erasure` seam, which settles every
   unknown representation; its output type is `Cpp_passes.Erasure.settled`.
3. After the seam: `casts`, `free_tvars`, `boxed_reads`, `template_args`,
   `method_calls`, `projections`, `conditionals`, `access_moves`,
   `constexpr`, `immortal_globals`.
4. Instantiation: `foreign` (mapping text instantiated, typed heads spelled),
   `qualifiers`, `pointer_slots`, `unused_bindings`, `scrutinees`,
   `capture_scrutinees`, `narrow_captures`, `captures`, `initialisers`.

Each obligation is discharged by one named pass (`describe` in
`pipeline.ml` names it). Under `CRANE_CHECK_IR`, `finish` fails if any obligation is
outstanding, if a lowered declaration still holds a plain `auto`
declaration (`check_deduced_bindings`), if the declaration differs from
what control lowering recorded, or if `Cpp_passes.Borrow_projection.check_decl`
or `Ownership_ir.Move_check.check_decl` fails. Loops are not built here.

**Immortal globals.** Under `Set Crane SharedVariant`, `immortal_globals`
wraps the initialiser of each global whose type is not a literal type in
`crane::immortal(...)`: its blocks are never counted or freed. A block's
count is then the constant `immortal` (`~0`, never changed), or, under
`NonAtomicRc` plus `SingleThreaded`, `sticky` (half the range, updated by
plain increments and decrements with no immortality test,
`theories/cpp/shared_block.h`). Static blocks written by `Crane Bake` start
at the same count (`block_detail::born_immortal`).

## 9. Emission

Once the unit program is installed, its header demands are recorded
([`cpp_passes/demands.ml`](../src/cpp_passes/demands.ml)), then the file
layout and synthesised constructor aliases are planned (`plan_file_layout`,
`plan_ctor_aliases`). Both files are rendered before either is opened
(`.cpp` then `.h`; `CRANE_RENDER_ORDER=intf-first` reverses the order to
show that nothing depends on it):

1. [`emit/leaf_plan.ml`](../src/emit/leaf_plan.ml) turns each finished
   declaration into a leaf with what it needs: names to resolve,
   declarations to place ahead of it, synthesised templates.
2. [`emit/files.ml`](../src/emit/files.ml) assembles the leaves into a CppAST
   `translation_unit` ([`cpp_ast/cpp_ast.mli`](../src/cpp_ast/cpp_ast.mli)):
   top-level chunks, module structs, members.
3. `Cpp_ast.schedule` places declarations that are due only once the file
   is assembled; `Cpp_ast.resolve` resolves names at each position
   ([`unit_plan/cpp_names.ml`](../src/unit_plan/cpp_names.ml)).
4. `Cpp_ast.print` writes the file with [`emit/print.ml`](../src/emit/print.ml),
   which reads only resolved CppIR and runs no compiler pass. Module-type
   concepts are planned by
   [`cpp_ast/modtype_concept.ml`](../src/cpp_ast/modtype_concept.ml) and
   spelled by [`emit/concepts.ml`](../src/emit/concepts.ml).

The preamble (includes, namespace) is written after both bodies, so it
follows from what the bodies use. The images of baked constants the unit
declares are checked for staleness (`Driver.Bake_inputs.check`), declared
`extern` in the header and appended to the implementation file. The text is
then laid out by [`emit/layout.ml`](../src/emit/layout.ml) (LLVM style as
clang-format applies it, 80 columns); no external formatter runs, and
`Set Crane Format Style "None"` keeps the printer's text as written.

After rendering the driver checks that rendering decided nothing
(`check_no_late_decisions`), that every planned declaration was emitted
(`Cpp_passes.Unit_program.check_against_plan`, `check_against_ahead`), that
the recorded kinds, template-parameter kinds and names still agree with the
plan (`check_against_plan`), and that the Core program did not change while
rendered (`check_structure_unchanged`, by `Core.Fingerprint`).

### Crane Bake

`Crane Bake c` ([`driver/bake.ml`](../src/driver/bake.ml)) runs the
pipeline above on `c` alone, inside a protected state, with `c`'s
initialiser handed to `crane::bake::root`; it compiles the unit with a
driver whose `main` is `crane::bake::main`, runs it, and records the image
it prints (C++ data) with the constant, together with the digests of every
file the compiler read, `clang++ --version` and `CRANE_BAKE_FLAGS`
(`Driver.Bake_inputs`). A later extraction lowers `c`'s body as usual but
initialises `c` with `crane::bake::read<T>(image)` (CppIR `Baked_value`),
on both the definition and the header-specification path, so the unit plans
and includes what it would without the image. A declaration whose type is
`auto` takes the proxy `crane::bake::value{image}` instead.

Crane runs the generated C++ once because the alternatives fail: C++
`constexpr` evaluation cannot leave a heap allocation in a constant,
`vm_compute` does not finish on large builders (the ParseALot DFA), and the
value written as constructor calls compiles slowly and hits Clang's
expression nesting limit. Two mechanisms keep an image current, since none
of its inputs (runtime headers, the compiler, `CRANE_BAKE_FLAGS`) is a
dependency a build system sees of the `.vo`: `Driver.Bake_inputs` records
the digest of every file the compiler's `-MD` output lists and refuses a
stale image at use, and `theories/RuntimeHeaders.v`
(`scripts/runtime-headers-digest.sh`, a rule in `theories/dune`) carries the
runtime headers' digest in a definition's name, so every file that requires
`Crane.Extraction` is rebuilt when a header changes.

## 10. Checking, tracing and layering

Every switch below is an environment variable read by the plugin, except
where noted.

| Switch | Effect |
| --- | --- |
| `CRANE_CHECK_IR=1` | Turns on every boundary check: Core invariants (`Core_passes.Check`, `Core_passes.Spines.check`), plan determinism, plan-versus-lowering agreement (callables, representation, ownership, control, parameter modes), typed lowering (every Core form lowered with a type, declared binders agree with their values, every adapter agrees with `Coerce.decide`, typed fit), the finishing obligations, move and borrow validation, unit-program completeness, structure unchanged by rendering. Set for all four test folders in their `dune` files. Violations go through `Base.Probe.violation`. |
| typed fit | Under `CRANE_CHECK_IR`, every value put in a destination or argument slot must need no adapter by `Coerce.decide` and have a type related to the slot's, unless the pair is of a class recognised by structure (`Typed_checks.known_class`: `event`, `carrier`, `itreeF`, `promoted`; see §6.1) or its (library, declaration, position, verdict, from, into) entry is in [`unit_tests/typed_fit_allowlist.txt`](../unit_tests/typed_fit_allowlist.txt) (81 entries, grouped by kind; built into the plugin). Each entry is an open type-reconstruction defect. The list may only shrink: a new pair fails extraction and prints its line; `scripts/check-typed-fit-allowlist.sh <probe-log>` lists entries a full `CRANE_PROBE` census no longer hits and counts the structural classes' firings. |
| `CRANE_PROBE=<file>` | Appends a line per firing of an instrumented repair path (`repr-plan`, `elab-fact`, ...), one per allowed typed-fit pair (`typed-fit-allowed`), and one per pair of a structural typed-fit class (`typed-fit-class <kind>`). |
| `CRANE_TRACE_PIPELINE=1` | Reports each stage and pass as it runs, plus program fingerprints. |
| `CRANE_TRACE_PASSES=1` or `=<name substring>` | Reports which finishing passes changed a declaration, with node counts. |
| `CRANE_TRACE_MAPPINGS=1` | Reports discovered typed-mapping heads and every resolved descriptor. |
| `CRANE_TRACE_ACCESS=1` | Prints the parameter access summaries. |
| `CRANE_RENDER_TWICE=1` | Renders both files twice and fails if they differ. |
| `CRANE_RENDER_ORDER=intf-first` | Renders the header before the implementation. |
| `CRANE_COUNT_GENERATION=1` | Reports how many bodies each phase generated. |
| `CRANE_LOOPIFY_DIAGNOSTICS=1` | Same as `Set Crane Loopify Diagnostics`. |
| `CRANE_LOOPIFY_CENSUS=<file>` or `=write:<file>` | Loopify on everywhere, violations logged instead of fatal (`scripts/loopify-census.sh`). |
| `CRANE_BAKE_FLAGS="<flags>"` | Extra `clang++` flags for `Crane Bake`, after `Set Crane Bake Flags`; recorded with the image. |
| `CRANE_COUNT_RC=1` | Uses the counting shared pointer of `count_rc.h` (measurement; not with `NonAtomicRc`). |
| `CRANE_STAMP=1` | Writes a digest of the plugin binary as a comment at the top of every generated file. |
| `CRANE_DBG_DROPPED_ARGS`, `CRANE_DBG_UNSPELLABLE`, `CRANE_DBG_LIFTED` | Diagnostics for dropped call arguments, unspellable types and lifted-helper placement. |
| `CRANE_CPP_OPTIMIZATION`, `CRANE_CPP_SANITIZE`, `CRANE_PCH_DIR` | Read by the test scripts (`scripts/compile-*.sh`), not the plugin: optimisation level (default `O0`), sanitizer, precompiled-header directory. The test suite also compiles with `-DCRANE_STRICT_ARITY`. |
| `unit_tests/pipeline_manifest.expected` | Golden of every pass list, from `Base.Pipeline_trace`. |
| `scripts/check-module-deps.sh` | Enforces layering: each directory names only those before it; Core, ControlIR and CppIR depend on no stage; only `Cpp_passes.Pipeline` converts CppIR to the resolved phase; the printer reads only `Cpp_passes.Erasure` of the finishing passes and nothing of lowering; only `Core_to_cpp.Coerce` builds coercions. `bin/printer_reads` lists the `Base.Table` reads the printer still makes; the list may only shrink. |

## 11. Terminology

| Name | Meaning | Code |
| --- | --- | --- |
| PCUIC | Rocq's kernel calculus, Crane's input | Rocq kernel terms |
| Core | Crane's typed functional IR after erasure, at phases extracted, optimized, frozen, normalized | `Core`, `Core_passes.Phase` |
| ProgramFacts | analysis results, whole-program and per unit | `Driver.Program_facts` |
| TargetPlan | backend decisions for a unit, with callable, representation, position and recursion plans | `Driver.Target_plan`, `Core_plan.Callable_abi`, `Core_to_cpp.Representation_plan`, `Core_to_cpp.Position_plan`, `Core_plan.Recursion` |
| ControlIR | explicit loops and machines over Core terms | `Control_ir`, `Core_to_control.Lower_control` |
| OwnershipIR | planned moves, copies, borrows, captures, reuse | `Ownership_ir.Region` |
| Typed mapping | a `TypeMapping` or `OperationMapping` instance, compiled to a plan | `Base.Mapping_plan`, `Base.Mapping_operation` |
| CppIR | structured C++, phases Lowered and Resolved | `Cpp_ir` |
| Value type, slot type | the type lowering gives a value, and what its position asks of it | `Cpp_ir.Lowered.Value_type`, `Cpp_ir.Lowered.Slot_type` |
| Coercion | the one adapter between a value type and a slot type | `Core_to_cpp.Coerce`, `Cpp_passes.Coercions` |
| Unit program | a unit's finished declarations by stable id | `Cpp_passes.Unit_program` |
| CppAST | a file as a scheduled, named tree | `Cpp_ast` |

In one sentence: Crane extracts Rocq terms into Core, optimizes, freezes and
normalizes it, analyses and plans the program, lowers it with types,
explicit control and ownership into CppIR, resolves every representation
obligation, and assembles, schedules, prints and lays out the result as C++.

### Trust boundary

Rocq verifies the source declarations; Crane is not a verified compiler. It
relies on regression tests, compiling and running the generated C++, the
`CRANE_CHECK_IR` boundary checks, static analysis, differential testing and
reviewable output. Typed mappings are trusted to obey the contracts they
declare: Crane checks their shape, holes and capabilities, the C++ compiler
checks the emitted types, and nothing checks that a `Read` operation does not
write. Distinguish "the source program is kernel checked" from "the
extraction is proved correct".
