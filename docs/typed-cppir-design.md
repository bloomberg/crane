# Typed CppIR: expression types and one coercion

Status: design. Branch `typed-cppir`, from `typed-mappings` d7c3f9fdc.
Goals: elegant, DRY, nanopass (small passes with explicit input/output
languages and invariants, phase-indexed IR), and illegal states
unrepresentable. All non-wip tests keep passing, byte-identical unless a
change is a deliberate improvement committed on its own.

## 0. The problem

A Rocq function type has two C++ spellings, chosen by
`Cpp_ir.Types.arrow_site` (`src/cpp_ir/types.ml`):

- Flat, where a declaration writes it: `Function ([A; B], R)`, printed
  `crane::fn<R(A, B)>`.
- Curried, where a type variable stands for it:
  `Function ([A], Function ([B], R))` (`spell_arrows Through_tvar`).
- `Declared_at n`: flat for the first `n` arguments, curried after.

`Type.t` can tell the two apart; lowered expressions cannot. `gen_expr`
(`core_to_cpp/expr.ml`, typed in `core_to_cpp/knot.ml:lowering`) is
`Lowering_state.t -> ?expected_ty:Lowered.Type.t -> ?slot:Slot.slot -> env
-> Core.Expr.t -> Lowered.Expr.t`. A type is pushed down, partly
(`expected_ty` optional, falling back to the ambient
`Lowering_state.current_cpp_return_type` via `Coerce.position_cpp_ty`), and
nothing comes back up. Every crossing site therefore infers the value's
grouping from the syntax of what it just built, or from Core. Each fuzzing
round found a new uncovered (source form, slot form) pair.

Per-boundary adapters and guesses this design replaces:

| # | Site | What it guesses or adapts |
|---|---|---|
| 1 | `coerce.ml:regroup_value`, from `expr.ml:gen_expr` (`Bound_variable`, ~l.242-250) | curried local read into a flat slot |
| 2 | `coerce.ml:curry_value_to_expected` (`expr.ml` ~l.238, ~447; `calls.ml:curry_to_expected`; `match.ml:gen_record_projection` ~l.1691) | flat global/local into a slot with fewer domains |
| 3 | `coerce.ml:grouped_lambda`, from `local_functions.ml` ~l.1424 with `position_cpp_ty cx None` | partial application closure grouping from the ambient return type |
| 4 | `coerce.ml:eta_expand_to_expected`, from `lambda.ml` ~l.957 | lambda shorter than its slot |
| 5 | `coerce.ml:mk_arity_call` (`local_functions.ml` ~l.1006, ~1458; `match.ml` ~l.1926) | applying a callee of known arity |
| 6 | `coerce.ml:apply_at_site`, `calls.ml:codomain_site`/`call_result_site`, `application.ml` `wrap_excess`/`chain_excess` (~l.852-1007) | grouping of extra arguments, guessed from Core |
| 7 | `coerce.ml:regroup_crossing`, from `application.ml` ~l.779, ~1733 | containers of functions crossing arrow sites (`Convert`) |
| 8 | `coerce.ml:name_fn_arg_for_tvar_param`, from `local_functions.ml` ~l.993 | `Lambda` at a type-variable parameter becomes `Function_value` |
| 9 | `application.ml:gen_call_args` ~l.343-361 (aedc4bbba, 498067038, b2f630668) | inline mapping callable argument at a type variable becomes `Converting_construct`/`Function_value` |
| 10 | `application.ml:gen_call_args` ~l.301-325 | lambda return annotation and `Shared_pointer` codomain wrap |
| 11 | `coerce.ml:erase_fn_arg_for_param`, `convert_carrier_arg` | erased-domain callables, carrier element conversion |
| 12 | `coerce.ml:coerce` and wrappers `unbox_into`, `unbox_value`, `recover_boxed_result`, `recover_boxed_component`, `box_for_any_slot`, `deep_box_list`, `recover_carrier_result` | box, unbox, erase, recover |
| 13 | `match_types.ml:joined_at`, `iife_closure_return_at`, `value_iife` (`expr.ml` ~l.281, 521, 526; `match.ml` ~l.1573, 2000; `effects.ml` ~l.57) | join of branch callables by scanning returns syntactically |
| 14 | `calls.ml:spell_as_declared` | grouping a callee parameter is declared at |
| 15 | `types.ml:let_value_result` (acc1c2985), `stmts.ml` ~l.285-330 | a let RHS slot; `Existing` binding type from a lambda's params |
| 16 | `stmts.ml` ~l.463/481 and six `k (Literal (Int 0))` probes in `core_to_cpp` | what kind of slot a continuation is, by calling it on a dummy |
| 17 | `expr.ml:gen_crossing` (~170 lines) | Core `Coerce`/`Boxed_value` boundaries, a separate decision tree |
| 18 | `control_to_cpp/frame.ml:collect_type_env` (`Declare (Auto,_), Lambda`), `decltype_of_saved_local` | frame field types recovered after the fact |
| 19 | `cpp_passes/view_args.ml:declared_holdings`, `read_back` | what an expression holds, from declarations and `decltype` |

Unused safety net: `theories/cpp/fn.h` provides `crane::regroup<Into>(f)`;
no compiler module emits it. The suite compiles with `-DCRANE_STRICT_ARITY`
(`scripts/compile-std.sh`), removing the implicit regrouping constructor, so
a missed crossing shows up only as a clang error.

## 1. The type of a lowered expression

`Type.t` names declarable types. An expression type also needs:
unnameable callables (a lambda's closure type; a global function's name as a
pointer or overload set), bottom (`Abort` fits every slot), and honest
deduction (verbatim text and runtime helpers; today `Call.Untyped`, `Auto`,
or a missing `?from`).

New families in `src/cpp_ir/grammar.ml` (recursive with `Type` and `Expr`;
re-exported from `cpp_ir/value_type.ml`, `slot_type.ml`, `coercion.ml`):

```ocaml
and Arrows : sig
  (** How a callable takes its arguments: [groups] in call order, each group
      one C++ call; never empty ([[[]]] for nullary). Flat
      [crane::fn<R(A,B)>] is [[[A;B]]]; curried is [[[A];[B]]]. *)
  type 'p t = { groups : 'p Type.t list list; result : 'p Type.t }
end = Arrows

and Deduction : sig
  (** Why only C++ knows a type: a closed list of honest admissions. *)
  type t =
    | Foreign_text
    | Runtime_helper of Crane_rt.helper
    | Generic_lambda
    | Requirement
    | Not_yet_typed            (** phases A-C only; deleted in phase D *)
end = Deduction

and Value_type : sig
  type 'p t =
    | Typed of 'p Type.t           (** exactly this nameable type *)
    | Closure of 'p Arrows.t       (** a lambda's own type *)
    | Function_name of Names.GlobRef.t * 'p Arrows.t
    | Never                        (** an abort *)
    | Deduced of Deduction.t
end = Value_type
```

Synthesis rules (each form module implements its rows):

| Expression | `Value_type` | Source |
|---|---|---|
| `Local x` | `Typed t` | binder table (`Binders.binder_cpp_type` / `planned_binder_type_or_derive`); a deduced callable parameter (`F&&`) is `Typed (Function ...)` at the `Invocable` grouping from `Core_plan.Callable_abi` |
| `Entity` of a function | `Function_name (g, arrows)` | `callee_core_type` through `Types.cpp_of_core`, grouped as declared |
| `Entity` of a value | `Typed t` | declared type |
| `Call` | callee result after the groups consumed (fewer groups: `Typed (Function rest)`); globals via `Calls.glob_yields`; `Foreign` via `yields`/`custom_yields` | callee |
| `Lambda l` | `Closure {groups=[params]; result}`; nested `Return (Lambda ...)` adds groups; result is `l.return_type` or the join (3.3) | lambda |
| `Literal`, `Numeral`, `Enum_value`, `Aggregate`, `Converting_construct t`, `Box t`, `Any_cast t`, `Convert t`, `Container_cast t`, `Baked_value t`, `Unbox` | `Typed` of the carried type | node |
| `Function_value e` | `Typed (Function arrows)` of `e`'s closure | operand |
| `Erase_callable shape` | `Typed (Function (Any...))` or `Typed Any` | shape |
| `Move e`, `Forward (_, e)` | type of `e` | operand |
| `Project (_,_,Some t)`, `Member`, `Access` | field type where known (`Constructors`/`Records`), else `Deduced Not_yet_typed` until D | field |
| `Abort` | `Never` | |
| `Foreign_text`, `Runtime h` | `Deduced` | |

Value category is not stored: it follows from the node (`Local` lvalue,
`Move` xvalue, else prvalue); `Typed.category` computes the existing
`Grammar.Value_category`. Ownership stays in `Param_mode` and
`Ownership_ir.Region`; it enters typing only via slots (3.1).

`Arrows.of_type`/`to_type` normalise a `Function` chain; `Arrows.same_function`
(same leaves once flattened) replaces `Cpp_ir.Types.same_arrows` and the local
`uncurried` in `Match_types.joined_at`. Equality goes through
`Types.unfold_cpp_typedef` (as `constructors.ml` ~l.212-225 does).

## 2. Where types are attached

Rejected: a type on every node (`{node; ty}`): ~300 mentions, 77 `Map.make`
and 63 `Map.expr` users, and every finishing pass would have to keep `ty`
correct while reshaping trees (a new bug class). Not enough alone: types only
at boundaries (control lowering and `View_args` read binder types).

Chosen: synthesised by lowering, recorded at boundaries and binders.

1. Lowering returns typed values. New `src/cpp_ir/typed.ml` (not grammar):

   ```ocaml
   type t = private { expr : Lowered.Expr.t; ty : Lowered.Value_type.t }
   val v : ty:Lowered.Value_type.t -> Lowered.Expr.t -> t
   val apply : t -> t list -> t
   val category : t -> Value_category.t
   ```

   Knot entry points become `expr : ... -> Slot.slot -> env -> Core.Expr.t ->
   Typed.t` and `stmts : ... -> Destination.t -> env -> Core.Expr.t ->
   Stmt.t list`. `private`: a typed value can only be built with a type.
2. The boundary is an explicit lowered-only node, like `Suspend`:
   `| Coerce : lowered Coercion.t * lowered t -> lowered t`. `Cpp_ir.Resolve`
   treats it as owed (like `Suspend`, `resolve.ml` ~l.117); a new
   `Representation_obligation.Unlowered_coercion` is discharged by one pass
   (phase B2).
3. Binders keep their type when spelled `auto`: `Binding.Declare (Auto, b)`
   (29 sites) becomes `Binding.Declare_deduced of 'p Value_type.t *
   Core.Binder.t option`; the printer still writes `auto`;
   `Frame.collect_type_env` and `View_args.declared_holdings` read the type.
4. `Call.signature.yields` is filled from the call's `Value_type` (`Yields t`
   or `Untyped`), so `Tmc` (~l.135) and `Erasure`'s `%ret` get it unchanged.

## 3. The single coercion

### 3.1 Slot types

One type replaces `?expected_ty`, the typed fields of `Slot.slot`
(`expected_core_ty` stays as a Core-side refinement for constructors), and
the ambient return type:

```ocaml
and Slot_type : sig
  type _ t =
    | Exactly : 'p Type.t -> 'p t
        (** declared parameter (Param_mode.value_type), variable, field,
            loop variable, frame field, return type; [Any] for an erased slot *)
    | Template_parameter : 'p Type.t option -> 'p t
        (** C++ deduces it: inline mapping [auto], a callee's own type
            variable; the instantiation, curried, where spellable *)
    | Forwarded : 'p t     (** [F&&] *)
    | View : Param_mode.view * Names.GlobRef.t -> 'p t   (** phase E *)
    | Free : 'p t          (** [auto] variable, discarded value *)
    | Join : int -> lowered t
        (** return type of lambda number n, decided from its returns (3.3) *)
end = Slot_type
```

One function per kind of position answers for it:
`Slot_type.of_param : Param_mode.t -> 'p Type.t -> 'p Slot_type.t` for call
arguments (`By_value`/`By_const_value`/`By_const_reference`/`By_reference`
give `Exactly (value_type m t)`, `By_forwarding_reference` gives `Forwarded`,
`By_view` gives `View`); the callee's parameter types from `Calls.plan_call`
at the grouping `Calls.spell_as_declared` gives (which becomes the definition
of a declared parameter's slot); inline custom parameters at a type variable
give `Template_parameter`; fields from `Constructors.regular_field` /
`record_field` / `custom_field`; returns from the destination (3.2); frame
fields and loop variables from `Shadow.ty` in
`control_to_cpp/tail.ml:make_shadow_updates`.

### 3.2 Destinations replace probed continuations

`gen_stmts`'s `k : Expr.t -> Stmt.t` is probed with `Literal (Int 0)` (six
sites) and the ambient `with_cpp_return_type` is set at 31 sites. Both
become:

```ocaml
(* src/core_to_cpp/destination.ml *)
type t =
  | Return of Lowered.Slot_type.t
  | Bind of Names.Id.t * Lowered.Slot_type.t * Core.Binder.t option
  | Assign of Names.Id.t * Lowered.Slot_type.t
  | Discard
  | Custom of (Typed.t -> Lowered.Stmt.t) * Lowered.Slot_type.t
val finish : Lowering_state.t -> t -> Typed.t -> Lowered.Stmt.t (* coerces, builds *)
```

A let RHS (`Types.let_value_result`) becomes `Bind (x, Exactly
(spell_in_scope binder_ty) | Free, b)`.

### 3.3 The coercion node and the decision

```ocaml
and Coercion : sig
  type 'p plan =
    | Regroup of 'p Arrows.t * 'p Arrows.t     (** rows 1, 2 (local), 3, 4 *)
    | Name of 'p Type.t option                 (** rows 8, 9 *)
    | Eta of { declared : 'p Arrows.t; into : 'p Arrows.t } (** row 2 (global) *)
    | Box of 'p Erase_shape.t option
    | Deep_box
    | Unbox of 'p Unbox.t
    | Erase of 'p Erase_shape.t
    | Recover of 'p Arrows.t * 'p Arrows.t
    | Convert of 'p Type.t                     (** rows 7, 11 *)
    | Container_cast of 'p Type.t * bool
    | Then of 'p plan * 'p plan
  type 'p t = { from : 'p Value_type.t; into : 'p Slot_type.t; plan : 'p plan }
end = Coercion
```

No `Identity` plan: the smart constructor returns the expression unchanged.

```ocaml
(* core_to_cpp/coerce.ml, replacing its current contents *)
val decide : Lowering_state.t -> Lowered.Value_type.t -> Lowered.Slot_type.t -> Lowered.Coercion.plan option
val into_slot : Lowering_state.t -> Typed.t -> Lowered.Slot_type.t -> Lowered.Expr.t
```

`decide` uses the context only for alias unfolding
(`Types.unfold_cpp_typedef`, `resolves_to_any_type`,
`Erasure.is_boxed_source`); it is a total function of the two types. First
matching row wins:

| from | into | plan |
|---|---|---|
| any | `Free`, `Forwarded`, `Exactly Void` | none |
| `Never` | any | none |
| `Typed t` | `Exactly t'` equal after unfolding | none |
| opaque on either side | any | none (keeps `classify_erasure`'s `Opaque` rule) |
| boxed | `Exactly` spelled as a box | none |
| boxed | `Exactly t`, `states_unboxed_target t` | `Unbox` (list shape per `Erasure.erased_list_shape`) |
| callable | `Exactly Any` | `Box (Some Boxed_whole)` |
| non-callable concrete | `Exactly Any` | `Box None` or `Deep_box` (`Family_box` list) |
| callable | `Exactly (Function d)` with erased domain | `Erase (At_signature cod)` |
| callable with erased codomain | `Exactly (Function ...)` concrete | `Recover` |
| `Closure a` | `Exactly (Function b)`, `a = b` | none |
| `Typed (Function a)` / `Closure a` | `Exactly (Function b)`, `same_function a b` | `Regroup (a, b)` |
| `Function_name (_, a)` | `Exactly (Function b)`, same, `a <> b` | `Eta` |
| `Closure _` / `Function_name _` | `Template_parameter t` | `Name t` |
| `Typed (Function _)` | `Template_parameter _` | none |
| `Typed t` | `Exactly t'`, non-function, same leaves | `Convert t'` |
| carrier at erased element | `Exactly t'` | `Convert t'` (`convert_carrier_arg`) |
| `Typed t` | `Exactly t'`, other | pointer dimension via `Convert.gen_type_conversion_expr` |
| `Deduced _` | any | none, with a census probe |

Expansion is a pure function in `src/cpp_passes/coercions.ml`:
`expand : Lowered.Coercion.plan -> Lowered.Expr.t -> Lowered.Expr.t`, made of
today's adapter bodies moved unchanged (`regroup_value`'s `_rg` lambda,
`curry_value_to_expected`'s `_ec` nest, `Erasure.converting_ctor`,
`Erasure.unbox`, `Erase_callable`). Captures are planned in one place: an
operand `Move (Local x)` becomes an adapter with `moved = [x]` reading
`Local x` (what `expr.ml` ~l.240, 248 do by hand).

Joins: a lambda's tail returns go to `Return (Join n)`. After the body is
generated, `Match_types.join` decides the return type from the collected
`Value_type`s: one common `Typed t` means deduce (no annotation, as now);
else if the lambda's own slot is `Exactly (Function f)` and the Core
annotation is the same function, `f` (the `joined_at` regrouping rule); else
the annotation's `Function`. A rewrite then resolves `Coerce {into = Join n}`
at that lambda's top-level returns (not inside nested lambdas). Replaces
`joined_at`, `iife_closure_return(_at)`, `value_iife`'s scan, and
`Match.branch_return`'s ambient return type.

Core boundaries: `expr.ml:gen_crossing` becomes: synthesise the inner value,
take `from` from extraction's record or the binder plan (`recorded_from`),
`into` from `Position_plan`, call `Coerce.into_slot`. Its special cases become
`decide` rows. `absurd_coercion` stays a Core question.

### 3.4 Application by grouping

`mk_arity_call`, `apply_at_site`, `chain_excess`/`wrap_excess`,
`call_result_site`, `codomain_site`, and `gen_applied_fix`'s surplus
arguments become one function:

```ocaml
val Typed.apply : Typed.t -> Typed.t list -> Typed.t
(* the callee's Arrows groups take the arguments group by group; a group
   straddled at the end leaves a closure over the rest (the [_sat] lambda);
   arguments past the last group apply to the result at the result's own
   Arrows. *)
```

Each argument goes through `Coerce.into_slot arg (Slot_type.of_param mode
param)` first: the uniform version of fc0c57200, fe074550e, 4aaa3aee2.

## 4. Phasing

Every phase keeps the non-wip suite byte-identical: `git checkout tests &&
git clean -fxq tests && rm -rf _build/default/tests && make test`, then
`git status --short tests` empty. Deliberate output changes are their own
commits naming the changed tests.

**Phase A: types alongside, checked (~+2000 lines; no output change).**
1. Add `Arrows`, `Deduction`, `Value_type`, `Slot_type`, `Coercion` to the
   grammar, re-exports, `Map`/`Children`/`Subterms` cases, `Resolve` owing
   them. `Expr.Coerce` declared, not yet built.
2. Add `cpp_ir/typed.ml`; `Knot.lowering.expr_typed`; `gen_expr` becomes
   `(gen_expr_typed ...).expr` as a shim. Convert form modules one at a time
   in Knot order (`Lambda` < `Application` < `Construction` < `Match` <
   `Effects` < `Local_functions` < `Stmts` < `Expr`); unconverted forms
   return `Deduced Not_yet_typed`.
3. Add `Coerce.decide`, used only by checks.
4. Checks through `Base.Probe` (census under `CRANE_PROBE`, fatal under
   `CRANE_CHECK_IR` once clean): binder agreement; declaration agreement
   (`decide (ty e) (Exactly t)` vs what is there); boundary shadow (each
   inventory adapter's plan matches `decide`'s, classifying produced shapes);
   `Not_yet_typed` census reaching zero. Each "no adapter where decide wants
   one" is a latent bug: file it as a wip test.
Done when: byte-identical, zero violations, zero `Not_yet_typed`.

**Phase B1: one decision, eager expansion (~+900/-300; byte-identical).**
Route every inventory site through `Coerce.into_slot`, expanding immediately.
Plans carry an `origin` tag (`Rg | Ec | Ee | Ue | Sat | Pa`) so adapter name
prefixes stay identical. Introduce `Destination.t` behind `gen_stmts`
(`Custom` wraps remaining continuations). Add unit test
`unit_tests/coercion_decide` over (source: flat global, curried local, lambda,
IIFE, match, let, local-fixpoint partial application, mapping result) x
(slot: declared parameter, type-variable parameter, inline mapping `auto`,
loop variable, frame field, return, let, field, erased) x arities 1-3, and
the same matrix as regression test `callable_crossing_matrix` compiled under
`CRANE_STRICT_ARITY`.

**Phase B2: the node survives to finishing (~+300; byte-identical).**
`into_slot` returns `Coerce (c, e)`. New pass `coercions` first in
`Pipeline.lowered_passes` after the control check expands nodes and
discharges `Unlowered_coercion` (`pipeline.ml:owes`; update
`unit_tests/pipeline_manifest.expected`). First move shape-inspecting
lowering code onto `Typed` or `Expr.under_coercion`: `expr.ml` ~l.299, ~489
(`match built with Call _`), `application.ml` ~l.303, ~347,
`Cpp_build.lift_iife_assignment`, `Lifting.fixpoint_escapes_in_stmts` /
`fixpoint_named_in_returns`, `tail.ml:make_shadow_updates`'s `make_rhs`.

**Phase C: delete the ad hoc adapters (~-2500/+500).** Delete rows 1-8,
11-14 as standalone functions, `Coerce.position_cpp_ty`,
`Lowering_state.current_cpp_return_type`/`with_cpp_return_type`/
`with_iife_return_type`, `Types.let_value_result`,
`Calls.call_result_site`/`codomain_site`, `Match_types.joined_at`/
`iife_closure_return_at`, `stmts.ml`'s lambda-derived binding type, the
`k (Literal (Int 0))` probes, and probe-only `Custom` destinations.
`Frame.collect_type_env` reads `Declare_deduced`; `decltype_of_saved_local`
remains only for `Closure` and `Deduced`. Unifying adapter prefixes is an
optional deliberate commit.

**Phase D: make untyped states unrepresentable (~800 mechanical).** Delete
`Deduction.Not_yet_typed`; remove `?expected_ty` from Knot entry points
(`Slot.slot` carries a non-optional `Slot_type.t`); delete the `gen_expr`
shim (only `Typed.t` crosses lowering modules); replace `Declare (Auto, _)`
with `Declare_deduced`; `Call.result.Untyped` becomes `Deduced` reasons;
`Join` and `Coerce` are `lowered`-only. Extend
`scripts/check-module-deps.sh` so only `core_to_cpp/coerce.ml` and
`cpp_passes/coercions.ml` build `Function_value`, `Erase_callable`, `Box`,
`Any_cast` and adapter lambdas.

**Phase E (optional): consumers.** `View_args` reads `Declare_deduced` and
`Call.yields`; view conversions become `Coercion` plans at `Slot_type.View`
decided at lowering from `Base.Mapping_plan`; `view_args` keeps only the
cross-argument checks. Optionally `Regroup` expands to `crane::regroup<Into>`
(a deliberate output change).

## 5. Impact on other stages

- Control IR (`control_to_cpp/lower.ml`, `tail.ml`, `frame.ml`,
  `loopify.ml`): recursive call arguments are already coerced to parameter
  slots (= shadow types); other shadow updates go through
  `Coerce.into_slot (Exactly shadow.ty)`; frames read `Declare_deduced`.
- Ownership: `Region` unchanged; adapter captures fixed by the operand in
  one place; `Move_check` runs after expansion.
- `Param_mode`: the single input to argument slots (`Slot_type.of_param`).
- Typed mappings: inline mapping argument at a type variable is
  `Template_parameter`; its result is the coerced argument's type, removing
  `call_result_site`'s inline-custom branch.
- Bake: `Baked_value (t, _)` is `Typed t`; the root hand-over is a `Bind`
  destination.
- `Position_plan` returns `Slot_type.t` from the shared `Calls`/
  `Constructors` functions; existing agreement checks cover it.
  `Representation_plan` unchanged.
- `Emit.Print` stays pure and never sees `Coerce`, `Join`, `Value_type`;
  `Declare_deduced` prints `auto`.

## 6. Risks

| Risk | Mitigation |
|---|---|
| Byte-identity of adapter names/shapes | `origin` tag in B1; shapes moved, not rewritten |
| Shape-inspecting lowering code misreads `Coerce` | B2 only after those sites use `Typed`/`under_coercion` |
| `decide` disagrees with an adapter (aliases, `Declared_at n`, erased leaves) | phase A shadow check over the whole suite; B1 unit table |
| Plan-versus-lowering drift | shared `Calls`/`Constructors` slot functions; existing checks |
| Joins change annotation decisions | join rule reproduces "deduce unless returns differ"; acceptance tests below |
| Signature change size (~49 `gen_expr` calls) | phase A shim plus `Not_yet_typed` |
| `Deduced` as an escape hatch | closed reason list, census, phase D layering rule |

Acceptance corpus (byte-identical through every phase): fold_curried_fix_step,
deque_fold_curried_acc, deque_fold_function_acc, deque_fold_fix_init,
loop_acc_curried_partial_app, fix_acc_match_none_erased, fix_acc_empty_erased,
scrutinee_list_return_type, fold_init_curried_branches,
branch_callables_fix_accumulator, nested_fix_alias_result,
boxed_fields_match_arg_obj, three_argument_curried_slot,
nat_iter_function_acc, stm_tvar_of_function, and the new
callable_crossing_matrix.

## 7. Progress

- [x] Phase A (see 8: `typed-fit` stays a census until B1, by design deviation)
- [ ] Phase B1 (in progress: Destination, real-slot fit census, coercion_decide, callable_crossing_matrix, written call types and yields, argument slots, typed local fixpoints, deduced call types, HKT carriers and nested aliases in decide, `Coerce.into_slot` for rows 1, 2, 4, 7, 8, 9, 11, 12, `Typed.apply` for rows 3, 5, 6 and the bound-variable call, rows 10, 13 and 17 done, `Join` slots; census tail and typed-fit fatal not yet; see 8, seventh session)
- [x] Phase B2 (see 8, B2: plans carry their expansion data; `coercions` pass; `Typed.head` is the look-through)
- [ ] Phase C (in progress: steps 1 and 2 done, the ambient return type deleted (threaded `~ret`); step 3 done except the shape-reading lowering sites listed in §4; the result site moved to `Coerce.result_site`, see 8, C/D fourth session)
- [ ] Phase D (in progress: one non-optional slot at the knot and the form functions; `Not_yet_typed` deleted (`Typed.carried`, `of_node ~fallback`); `gen_expr` shim deleted; `Call.yields` is a `Value_type` with `Deduced` reasons; `Declare_deduced` with frame and view readers ported; coercion-builder rule strict (no lowering file outside `Coerce` builds the vocabulary); `Coerce.coerce ?value` for the `Ue` operands that had a value; the `Param` operands, the two `result_site` reads, `Typed.expansion`, typed-fit fatal not done; see 8, phase D seventh session)
- [ ] Phase E (optional)

## 8. Findings

### Phase A

Where the implementation departs from sections 1-4, and why.

- **Grammar.** As designed: `Arrows`, `Deduction`, `Value_type`,
  `Slot_type`, `Coercion` in `cpp_ir/grammar.ml`, re-exported from
  `arrows.ml`, `value_type.ml`, `slot_type.ml`, `coercion.ml` (with
  `Deduction` inside `Value_type`), and `Lowered.{Arrows,Value_type,
  Slot_type,Coercion}`.  `Expr.Coerce` is lowered-only and owed by
  `Resolve`; `Map.coercion` rewrites every type in a coercion and
  `Children` reuses it, so the two cannot drift.  `Slot_type.of_param`
  reads `Param_mode.value_type`.
- **`Typed`.** `cpp_ir/typed.ml{,i}`: the private record, `v`, `typed`,
  `untyped`, `category`, plus `of_node`/`node_type` (the rows of section 1
  a node answers by itself: casts, boxes, conversions, calls with
  `Yields`, aborts, foreign text, runtime helpers, requirements, moves,
  `Function_value`, `Erase_callable`, lambdas with a written or nested
  return type), `rewrap` (a rewrite that keeps the value, such as
  `made_of`), and `or_type`.  `Typed.apply` is left to B1, where it first
  has a caller.
- **Knot.** `lowering.expr_typed` replaces `lowering.expr`;
  `Knot.gen_expr` and `Expr.gen_expr` are the shims.
- **Form conversion is at the dispatcher first.** Each `Expr.gen_form` arm
  returns `Typed.t`.  Arms Expr owns are typed from what they know:
  variable reads from the binder table (`Binders.read_value_type`, the
  declared type without its parameter spelling, or the Core type's
  conversion where it is `auto`), adapters at the slot type
  (`Typed_checks.adapted_to`: a closure grouped as the slot), globals as
  `Function_name` at the declared grouping (`Typed_checks.global_value_type`:
  the first group the declaration takes, the rest of the chain curried) or
  their declared type, literals at their primitive's registered type
  (`strings.pstring.type`, `num.int63.type`, `num.float.type`), numerals and
  enum constructors at their inductive.  Arms that delegate to a form module
  are typed by `Typed_checks.of_built`: the node's own type, and failing
  that the conversion of the Core term's type (a closure grouped as the
  lambda's own parameters where the node is a lambda), each such fallback
  counted under the `typed-derived` probe.  Moving the synthesis into each
  form module (so `Application` holds typed arguments) is B1 work: it is
  what `Typed.apply` and `into_slot` consume, and nothing in phase A reads
  a form module's internal types.
- **`decide` takes its aliases as a record.** `Coerce.decide_with aliases`
  is the total function; `Coerce.decide cx` instantiates it with the unit's
  alias unfolding and box classification, `Coerce.as_written` with the
  structural ones, so the adapters that take no context
  (`regroup_value`, `regroup_crossing`, `eta_expand_to_expected`,
  `name_fn_arg_for_tvar_param`) are shadow-checked too.
- **`decide` follows `coerce`, not the 3.3 table, where the two differ.**
  Measured against what the adapters build (the shadow check), four rows
  of 3.3 were wrong:
  - a boxed value is unboxed into any slot not spelled as a box, a type
    variable included (`coerce` does; `states_unboxed_target` is
    `unbox_into`'s narrower question);
  - a value of unknown type (`Deduced`) is boxed into an erased slot, a
    generic lambda as a callable (`Box (Some Boxed_whole)`) and erased into
    a slot with an erased domain, as `coerce` does for a term it cannot
    type;
  - "opaque on either side" is opaque *source* only: `coerce` unboxes into
    and erases into slots with undecided parts.  A slot with an undecided
    part takes nothing out of a type boxed only by an alias (a class
    instance type such as `ReSum<erased, erased>`);
  - the pointer row is only a `Shared_pointer` on exactly one side; types
    that are otherwise unrelated get no plan (`Coerce.unrelated` reports
    them, for diagnostics).
  Types compare after `Coerce.normal`: aliases unfolded, `const` dropped, a
  type variable by the name C++ spells it under (`Index (2, Some T1)`,
  `Index (1, None)` and `Named T1` are one type), an inductive without its
  namespace wrapper, then `cpp_ty_eq` or structural equality.
- **Implicit plans.** `Coerce.implicit from plan`: C++ performs `Box None`
  (the box's converting constructor) and the erasure of a callable whose
  domain is already erased or which is generic (`crane::fn` at the erased
  signature takes it).  A value left without such a plan is well-formed;
  the checks count it as `fits-implicitly`.
- **Checks.** Under `CRANE_PROBE`: `typed` (form x kind of type, the
  `Not_yet_typed` census), `typed-derived` (fallbacks to the Core type),
  `typed-fit` (at every `gen_expr_typed` exit with an `expected_ty`, whether
  `decide` finds the value fits), `typed-agree` (declaration agreement at
  the two bind declarations of `Effects.gen_bind_stmts`), `typed-shadow`
  (each inventory adapter that built something different from its input,
  against `decide`'s plan kind; `coerce` classified by the shape it built,
  `Coerce.coerced_kind`, a lambda's own type read from its node).  A slot
  mentioning type variables, a slot with no type, a generic slot, and an
  untyped value are counted `unchecked`: the slot is the callee's own
  variables (`Template_parameter` in B1), not comparable to a value typed in
  the caller's scope.
- **Binder agreement is at the declarations lowering builds from a typed
  value.** A let's right-hand side reaches its `Declare` through `gen_stmts`'
  continuation as a bare expression, so it cannot be checked before B1's
  `Destination.Bind`; the bind declarations can, and are.
- **No latent bug found yet.** Every remaining `typed-fit` plan was traced
  to a synthesis inaccuracy, not to missing output: a `Call.yields`
  recorded at the flat spelling where the call is instantiated curried
  (`hkt_curried_pure_arity`: `pure<crane::fn<crane::fn<Nat(Nat)>(Nat)>>`),
  a Core-derived `erased` for a call C++ instantiates concretely
  (`interp_state_case_handler`, `interp_state_after_interp`), a generic
  lambda the caller wraps in `crane_erase_fn` after `gen_expr` returns
  (`erased_index_fun_type`).  The suite compiles under
  `CRANE_STRICT_ARITY`, so a missing regrouping in a passing test is a
  compile error, not a latent bug: latent bugs can only hide behind
  implicit conversions, and none has turned up.  No wip test was filed.

### Phase A, second session

- **Typing moved into the form modules where the information is.**
  `Lambda.gen_lambda` returns `Typed.t`: the closure over its emitted
  parameters, its result the type C++ deduces from its `return`s where
  their nodes agree, else the body's type read *with the body's binders
  in scope* (a variable at its binder's type, anything else at its Core
  type; parameters folded in from a fixpoint body take their arrows off
  it); a thunk call `[]{...}()` is its body's type.
  `Application.gen_instance_projection` and
  `gen_singleton_dictionary_call` return `Typed.t` at the member's
  codomain: `Elaborated_call.static_projection` records `codomain`, from
  the same instantiated type as `domains` (`Query.projection_type`), and a
  singleton dictionary call substitutes the dictionary's carrier into the
  method's declared type.  A custom constant without a Core type
  (`Crane Extract Inlined Constant`) is `Deduced Foreign_text`; an inline
  constant's value is typed by its `glob_yields`.  `Typed.node_type`:
  `Erased_call` is `Typed Any`.
- **`Typed_checks.core_type_of` reads more of the term.** Under a lambda
  or a let it pushes the binder (`with_scope`, so nothing leaks); literals
  at their registered primitive types; a persistent array at
  `Corelib.Array.PrimArray.array` (which registers no name); a fixpoint at
  its selected member's type; any application whose head is typed, by
  stripping its arguments; a static projection at the recorded codomain.
  A local's call that Core cannot type is typed from the binder's C++
  type (aliases unfolded) by `Typed_checks.applied`, the grouping rule of
  `Typed.apply` (groups consume arguments, a straddled group leaves a
  function of the rest).  `[tt]` applied (only an impossible dependent
  branch writes it; `Coerce.absurd_coercion` turns its crossing into an
  abort) is `Never`.  A sequential bind's action yields the monad's last
  type argument, once leading type-binder arrows are dropped
  (`emptyVec int` keeps an erased `A ->` after its instance argument).
- **`decide` and its comparisons.** `Coerce.normal` unfolds aliases at
  every node (nested `key<>`, `priqueue<>`, `uf<>` used to compare
  unrelated) and drops references, so a closure's `const T&` parameter
  compares as `T` (`normal_arrows`).  A box is read through the slot *as
  written* (`Erasure.spells_as_any` before unfolding), as `coerce` does:
  unfolded with no environment, an alias over an instance member type
  (`memM<_tcI0::mm_state::state>`) wrongly read as `std::any`.  New row: a
  `Function_name` whose signature keeps an undecided part (a rank-2
  template, `Rank3Handler`) is named through `Eta` even at the same
  grouping, since a template's name is no value.  `Coerce.unrelated`
  treats an erased or undecided part on either side as agreeing.
- **The 13 shadow disagreements.** 10 were `coerce` wrapping a value that
  is a `std::any` already (directly or through an alias such as
  `SemVal<>`) in `std::any(...)`: C++'s converting constructor excludes the
  box's own type, so that is the identity, and the shadow now reads it as
  no coercion (`kind = ["box"; "none"]`).  1 (`hk_class_field_result_
  cast_to_concept`) was `decide`'s unfolding, fixed above.  2 were
  `curry_value_to_expected`: `Rank3Handler` is the template row above;
  `PolyRank2RecordField` passes the *record* `mapper` as the slot of the
  field's value, a slot no callable fills, which the shadow now counts as
  `unchecked (slot is no callable's)`.  No output changed.
- **Deviation: `typed-fit` is not a slot check, so it stays a census.**
  Phase A's done criterion assumed `?expected_ty` at a `gen_expr_typed`
  exit is the slot the value fills.  At many call sites it is not: a let's
  right-hand-side lambda reached with the enclosing return type
  (`mem_safety_probe14.two_closures`: `closure (nat)->nat` "into" `nat`),
  a record field's value with the record type, a `Npos` constructor with
  the `N` it builds.  The 2131 `unrelated` and 912 planned verdicts left
  measure that as much as synthesis; driving them to zero means giving
  every position a `Slot_type`, which is B1 (`Destination`, `of_param`).
  The checks that are fatal under `CRANE_CHECK_IR` (`Base.Probe.violation`)
  are the three whose slot is a real one: `typed lowering` (a value
  without a type), `binder agreement` (the bind declarations of
  `Effects.gen_bind_stmts`), and `coercion shadow` (an inventory adapter
  that built something other than `decide`'s plan).
- **Latent bugs.** None found: no fatal check fires on the suite, and the
  remaining `typed-fit` plans trace to misdescribed positions or to a
  call typed from Core where C++ instantiates concretely (next item).

### Phase A status (2026-11-22, end of second session)

First session: grammar families (`38b874e49`), typed lowering, `decide`
and probes (`d42a8e8dd`), census refinement (`1510324a6`).  Second
session: form-module typing (`aff6eb10e`), the fatal checks
(`b52b07fab`).  Extraction byte-identical (`git status
--short tests` empty; the same 2 wip extraction errors as the base,
`rocq_bug_3287`, `fibst_cofix_repro`).  `make test` from clean: 1525
passed, 16 failed, all in `tests/wip`; `dune build @unit_tests/runtest`
and `scripts/check-module-deps.sh` pass.

| probe | first session | now |
|---|---|---|
| `typed` `Not_yet_typed` | 1903 | 0 (fatal) |
| `typed-agree` | 2500 fit, 36 unrelated | 2536 fit (fatal) |
| `typed-shadow` disagree | 13 sites | 0 (fatal); 2369 agree |
| `typed-fit` unrelated | 4437 | 2131 (census) |
| `typed-fit` planned | 1011 | 912: unbox 596, erase 284, eta 16, box 8, convert 8 (census) |

Known synthesis gaps feeding `typed-fit` (to fix as B1 gives slots):
- A call typed from Core where C++ instantiates it concretely: `ReSum_inl`
  / `ReSum_id` / `subevent` / `interp` yield `ReSum<erased,erased>` or
  `erased` by their Core type, while the call names concrete template
  arguments.  Design 2.4's fix stands: take `yields` from the callee's
  declared C++ result at the call's written template arguments
  (`Calls.written_at_variables` gives them by variable).
- Constructor values: `Construct` falls back to its Core result type,
  which loses the instantiation a factory call writes (`prod<>` against
  `prod<any,any>`), and a constructor a mapping rewrites (`Npos p` is `p`).

Next: Phase B1 as designed, starting with `Destination.t` behind
`gen_stmts` (so a let's right-hand side has its `Bind` slot) and
`Slot_type.of_param` at call arguments; once every `gen_expr_typed` call
passes a real slot, `typed-fit` becomes the fit check and can be made
fatal.

### Phase B1, first session (2026-11-22)

Done:
- **`Destination.t` behind `gen_stmts`** (`core_to_cpp/destination.ml`):
  `Return of Slot_type.t | Return_void | Assign of Id.t * Slot_type.t |
  Discard | Adapted of (Expr.t -> Expr.t) * t | Custom of {build; into;
  returns}`.  `finish cx d x` checks the typed value against the slot and
  builds the statement; `finish_inlined` inlines an invoked lambda's
  returns where `d` returns (was `Cpp_build.inline_iife`, now
  `Cpp_build.inline_returns`).  The three `k (Literal (Int 0))` probes are
  gone (`returns`, `discards`).  Deviations from 3.2: no `Bind` (a let's
  right-hand side is an `Assign` to the variable declared before it, which
  `Stmts` folds into a declaration when it is one statement, as before);
  `Return_void` is its own case (`return_into_void` drops a pure value, so it
  is not `Return (Exactly Void)`); `Adapted` is the unbox
  `gen_cpp_custom_body` puts before a template-parameter return, to become
  a `Coerce` in B2; `Custom` builds from an `Expr.t` (a suspension, a
  reified `ret`) and states `returns` itself.
- **Destinations are honest, the ambient is not touched.**  A lambda whose
  position states no signature returns to `Return Free` (the ambient still
  holds the enclosing function's result for its legacy readers); a let's
  right-hand side is `Assign (x, let_value_result)` on both let paths.  The
  tail still passes the ambient as `?expected_ty` and recovers boxes at the
  ambient: switching those to the destination is phase C (it changes output
  where they differ).  `dest-ambient` counts where they differ.
- **`typed-fit` is a check at real slots**: `Typed_checks.fit` at every
  `Destination.finish` and at every global call argument
  (`Application.gen_call_args`) against its parameter: `Forwarded` for a
  deduced callable, `Template_parameter` for an inline mapping's parameter
  at a type variable, else `Exactly` the parameter at the call's
  instantiation (`Calls.argument_position.expected`).  The argument check
  sees the argument after its adapters (`Typed_checks.adapted`).  The old
  per-exit census is `typed-expected` (the expected type is not a slot).
- **`decide`**: a mapped inductive with no arguments compares as its
  mapping's C++ type (`positive`/`N` both `unsigned int`; 264 false
  `unrelated`); the name of a function taking a callable is `Eta` at any
  grouping (a deduced `F&&` parameter makes it a template;
  `curry_value_to_expected` always expands it).  The second row was a real
  `decide` gap the new matrix test hit (fatal shadow disagreement).
- **Tests**: `unit_tests/coercion_decide_test.ml` (8 sources x 9 slots x
  flat/curried x arity 1-3, plus the template-name row);
  `tests/regression/callable_crossing_matrix` (7 sources x 8 slots at two
  arguments, 4 x 7 at three; compiled with `-DCRANE_STRICT_ARITY` like the
  whole suite, `scripts/compile-std.sh`).  Both pass.

`typed-fit` census after this session (extraction of the whole suite,
`0c73f034b`):

| site | fits | implicit | unchecked | unrelated | planned |
|---|---|---|---|---|---|
| destination | 121987 | 688 | 74418 | 643 | 128: erase 84, unbox 20, eta 16, box 8 |
| argument | 47813 | 520 | 143791 | 288 | 436: unbox 412, erase 16, convert 8 |

Unchecked: at destinations 44527 slots at type variables (the callee's or
lambda's own variables: `Template_parameter` from the declared
signature), 27746 untyped values (`Typed.of_node` of a local fixpoint's
call or name and of an inlined invoked lambda's returns: type them from
the fixpoint's arrows / the lambda body's typed returns), 2145 slots
stating no type; at arguments 125559 slots stating no type
(`argument_position.expected = None`: the parameter's type is not
computed when nothing needs it; compute it for every regular argument)
and 18011 at type variables.  `dest-ambient`: 1260 of 197860 tails
disagree (the honest lambda and let destinations).

Remaining misses, by cause (each to fix before `typed-fit` is fatal):
- All 432 planned `unbox` are a value typed `erased`/`ReSum<erased,erased>`
  from Core where C++ instantiates the call concretely: goal 3, `yields`
  from the written template arguments.  Plan: in `Application.eta_fun`'s
  global branch `Calls.lower_call` returns `written_by_var`; substitute
  them into the callee's codomain converted with its own variables
  (`Cpp_ir.Types.substitute`), and type the call with it (in the `Typed.t`
  first; writing `Call.yields` feeds `Tmc` and `Erasure`'s `%ret`, check
  byte-identity separately).  This needs `gen_application` to return
  `Typed.t` (it is wrapped by `form` in `Expr.gen_form` today).
- `unrelated` at destinations, largest groups: constructor
  values typed at their Core result (`lifted_param_const_v_mut`
  `option<prod<T1,..>>`, `cpu_emulator` `nat` into a record: a record
  field projected); calls whose result is a function partially applied
  (`partial_app_prefix_work`, `fold_step_list_match_const_v_mut`: `nat`
  into `fn(nat)->nat`, the call's `yields` is the codomain after all its
  arguments).
- `unrelated` at arguments: `TVar<fn>` into `TVar<nat>`
  (`stm_tvar_of_function`), `future<nat>` into `future<prod>`
  (`parallel`): the parameter slot of an effect primitive read from the
  wrong instantiation; lambdas returning an alias of a function
  (`function_alias_spelling`, `state_monad_type_synonym`, `monadic`):
  compare after unfolding the closure's result alias.

Not started: goal 4 (route every inventory adapter through
`Coerce.into_slot` with eager expansion and origin tags), the remaining
ambient readers (phase C), B2.

Destinations still built from the ambient (`Destination.return_ cx`):
match-branch and expression IIFEs (`Match`, `Expr`, `Effects`) and
instance method bodies; each is inside the `with_cpp_return_type` that
states its result, so they agree today, but they should take the slot
from the caller explicitly before phase C deletes the ambient.

Commits: `eb4b70e95` (Destination, fit census, decide rows, tests),
`0c73f034b` (let and lifted-lambda slots).  Full `make test` from clean
after `eb4b70e95`: 1526 passed, 16 failed (all `tests/wip`, as at the
base), `git status --short tests` empty; extraction byte-identical after
`0c73f034b`; `dune build @unit_tests/runtest` and
`scripts/check-module-deps.sh` pass.

Next, in order: (1) goal 3 as above; (2) the unchecked categories (argument
slots for every parameter, typed local-fixpoint values); (3) the
`unrelated` causes listed; (4) `typed-fit` fatal, filing any genuine miss
in `tests/wip`; (5) goal 4.

### Phase B1, second session (2026-11-22)

Done (next-steps 1 and 2 of the first session, and part of 3):
- **Goal 3: a global call is typed at its written codomain.**
  `Application.eta_fun` returns `Typed.t`; a saturated call (no excess
  arguments, one argument per domain of `written_fn_ty`) is typed at the
  callee's declared C++ codomain substituted with the template arguments
  the call writes (`written_fn_ty`, which the `regroup_crossing` of the
  result already computed), a regrouped result at its `Convert`.
  `Call.signature.yields` is filled from it (`Calls.record_call_sig
  ?written`), so `Tmc` and `Erasure`'s `%ret` read the written type; no
  output changed.
  `gen_application` returns `Typed.t`: the call's type where nothing
  recovered it from a box afterwards and the term is no action of a
  sequential monad (`Typed_checks.sequential_action`, split out of
  `of_built`), else `of_built`.  A kept closed instance call
  (`Runtime (Constant ...)`) is the value it builds.  Planned `unbox` at
  arguments: 412 -> 32.
- **Every regular argument has a slot** (`Calls.argument_slot`): the
  callee's declared parameter (Core type at the *unsubstituted* position)
  converted and substituted with the written template arguments; a slot
  in which a variable the call leaves to C++ remains is
  `Template_parameter` (honestly deduced), as is every parameter of a
  mapping (inline: its text takes the argument as it comes; a non-inline
  custom has no declaration of ours).  A deduced callable is `Forwarded`.
  This replaced `argument_position.expected` as the slot, which is the
  type the argument is *generated against* and was `None` for 125559
  arguments.  Deviation: `expected` stays what is passed down as
  `?expected_ty` (changing it changes output; phase C).
- **Typed local fixpoints.**  `Local_functions.gen_applied_fix` types the
  lifted call, the in-place call and the partial application from the
  member's Core type after the arguments given (`applied_type`); the
  standalone wrapper is a closure over the member's arrows;
  `Destination.finish_inlined` types an inlined lambda's returns at the
  lambda's type where their node says nothing.  Untyped values at
  destinations: 27746 -> 112.
- **`decide` reads a variable by index as the scope names it**
  (`Coerce.aliases_in`): `Index (1, None)` is `Index (1, Some A)` where
  the scope's first variable is `A`.  No shadow disagreement appeared.
- **Census detail.**  A slot at type variables reports the verdict
  `decide` gives inside it (`unchecked (slot at type variables: fits)`),
  since after substitution most such slots are the caller's own
  variables and comparable.

`typed-fit` census after `b4a9abdfa` (whole-suite extraction):

| site | fits | implicit | deduced/forwarded | tvar slot (fits / other) | no type | untyped | unrelated | planned |
|---|---|---|---|---|---|---|---|---|
| destination | 143024 | 720 | - | 48513 / 2436 | 2304 | 112 | 627 | 128: erase 84, unbox 16, eta 16, box 8, regroup 4 |
| argument | 84258 | 694 | 71910 / 19772 | 15088 / 234 | 0 | 221 | 611 | 60: unbox 32, convert 12, erase 12, eta 4 |

Remaining causes, measured (all synthesis or slot inaccuracies; none is
missing output, the suite compiles under `CRANE_STRICT_ARITY`):
- Slots at type variables, `unrelated` 2412 at destinations: the value
  typed in a different numbering than the slot (`T2` into `N:T1`: a
  lifted fixpoint's or lambda's own variables renamed; `list<T1>` into
  `list<T1:A>` where both are named), and HKT carriers spelled two ways
  (`app(T1)<T3>` against `app(_tcI0::m)<T3>`).  To fix: type values in the
  scope's numbering (`Lowering_state.with_type_vars` at the lifted
  fixpoint and eta-lambda), then drop the "slot at type variables"
  exemption.
- Module-level type aliases `decide` cannot unfold: `uf<>` (a
  `Definition` over `NatMap.t`), `NatMap.value<>`/`key<>` (a functor
  argument's type member); `Types.unfold_cpp_typedef` reads only
  `Base.Table.lookup_typedef_unchecked`.
- Indexed events applied: `app(getE)<nat>` against `getE` (a family with
  an erased index is its constructor; normalise `Apply` of a
  non-template head).
- Constructor values at their Core result: `itreeF<>` for an itree
  constructor (`RetF`/`VisF` through the coinductive), `prod<>` against
  `prod<any,any>`, `nat` into a record (a projected field).
- Lambdas returning an alias of a function (`st<Z>`,
  `State<nat,nat>`): `unrelated` although both sides print alike;
  `Coerce.unrelated`'s `curried_agree` flattens the alias on one side
  only.
- Effect primitives' parameter slots at the wrong instantiation
  (`TVar<fn>` into `TVar<nat>`, `future<nat>` into `future<prod>`):
  their written arguments are recovered from the expected result.

Commits: `de7931527` (written call types, argument slots, typed local
fixpoints), `b4a9abdfa` (mapping arguments deduced, variables by index),
`530d956cf` (yields from the written codomain).  Extraction byte-identical
after each; full `make test` from clean after `530d956cf`: 1526 passed,
16 failed (all `tests/wip`, as at the base), `git status --short tests`
empty; `dune build @unit_tests/runtest` and `scripts/check-module-deps.sh`
pass; no `CRANE_CHECK_IR` violation, `typed-shadow` 2485 agree / 0
disagree.

Next, in order: (1) type values in the scope's numbering (lifted
fixpoints, eta-lambdas) and drop the "slot at type variables" exemption;
(2) the remaining `unrelated` causes above (module aliases, applied
indexed events, constructor values, function-alias closure results,
effect-primitive slots), and destinations built from the ambient taking
their slot from the caller; (3) `typed-fit` fatal, filing any genuine
miss in `tests/wip`; (4) goal 4.

### Phase B1, third session (2026-11-22)

Done:
- **Type variables in the scope's numbering, partly.**  The largest
  group of "slot at type variables, unrelated" (2412 at destinations) was
  not a renaming in lifted fixpoints: it was (a) a call whose type
  arguments C++ deduces (no `written_by_var`), typed at the callee's own
  variables -- a methodified `fold_left`'s recursive call yielded the
  callee's `T1` (its accumulator) inside a method whose scope numbers the
  accumulator 2 -- and (b) HKT carriers, a function's own variable that
  `Decl_state.apply_hkt_resolutions_stmts` rewrites to `typename
  _tcI0::m` only after the body is lowered.  Fixes:
  `Cpp_ir.Types.deduce` is C++'s template argument deduction (a callee's
  declared parameters matched against the typed arguments, arrows
  compared curried); `Application.gen_call_args` returns `Typed.t`, and a
  global call whose codomain's variables are all written or deduced is
  typed at it (`deduced_fn_ty`; only typing reads it, the `Convert` of a
  crossing still reads `written_fn_ty`).  The HKT resolutions are
  lexical state (`Lowering_state.with_hkt_resolutions`, set where
  `Functions` lowers a body) and `Coerce.aliases_in` reads a resolved
  variable as its member.  2412 -> 159.
- **One alias unfolding in `decide`.**  `Coerce.normal` strips every
  `const`/reference before unfolding (a closure's `const priqueue&`
  parameter was compared unfolded on one side only) and unfolds to a
  fixpoint (`uf<>` over `NatMap.t` over `bst<>`, a functor argument's
  `key<>`/`value<>`).  A closure's result an alias spells as a function
  continues the chain (`Arrows.curried`, `Coerce.normal_arrows`: `st<Z>`,
  `State<nat,nat>`).  `Coerce.implicit` reads the value through aliases
  (`ReSum<any, fn(opaque)->opaque>` is a callable with an erased domain).
  `Calls.record_call_sig` reads a callee typed by a function alias
  (`Id_ obj c`) through the alias, so the call yields the alias's
  codomain, not the alias.  Deviation from the brief: the printer's type
  spelling does not unfold aliases (it prints the alias name, which C++
  resolves), so there was no second unfolding to share; `Coerce.normal`
  over `Types.unfold_cpp_typedef` is the one place.
- **Goal 4, the adapters through `Coerce.into_slot`.**  `into_slot ?al
  ~origin x into` is the one entry for rows 1 (`regroup_value`, origin
  `Rg`), 2 (`curry_value_to_expected`, `Ec`), 4
  (`eta_expand_to_expected`, `Ee`), 7 (`regroup_crossing`, `Crossing`), 8
  (`name_fn_arg_for_tvar_param`, `Tvar_name`), 11
  (`erase_fn_arg_for_param` with `convert_carrier_arg`, `Param`) and 12
  (`coerce`, `Ue`, and through it `unbox_into`, `unbox_value`,
  `recover_boxed_result`, `recover_boxed_component`).  The origin names
  the adapter body (`*_built`) that expands and carries what it reads
  beyond the two types, so parameter prefixes are unchanged.  Where
  `decide` answers (`Coerce.decides`: a typed value at a stated slot,
  neither side mentioning a type variable, no `auto` in the slot, not a
  callable at a slot no callable fills) its plan decides whether the body
  runs; elsewhere the body's own test still decides.  Byte identity
  follows from the shadow check: an adapter that built something always
  agreed with `decide`'s plan kind, and a body run where it would build
  nothing still builds nothing.  One exception kept explicitly: `coerce`
  boxing a value that is a `std::any` already (an identity in C++) where
  `decide` plans nothing; dropping it is a deliberate output change for
  phase C.  Deviation: expansion is not yet a pure function of the plan
  (`cpp_passes/coercions.ml`, 3.3): the bodies still re-test their own
  conditions and read the slot as written, which is what keeps output
  identical; making the plan carry everything they read is B2/C work.
- **Row 11's slot is the parameter as the callee declares it.**  Routing
  `erase_fn_arg_for_param` first changed four outputs
  (`arrow_behind_type_function`, `sigt_fn_any`, `sigt_prod_fn_any`,
  `sigt_leaf_forward_string`: `crane_erase_fn` dropped), because this
  adapter had never been shadow-checked and `decide` disagreed with it
  twice.  (a) A slot an alias spells as a box (`nfun = crane::obj`) is a
  box: `decide`'s box row now reads `al.spells_as_any` on the slot as
  written, not only `is_boxed_type`.  (b) A parameter erased by a
  value-indexed family that the C++ type in this scope does not show
  (`fn(Inst::sem)->bool`, `sem` erased in the functor's body) is erased
  only by the Core type: `Coerce.erased_param` (split out of the
  adapter) gives the shape, and the slot `into_slot` receives is the
  erased signature the callee declares (`fn(any)->bool`, or `any` for
  `Boxed_whole`).  With both, `decide` agrees and output is identical.
- **`typed-declined`**, a new census: an adapter that built nothing where
  `decide` plans a coercion C++ does not do by itself, at a comparable
  slot.  It never changes output (the body is what declines), but it
  lists where `decide` is ahead of the adapters: `regroup_crossing`
  unbox 92 / regroup 48 and `curry_value_to_expected` erase 44 (other
  adapters' plans, built elsewhere), `coerce` unbox 90 (the expression is
  already an `Any_cast` the caller still calls `from:Any`), `eta`
  16 (a template's name whose signature keeps the callee's own `T1`).

`typed-fit` census after `69d1d59d6` (whole-suite extraction):

| site | fits | implicit | deduced/forwarded | tvar slot (fits / other) | no type | untyped | unrelated | planned |
|---|---|---|---|---|---|---|---|---|
| destination | 143255 | 624 | - | 50766 / 183 | 2304 | 112 | 492 | 128: erase 84, unbox 16, eta 16, box 8, regroup 4 |
| argument | 84286 | 850 | 71910 / 19772 | 15092 / 230 | 0 | 221 | 427 | 60: unbox 32, convert 12, erase 12, eta 4 |

What is left before `typed-fit` can be fatal (none of it missing output;
the suite compiles under `CRANE_STRICT_ARITY`): a long tail of about 300
distinct (value, slot) pairs, the largest groups being applied indexed
events (`app(getE)<nat>` against `getE`), an instance used as a carrier
(`app(Monad_option<>)<nat>`), constructor values at their Core result
(`itreeF<..>` for an itree, `prod<>` against `prod<any,any>`, `nat` into
a record from a projected field), effect primitives' parameter slots at
the wrong instantiation, a callee's own variable still leaking where
deduction cannot see it (a result-only variable; `Raw.t<T3>` against
`list<prod<key,T1>>` in `FMapList.map2`), and the 2304 destinations that
state no type (`Destination.return_ cx` with no ambient type).

Commits: `e1476dcd7` (decide: HKT carriers, nested aliases, declined
census), `d16ec300d` (deduced call types; `crane_move_hunt.h` drops an
unused `#include <variant>`, the only output change), `4229362c4`
(rows 1, 2, 4, 7, 8 through `into_slot`), `69d1d59d6` (row 12),
`6238d97fd` (row 11; decide reads a box an alias spells, a carrier at an erased element).  Full `make test` from clean after `d16ec300d` and again after
`6238d97fd`: 1526 passed, 16 failed (all `tests/wip`, as at the base),
`git status --short tests` empty; extraction byte-identical after each
commit in between; `dune build @unit_tests/runtest`
and `scripts/check-module-deps.sh` pass; no `CRANE_CHECK_IR` violation,
`typed-shadow` 0 disagree.

Next, in order: (1) route the remaining rows (3 `grouped_lambda`, 5
`mk_arity_call`, 6 `apply_at_site`/`wrap_excess`: these build calls
from parameters, so they become `Typed.apply` (3.4) rather than
`into_slot`; 9-10 `gen_call_args`' inline-mapping naming and codomain
wrap; 13 joins; 17 `gen_crossing`); (2) the census tail above, then
`typed-fit` fatal, filing any genuine miss in `tests/wip`; (3) B2: make
each plan carry what its expansion reads, move the bodies to
`cpp_passes/coercions.ml`, and have `into_slot` return `Coerce (c, e)`.

### Phase B1, fourth session (2026-11-22)

Done:
- **Application by grouping (3.4), rows 3, 5, 6.**  `Cpp_ir.Typed.apply
  ?first ?prefix f args` applies a typed callee group by group as its
  `Arrows` take the arguments: a group straddled at the end leaves a
  closure over the rest of it (parameters `prefix` + position, `_sat` by
  default), arguments past the last group apply to the result at the
  result's own groups, all at once where the result (or the callee) has no
  arrows.  `first` builds the first group's call where the callee takes
  more than the arguments (a lifted lambda's captured variables, a local
  fixpoint's opaque signature); a callee given `first` is always called.
  `Typed_checks.applied` moved next to it as `Typed.applied` (the same
  rule, types only).  Replaced: `Coerce.mk_arity_call` (lifted let-lambda
  calls, `gen_applied_fix`'s in-place call and its surplus, the class
  method call in `Match`), `Coerce.apply_at_site` (both
  `curry_value_to_expected` sites and the eta-lambda surplus in
  `Application`: the callee is typed at `spell_arrows site`), and
  `chain_excess` (now `excess_groups`, the codomain read through aliases
  as a list of groups, then `Typed.apply`).  Each callee is typed at its
  declared parameters and `Types.codomain_after` (the Core codomain after
  the value arguments; `auto` where the type has fewer arrows).
- **Row 3 is `Typed.apply` plus a regroup.**  A local fixpoint's partial
  application is `Typed.apply ~prefix:"_pa"` (the straddle closure), put
  in the position's slot through `into_slot ~origin:Pa`, whose expansion is
  `grouped_lambda`: a fresh closure is regrouped by nesting its own
  parameters rather than wrapped in an `_rg` adapter.  Shadow: 4 agree.
- **Row 9.**  `gen_call_args`' naming of a callable at an inline
  mapping's parameter declared at a type variable is origin
  `Mapping_name` at `Template_parameter spelled` (`Coerce.mapping_name_built`:
  `Converting_construct` at the instantiation where spellable, else
  `Function_value`).  `decide` plans `Name` for a closure or a function's
  name; a value already typed or deduced is named all the same (the text
  keeps it in an `auto`; for a value of exactly that type the copy is an
  identity), which the shadow accepts as `["name"; "none"]` and phase C
  may drop.  Shadow: 52 agree.

Deviations:
- `wrap_excess` keeps its erased-convention path
  (`Coerce.apply_erased_callee`) and `boxed_group_target`'s unbox between
  groups: both are coercions between groups, which `Typed.apply` does not
  do (each argument and result is coerced by its caller); they move once
  the result of a group is a `Typed.t` the next group's slot can coerce.
- Not yet through `Typed.apply`: the bound-variable call in
  `Application` (its own `_pa` closure with `moved`, and the over-applied
  `Call (sig0, Call (sig0, f, primary), excess)` whose signatures say
  `nargs = 0`).  Routing them needs the provided arguments' types as the
  callee's first group; `auto` placeholders would do for the count, but
  the honest fix is typing the callee from the binder (`Binders.read_value_type`).
- Rows 10 (a lambda argument's return annotation and `Shared_pointer`
  codomain wrap), 13 (joins) and 17 (`gen_crossing`) are not started.
  Row 10 is a lambda's returns coerced into the slot's codomain: it wants
  the lambda lowered against `Return (Exactly cod)` (its destination), not
  an adapter after the fact.  Row 17 already expands through `Coerce.coerce`
  (origin `Ue`) on each branch; what is left is choosing `from` from the
  typed inner value instead of the decision tree.

`typed-fit` census after `2498b061f` (whole-suite extraction): unchanged
from the third session except destination `box` 8 -> 12 and fits-implicitly
624 -> 696 (the `_pa` closure now typed as a closure before its slot);
destination 492 unrelated / 183 tvar-other / 132 planned / 112 untyped /
2304 no slot type; argument 427 / 230 / 60 / 221 / 0.

Commits: `0205e7195` (Typed.apply, rows 3, 5, 6), `2498b061f` (row 9).
Extraction byte-identical after each (`git status --short tests` empty,
the same 2 wip extraction errors); full `make test` from clean after
`2498b061f`: 1526 passed, 16 failed (all `tests/wip`, as at the base),
`git status --short tests` empty; `dune build @unit_tests/runtest` and
`scripts/check-module-deps.sh` pass; no `CRANE_CHECK_IR` violation,
`typed-shadow` 0 disagree.

Next, in order: (1) rows 10, 13, 17 and the bound-variable call above;
(2) the census tail (third session's list: the 2304 destinations stating
no type are `Destination.return_ cx` with no ambient type; applied indexed
events; constructor values at their Core result; effect-primitive slots),
then drop the type-variable exemption and make `typed-fit` fatal under
`CRANE_CHECK_IR`, filing genuine misses in `tests/wip`; (3) B2.

### Phase B1, fifth session (2026-11-22)

Done:
- **Row 10.**  Measured first (probes on both adapters, whole suite):
  the split lambda's return annotation fired 96 times and was dropped
  every time by `Cpp_passes.Simplify` (a lambda whose body only returns a
  lambda is unannotated), and the `Shared_pointer` codomain wrap never
  fired (a `Shared_pointer` codomain comes only from a self-referential
  constructor field, `Types.cpp_of_core`, never a call parameter here).
  Both adapters are deleted; the lambda is lowered against its slot only
  (`gen_lambda`'s `Return (Exactly cod)` from `arg_expected_ty`, which
  already existed).  Deviation from the doc's plan: no new slot field
  was needed.  Of the 96 split annotations, 12 were flat where the
  destination is curried (`fold_curried_accumulator`,
  `deque_fold_curried_acc`, `fold_init_curried_branches`): Simplify hid
  a wrong annotation, another reason to delete it.
- **Bound-variable call through `Typed.apply`.**  The callee is typed
  from its binder's Core type (`callee_typed k`: one group of its first
  `k` value domains, the rest converted as the result); the
  under-application `_pa` closure and the over-applied excess are
  `Typed.apply` (`moved` still set on the closure).  The binder is read
  through `Coerce`/`Boxed_value`/barrier wrappers for both branches (it
  was direct-only for the under-application); no output changed.

Not done, with what was learned:
- **Row 13 (joins).**  The scan (`iife_closure_return_at`) cannot be
  replaced by the 3.3 rule "one common `Typed t` deduces" without output
  changes, for three measured-by-reading reasons: (a) the match IIFE
  sites (`iife_closure_return`, `several = false`) annotate even a single
  callable return; (b) two returns of function-typed binders annotate
  (a deduced `F&&` parameter is a template parameter of its own), while
  `Binders.read_value_type` types such a binder at its function type, so
  both read as one `Typed t`; (c) a call yielding a `crane::fn` is no
  "callable" to the scan but is `Typed (Function _)`.  So the join needs
  (i) a `Value_type` for a deduced callable parameter that is not its
  function type (its template parameter, `Typed (Variable F)`), and
  (ii) the collected returns: a `Destination.Joining {into; seen}` that
  `finish` records into.  The lambda site and the five `value_iife`
  sites take it directly; the match sites build each branch with
  `Destination.return_ cx` in five functions (`match.ml` ~l.185, 625,
  637, 751, 979), which need the destination threaded.  One more trap:
  `gen_lambda`'s fixpoint fold rewrites the last `return f` into
  `return f(..)` after the body is lowered, so the collected value and
  the scanned statement differ there.  Recommended method: implement
  collection plus the type rule as a shadow probe against the scan, fix
  (i), then switch site by site.
- **Row 17.**  Not started.  `gen_crossing`'s `from` is `Any`,
  `Opaque_type` or `recorded_from` by a decision over Core and binder
  plans; taking it from the typed inner value needs that value typed as
  boxed where `Binders.read_is_boxed` says so (today it is typed at the
  Core conversion).  Probe the two side by side first.
- Census tail, fatal `typed-fit`, B2: not started.

Commits: `82b69cd22` (row 10), `355079d8d` (bound-variable call).
Extraction byte-identical after each (`git status --short tests` empty,
the same 2 wip extraction errors), `typed-shadow` 0 disagree.

Next, in order: row 13 as above, row 17, the census tail (fourth
session's list), `typed-fit` fatal, B2.

### Phase B1, sixth session (2026-11-22)

Baseline census at `7b90ec6f0` (whole suite): destination fits 143179,
type-variable fits 50766, no slot type 2304, implicit 696, unrelated
492, type-variable other 159, untyped 112, planned 136; argument
unrelated 427, type-variable other 188, untyped 221.

Done:
- **Row 13, joins from types.**  Deviation from 3.2/3.3: no
  `Destination.Joining`, and `Join` carries no lambda number.  The five
  match branch builders all take `Destination.return_ cx`, so the
  returns are collected lexically instead: `Lowering_state.with_returns`
  installs a collector, `Destination.finish` records each returned
  expression with the type lowering synthesised for it, and a nested
  collector hands its records outward (an IIFE inlined by
  `finish_inlined` returns its body's values as the outer body's; they
  keep their recorded types instead of the IIFE's).  The join enumerates
  the body's own-level `return`s (`Match_types.returned_types`, a
  structural walk, not a classification) and looks each up by physical
  identity, falling back to `Typed.node_type`; it decides by
  `Cpp_ir.Value_type.deduces_none`: a closure, a function's name or a
  generic lambda has no type C++ can write, and two different types have
  none in common (two `F&&` parameters, `Typed (Variable F0)` and
  `Typed (Variable F1)`, are two types).  This replaces the syntactic
  scan; `joined_at` stays as the regrouping rule (it is also used by the
  custom-case IIFE, which always annotates).  `gen_lambda` asks it of the
  body as lowered, before the capture substitutions and the fixpoint fold
  rebuild the returns (the fold trap of the fifth session never arises).
  `value_iife` takes its body as a thunk.  Shadow first, as recommended:
  over the suite only 36 join decisions are live (others have a
  non-function Core type or a single return); two disagreed, both typing
  bugs, fixed: (a) an inlined match IIFE's lambda return took the IIFE's
  type (`or_type`), fixed by the outward hand-over above; (b) a class
  method named through a record projection (`I::m`) and a global left
  untyped by its form module were typed at their function type: now
  `Function_name` (`Match.read_class_method`, `Typed_checks.of_built`).
  Item (i) of the fifth session (a value type for a deduced callable
  parameter) needed nothing new: such a binder's recorded type is
  `Reference (Forwarding, Variable F)`, which `read_value_type` already
  reads as `Typed (Variable F)`; no live decision in the suite depends on
  it.
- **`Join` slots.**  `Slot_type.Join` is now nullary: the return slot of
  the lambda being lowered when C++ deduces its result.  `gen_lambda`
  without a function slot, a lifted helper, and every return where no
  result type is in force (`Destination.result_slot`) return at `Join`;
  `Free` is left to `auto` variables and discarded values.  The 2304
  "slot states no type" destinations were 2300 joins and 4 discards
  (census sites `destination` / `discard`).
- **Row 17, first step.**  A boxed variable read
  (`Binders.read_is_boxed`) is typed `Typed Any` (it was the binder's
  converted type).  Probe (`crossing-from`, removed) over
  `gen_crossing`'s coercing branches before/after: erased variable 207
  box + 75 concrete -> 282 box.

Not done, with what was learned:
- **Row 17, `from` from the typed value.**  Tried: all three coercing
  branches take `from` from the typed inner value where it is `Typed`.
  12 outputs change, every one dropping a needed unbox
  (`typed_expr`, `any_cast_nested`, `existential_fn_projection`,
  `hk_class_field_result_cast_to_concept`, `interp_chain_perf`,
  `interp_params_family`, `interp_state_after_interp`,
  `interp_state_case_handler`, `itree_case_handler`,
  `let_bound_monad_family`, `resum_id_eta_lambda`, wip
  `shared_event_subevent`): the inner value is typed concrete where it
  is a box at run time.  The forms: loopify frame temporaries
  (`_f._tmp2`, `_result`), calls whose callee declares an erased result
  (typed at the use's instantiation, 24 `recorded` crossings), a value
  already `crane_any_cast` once (`any_cast_nested`), a variable the
  oracle reads erased but typed opaque (62, where the old coerce built
  nothing either).  Next: type a call's result as the callee declares it
  (erased result -> box) and frame fields from their declarations, then
  retry; the probe is the experiment above.
- **Census tail.**  After the joins: destination unrelated 488,
  type-variable other 159, untyped 116; argument unrelated 427,
  type-variable other 188, untyped 221.  The largest destination groups
  are a return slot read from an ambient result type that is not the
  position's (a `nat` returned where the enclosing function's `state`
  is in force: `dest-ambient` disagrees 1260 times, the same as the
  baseline), constructor values at their Core result (`itreeF` for an
  `itree`), applied indexed events, and a result-only callee variable.
  `typed-fit` cannot be fatal until those are fixed; not started.
- B2: not started.

Commits: `17f73a881` (row 13), `f5bf44e57` (boxed read typed as box),
`c41b00f52` (Join slots).  Extraction byte-identical after each
(`git status --short tests` empty), no `CRANE_CHECK_IR` violation,
`typed-shadow` 2637 agree / 0 disagree; `dune build @unit_tests/runtest`
and `scripts/check-module-deps.sh` pass.  Full `make test` from clean at
`c41b00f52`: 1526 passed, 16 failed (all `tests/wip`, as at the base),
`git status --short tests` empty.

Next, in order: row 17 as above (typed call results and frame fields
first), the census tail (ambient-free return slots everywhere: the
destination a match branch gets should be its IIFE's, not the ambient
type), `typed-fit` fatal, B2.

### Phase B1, seventh session (2026-11-22)

Done:
- **Row 17, `from` from the typed value.**  `gen_crossing` lowers its
  inner term typed and every coercing branch (erased variable, oracle,
  recorded, and the fall-through) coerces from that type through one
  helper, `cross ~concrete ~into`: unbox where the value is a box, adapt
  from its own type where the branch allows a concrete source
  (`~concrete`), else leave it.  `binder_is_opaque` and the per-branch
  `from` choices are deleted.  What the sixth session's attempt lacked,
  measured with a probe that compared the tree's result with the typed
  one at every crossing (112 differences at the start, 0 output changes
  wanted):
  (a) a variable whose binder has no decided C++ type (none, or `auto`)
  and whose Core type converts to `Obligation Opaque_type` is read as
  `Typed Any`: the erased value is represented by a box, and only a
  binder declared opaque is an admission (62 sites: loopify frame
  temporaries, `Case_sum1` handlers, `measurer`);
  (b) a type is a box under aliases (`Coerce.normal`, `boxed_source`,
  `names_erased_alias`) and as an alias template of a box with
  arguments (`payload_ty<T1>` for `using payload_ty = crane::obj`;
  `resolves_to_any_type` reads only the unapplied head);
  (c) an `Abort` is at the type it carries (it prints as an invoked
  lambda returning that type, `[]() -> crane::obj { throw ...; }()`), not
  `Never`, here only (19 sites in `dep_elim`); joins keep `Never`;
  (d) where extraction recorded the source as opaque (a value-indexed
  family's call result, `dt<>`, `tuple<>`, `nfun<>`, `domty<>`: 24 sites)
  the crossing leaves the value alone even though it is typed a box: the
  enclosing position recovers it at the right shape, and recovering at
  this crossing's `boxed_shape_of` would name `pair<obj,obj>` where the
  box holds `pair<uint64_t, monostate>` (`tt_at_computed_type` breaks).
  So the recorded record keeps choosing *whether* the recorded branch
  coerces (`recorded : [`Box | `Opaque | `None]`); `from` is the typed
  value's.
  Calls whose callee declares an erased result and values already cast
  out of a box needed nothing further: after (a)-(d) no crossing
  disagrees.
- One deliberate output change, in the same commit:
  `hk_class_field_result_cast_to_concept`, `natMMP::mk_prov(ptr p)`:
  `Nat::s(crane::any_cast<Nat>(std::move(p)))` becomes
  `Nat::s(std::move(p))`.  `ptr` is `natPtr::ptr = Nat`, a promoted
  member typed concrete; the tree unboxed it on the oracle's say-so.  The
  test compiles and passes.

Findings:
- A probe that computes the alternative result is not a test of it:
  differences at one crossing are often absorbed by the enclosing one,
  and a first flipped run here (an environment switch, then a `sed`
  edit not checked) showed no change where the committed code changed
  three files.  Flip in code, check the edit, diff the outputs.

- **Own return slots for deduced lambdas.**  `Lowering_state.own_return`
  (set by `with_own_return`, reset by `with_cpp_return_type`) is the slot
  a `return` fills in the body of a lambda C++ deduces the result of:
  `value_iife` (its `ret`, else `Join`), `gen_lambda` without a function
  slot, and a lifted helper.  `Destination.return_` reads it before the
  ambient type, so the match branches inside such a body (the five
  builders in `match.ml`) return at the lambda's slot.  The ambient
  `current_cpp_return_type` is untouched (lowering decisions still read
  it until phase C), so outputs are byte-identical; only the census and
  `dest-ambient` see the change.  Census: destination unrelated
  488 -> 484, type-variable other 159 -> 155 (343 + 16 + ... at type
  variables), join 2300 -> 2532, fits 143179 -> 142955.  `dest-ambient`
  disagree 1492.

Census after this session (whole suite): destination unrelated 484,
type-variable unrelated 343 (of 65858 type-variable fits), untyped 116;
argument unrelated 427, untyped 221.  The 484 unrelated destinations are
mostly not IIFE returns.  Largest groups (from, into, value node):
`itreeF` into `itree` from a constructor call (40: a constructor value
at its Core result); `nat` into a record `state` from a call or an
other node (~48: `get_pair_bound_prop`, `cpu_emulator`,
`coalition_bid_honor_trace`; in `execute`'s `let sum := ... + if ...`,
the branch of an `if` under an inline custom operator); `prod` into
`prod` (27, differing arguments); `option<prod<T1,..>>` in
`lifted_param_const_v_mut` (40); `list` into a `fn` (20,
`call/0(other)`); `closure nat->nat` into a function (12).  To find
the site of each, the census line needs the Core form of the value
(`Destination.finish` has none): thread it, or record the form in
`Typed.t` at `gen_expr_typed`.

Commits: `0a46b5ab8` (row 17), the next commit (own return slots).
Extraction byte-identical after each except the named
`hk_class_field_result_cast_to_concept` change; full `make test` from
clean at `0a46b5ab8` and again after own return slots: 1526 passed,
16 failed (all `tests/wip`, as at the base), `git status --short tests`
empty after the second; `dune build @unit_tests/runtest` and
`scripts/check-module-deps.sh` pass.

Next, in order: (1) census tail: put the Core form on census lines,
then fix the groups above at their source (constructor values typed at
the C++ type the constructor builds; inline custom operator operands and
their IIFEs at their own slots; `prod` argument mismatches); (2) drop
the type-variable exemption, make `typed-fit` fatal under
`CRANE_CHECK_IR`, file genuine misses in `tests/wip`; (3) B2.

### Phase B2 (2026-11-23)

Done:
- **Plans carry what their expansion reads.**  `Coercion.plan` is now
  the expansion vocabulary; decide's two-type answer is
  `Coercion.decision` (constructors unchanged, `decision_name` for the
  census).  One plan per adapter, keeping its parameter prefix:
  `Regroup_curried (from, into)` (`_rg`), `Nest into` (the partial
  application's closure), `Eta_short {domain; arity}` (`_ee`),
  `Eta_global {declared; into; site; exact}` (`_ec`), `Name_closure`,
  `Name_at`, `Erase_as`, `Convert_to` (crossings, carrier arguments),
  `Represent (src, dst)` (pointer dimension), `Box_value (box, erase)`,
  `Recover_box {into; lambda}` (a lambda's returns recovered at its
  codomain by a sub-plan), `Recover_call {domain; args; result}` (`_ue`,
  sub-plans per argument and result), `Moving (x, p)` (the adapter holds
  `x` by move: the two `moved = [x]` sites in `expr.ml` now say it as a
  plan).  `Coerce` keeps one planner per origin (`ue_plan`,
  `eta_global_plan`, `erase_fn_arg_plan`, `crossing_plan`,
  `eta_short_plan`, `name_fn_arg_plan`): every read of `Lowering_state`,
  the environment or Core happens there.  The adapter bodies moved
  unchanged to `cpp_passes/coercions.ml`, `expand : plan -> Expr.t ->
  Expr.t`, pure.  `Convert` moved to `cpp_passes` (it was already pure);
  `Arrow_site` moved to the grammar (`Types.arrow_site` re-exports it).
  Deviation: `Box_value` names its box type (`Any`) rather than leaving it
  implicit, because a type rewrite between lowering and finishing (a
  generic lambda's `Any` respelled `CraneX`, `hkt_record_dict`) must reach
  the box the expansion builds.
- **The node survives to finishing.**  `into_slot` returns `Coerce (c,
  e)` whenever the plan's expansion differs from the value (no identity
  node).  New pass `coercions`, first in `Pipeline.lowered_passes` after
  the control check, expands innermost first; new obligation
  `Representation_obligation.Unlowered_coercion`, checked by `owes` as
  the pass's fixed point (`unit_tests/pipeline_manifest.expected`
  updated).  `Resolve` already owed `Coerce`.
- **Looking through a coercion.**  Deviation from "move shape-inspecting
  code onto `Typed` / `Expr.under_coercion`": the exact look-through is
  `Cpp_ir.Typed.head e`, `e` with its outermost coercions expanded (the
  shape the eager code saw), and `Typed.node_type (Coerce _)` is the node
  type of that head.  The expansion builds with finishing's vocabulary
  (`Cpp_passes.Erasure`, `Convert`, `Ownership_ir.Region`), which
  `cpp_ir` may not read, so `Coercions` installs `expand` into
  `Typed.expansion` at load.  A hook is the price of keeping `node_type`
  exact until phase D, where every value crossing modules is a
  `Typed.t` and `node_type` no longer has to read nodes.  Sites moved to
  `head` (each found by a byte diff, 31 tests at first): the doc's list
  (`expr.ml` constant `Call` checks, `Cpp_build.lift_iife_assignment`)
  and: `application.ml` crossings (`regroup_crossing` results tested by
  physical identity instead of matching `Convert`), `eta_arg_is_cheap`,
  pair-accessor `single_arg`, the custom-list `as_value` reuse,
  `made_of_application` through a recovering coercion (the recursion
  plan finds the call by its occurrence), result `Call` checks;
  `Typed.closure_arrows` (a body returning a coerced lambda);
  `construction.ml` closure naming at a field (`has_signature`,
  `returns_closures`); `stmts.ml` let binding type from a lambda;
  `Erasure.reads_recovered_pair` / `yields_boxed_component`;
  `Coerce.box_for_any_slot`, `Coerce.coerce`'s lambda test,
  `curry_value_to_expected`'s entity test; `Lifting.local_var_subst_expr`
  and `Local_functions`' lifted-call substitution (a cast around a call
  of the lifted local); control lowering: `Frame` (resume cast and
  `planned_resume`), `Analysis.count_calls_expr`, `Lower.check_lowered`'s
  `bare`.  `Lifting.fixpoint_escapes_in_stmts` /
  `fixpoint_named_in_returns` and `tail.ml:make_rhs` needed nothing
  (their traversals descend into the node, or the eager adapter was not
  a variable either).
- Not deferred: `Coerce.box_for_any_slot`, `deep_box_list`,
  `recover_carrier_result`, `apply_erased_*` still build directly (they
  never went through `into_slot`); phase C folds them into plans.

Finding: deleting a test's `.vo` does not make dune rebuild it when
nothing it depends on changed (the digest database remembers the rule);
a bisecting harness must change the `.v`'s digest each run
(`/tmp/tcppir8/many.sh` appends a unique comment, `git checkout tests`
restores).  Two of the early bisections here silently measured nothing.

Commits: `6c64774c3` (plans carry their data, eager), `142448616`
(node survives to finishing).  Extraction byte-identical after each
(`git status --short tests` empty), no `CRANE_CHECK_IR` violation;
`dune build @unit_tests/runtest` and `scripts/check-module-deps.sh` pass.
Full `make test` from clean at the second: 1526 passed, 16 failed (all
`tests/wip`, as at the base).

Next: phase C.  Start with the standalone row functions (`regroup_value`,
`eta_expand_to_expected`, ... are now one-line `into_slot` calls whose
callers can name the origin and slot) and `box_for_any_slot` /
`deep_box_list` as plans; then the ambient return type
(`current_cpp_return_type`, 57 uses; `with_cpp_return_type`, 28), which
needs destinations threaded to every reader, the bulk of C.

### Phase C, first session (2026-11-23)

Done:
- **Row adapters are `into_slot` calls.**  `regroup_value`,
  `eta_expand_to_expected`, `regroup_crossing`,
  `name_fn_arg_for_tvar_param`, `unbox_value` deleted; callers name the
  origin and the slot.  What was logic in the remaining wrappers stays,
  named for what it computes: `named_value` (the typed value of a name,
  `Function_name` for a global) plus `eta_global` (origin `Ec`, 4
  callers), `param_slot` (the slot of a declared parameter) plus
  `at_param` (origin `Param`).  `into_slot` takes its aliases from the
  origin (`Ec`/`Ue`/`Param`/`Any_slot`/`Family_list` carry `cx`), so no
  caller passes `~al`.  `coerce` (row 12's entry, 28 callers) stays: it
  derives `from` from the operand (a lambda is a closure whatever box the
  caller names), which is the typed value's job until phase D makes every
  operand a `Typed.t`.
- **Box and carrier adapters are plans.**  `box_for_any_slot`,
  `deep_box_list`, `recover_carrier_result` become planners
  (`any_slot_plan`, `deep_box_plan`, `carrier_result_plan`) behind new
  origins `Any_slot`, `Family_list`, `Carrier_result`, with two new plans
  `Box_list_deep` (`crane_deep_box`) and `Recast_carrier`
  (`Container_cast`), expanded by `coercions`.  Their slot is the box's
  declared type (or the position's type for the carrier).  These origins
  keep their own test (`own_test` in `into_slot`): `decide` does not gate
  them, but the shadow still compares.
- Deviation: `apply_erased_curried` / `apply_erased_callee` are not
  coercions.  They apply a boxed callee (`Erased_call` per argument,
  each argument boxed); there is no value-into-slot step to plan.  They
  belong with `Typed.apply` (a boxed callee's `Arrows` are one unary group
  per argument); left in `coerce.ml` until then.
- **Planning no longer reads the ambient return type.**
  `Position_plan.region` and `Representation_plan.region` take `~ret`
  (`with_region` passes the region's), and the functions they share with
  lowering take it too: `Constructors.regular`, `custom`, `custom_field`,
  `custom_refined_annotation`, `into_erased_return`, `temps_from_slot`,
  `Ctor_args.expected_type_args_from_return`, `Calls.plan_call`,
  `argument_position`, `call_type_args`, `hkt_carrier_type_args`,
  `lifted_call_type_args`.  `Position_plan` had six
  `with_cpp_return_type` brackets whose only job was to hand its own
  explicit `ret` to those functions through the ambient; all six are gone
  (three were around calls that, once the shared functions took `~ret`,
  reached no reader).  Lowering callers read the ambient once per
  function (`Construction.gen_expr_custom_cons`, `gen_construction`,
  `Calls.lower_call`) and pass it.  `with_iife_return_type` (an alias)
  deleted; `Coerce.position_cpp_ty cx None` (the ambient by another name)
  replaced by `current_cpp_return_type cx ()` at its five sites.

Finding: `decide` sees a `Family_box` slot (`den<>`, an alias of the box)
as a plain box and answers `box` where `deep_box_plan` builds a deep box
(3 regression tests: `den_value_not_deep_erased`,
`family_call_result_deep_shape`, `family_call_result_mapped_list`).  A
deep box is a box at every level; the shadow accepts either name for
the two box origins.  A `Family_box` slot type would let `decide` say it.

Where the ambient stands: 41 reads (`match.ml` 10, `local_functions.ml`
7, `lowering_state.ml` 6 incl. `with_region`, `with_escape_analysis`,
`returns_void`; `stmts.ml` 5, `effects.ml` 3, `application.ml` 2,
`construction.ml` 2, `coerce.ml` 2 (`position_cpp_ty`, now only under
`recover_boxed_result` and the carrier slot), `destination.ml` 2,
`calls.ml` 1, `functions.ml` 1) and 19 `with_cpp_return_type` brackets
plus three direct `set_lexical`s (`match.ml` 1130, `functions.ml` 1496,
`with_escape_analysis`).  Why the rest is not a mechanical thread: the
ambient means two things.  (a) The result type of the function or lambda
whose body is lowered: read at tail positions (`stmts.ml` 460-480,
`effects.ml`, `match.ml` 2047/2054, `returns_void`).  It is not the
destination's slot: inside a deduced lambda the destination returns at
`own_return` (`Join`) while the ambient is still the enclosing type
(`dest-ambient` disagree 1492), and readers decide on the latter.  (b)
The type of the value being built where no return is involved: a let
RHS (`stmts.ml` 283, `Types.let_value_result`), a constructor argument
(`construction.ml` 159, `a.ret`), a call argument (`application.ml` 157,
258, `argument_position`'s `ret`), an IIFE (`expr.ml` 563, `match.ml`
2024).  (b) is a second, undeclared `expected_ty` that survives the
`?expected_ty` of the knot's entry points; threading it means a `~ret`
on `Knot.lowering`'s functions next to `?expected_ty`, or better, the
phase D non-optional slot carrying it.  A `ret` field on `Slot.slot` is not a
drop-in: slots are rebuilt from `Slot.empty_slot` at many sites, while
the ambient is lexical (it survives every call that does not bracket
it), so the two diverge wherever a form starts a fresh slot.  Order that
keeps each commit byte-identical: (1) for each (b) bracket, find the
readers reached under it (a probe that tags the ambient with the bracket
that set it and records the tag at each read), and where every read
under a bracket is in the shared functions already taking `~ret`, pass
it and drop the bracket, as was done for `Position_plan`; (2) the
readers left under (b) brackets read a `ret` added to the form
functions they sit in, passed down from the bracket site, one reader per
commit with the bisect harness; (3) (a)-readers read a `Destination`
that carries the enclosing result type next to its slot; (4) delete the
brackets, `current_cpp_return_type`, `position_cpp_ty`,
`let_value_result`.  Step 3 of phase C
(`call_result_site`/`codomain_site`, `joined_at`,
`iife_closure_return_at`) reads `~ret` from (a) and follows it.
`Binding.Declare_deduced` is not introduced yet: it needs the RHS
`Value_type` at the 29 `Declare (Auto, _)` builders, which is phase D's
"only `Typed.t` crosses lowering modules".

Commits: `a0e318ff1` (row adapters, box/carrier plans), `7b7a370ff`
(planning takes the return type), `0523c5e54` (ambient read under its
own name).  Extraction byte-identical after each (`git status --short
tests` empty, no `CRANE_CHECK_IR` violation); unit tests and
`scripts/check-module-deps.sh` pass.  Full `make test` from clean at
`0523c5e54`: 1526 passed, 16 failed (all `tests/wip`, as at the base),
`git status --short tests` empty.

Next: phase C step 2 from (1) above (the bracket-tag probe, then the
(b) brackets), then step 3.  Phase D not started.

### Phase C, second session (2026-11-23)

Done:
- **Bracket-tag probe.**  Each `with_cpp_return_type` bracket (and the
  three direct sets: the function body, the match scrutinee,
  `with_escape_analysis`) tagged the ambient with its site; each read
  recorded the innermost tag.  Every bracket reaches the main readers
  (`Calls.lower_call`, `Calls.argument_position` through
  `application.ml`, `Construction.gen_expr_custom_cons` /
  `gen_construction`, `position_cpp_ty`, `with_escape_analysis`):
  no bracket could be dropped with the readers left in place.  The
  readers sit on the shared expression path, not at tails, so the
  "(a) tail readers / (b) hidden expected type" split does not separate
  them by site; it is a property of the value, not of the reader.
- **Deviation: one threaded `ret` instead of the (a)/(b) split.**  The
  knot's entry points take `~ret : Cpp_ir.Lowered.Type.t option` (the
  result type of the function or lambda whose body is lowered) next to
  `?expected_ty`, and so do the form functions on the path
  (`Expr.gen_form`/`gen_crossing`, `Stmts.gen_stmts_scoped`,
  `Application.eta_fun`/`gen_call_args`/..., `Construction`, `Match`,
  `Local_functions`, `Effects`, `Lambda.gen_lambda`),
  `Destination.return_`, `Lowering_state.with_region`,
  `with_escape_analysis` (which hands its body the inner result type)
  and `Calls.lower_call`.  A bracket became the `ret` its body is
  lowered at (`gen_stmts ~ret:rhs_result`, `gen_expr ~ret:expected`,
  `let ret = Some scope.cod in`).  Done in two commits: first threaded
  with the ambient kept and compared at every entry point under
  `CRANE_CHECK_IR` (`check_ret`, zero disagreements over the suite),
  then the ambient deleted.  Splitting `ret` into a tail destination
  field and an explicit slot is now a per-reader change on explicit
  data rather than a hunt for which bracket a read sees.
- **Deleted:** `lexical.current_cpp_return_type`, `lexical.own_return`,
  `with_cpp_return_type`, `with_own_return`, `own_return`,
  `current_cpp_return_type`, `returns_void` (now `ret = Some Void`),
  the probe-only `Destination.check_ambient` (`dest-ambient`).
  `Coerce.position_cpp_ty ~ret expected` stays as a pure function (the
  precedence "the position's type, else the enclosing result").
- **`own_return` was read in one place.**  A probe on
  `Destination.return_` found it `Some` only inside
  `Match_types.value_iife` callbacks (expr.ml let/fixpoint IIFEs,
  effects.ml bind IIFE): `value_iife` now hands its slot to the body,
  which returns at it (`Destination.Return into`), and
  `Destination.return_ ~ret` is `Return (result_slot ret)`.  The two
  other `with_own_return Join` sites (deduced lambda, lifted local
  lambda) already passed `Return Join` and nothing under them read it.
- `Types.type_term_arg` (a value lowered as a type argument) lowers at
  `ret = None`; byte-identical.

Finding: punning `~ret` at a call where a local `ret` of another meaning
is in scope type-checks when the types agree.  The threading commit
found one by type error (`gen_cpp_custom_body`'s branch type, renamed
`branch_ty`) and relied on `check_ret` for the rest; local closures
defined outside a bracket and called inside it
(`gen_ctor_arg`, `gen_enum_branches`, `gen_default_stmts`, `gen_body`,
`gen_body_stmts`, lambda's `with_lam_return_type` continuation) now
take `~ret`.

Not done (phase C step 3): `Types.let_value_result` (still the let RHS
`ret`), `Calls.call_result_site`/`codomain_site`, `Match_types.joined_at`
(one caller in `match.ml` custom-case IIFE) and `iife_closure_return_at`
(`lambda.ml`, `value_iife`), `stmts.ml`'s lambda-derived binding type
(needs the RHS typed value out of `gen_stmts`).  Probe-only `Custom`
destinations are already gone: the one left (`local_functions.ml`,
reified monadic let) builds a real `ret` statement.  Each replaces a decision on node shapes or Core with a
`Value_type` the lowering has, so each needs the typed value to reach
the site; `stmts.ml`'s binding type and `let_value_result` need
`gen_stmts` at an `Assign` destination to hand back the `Typed.t` it
assigned, which is phase D's "only `Typed.t` crosses lowering modules".

Commits: `c4cc387c1` (threaded, checked against the ambient),
`43bd0b82d` (ambient deleted), plus a tidy/doc commit.  Extraction
byte-identical after each (`git status --short tests` empty, no
`CRANE_CHECK_IR` violation); unit tests and
`scripts/check-module-deps.sh` pass.  Full `make test` from clean at
`43bd0b82d`: 1526 passed, 16 failed (all `tests/wip`, as at the base),
`git status --short tests` empty.

Next: phase C step 3 as listed above; then phase D.  A natural first
move for D now that `ret` is explicit: fold `~ret` and `?expected_ty`
into the non-optional slot, so each form states both where it builds
the slot.


### Phase C, third session (2026-11-23)

Done:
- **One slot at the knot (phase D groundwork).**  `Slot.slot` carries
  `ret` (the result type of the body the position is in) and `into : 
  Slot_type.t` (what the position states: `Exactly t` or `Free`).
  `Knot.lowering`'s entry points, `Expr.gen_expr_typed`/`gen_expr` and
  `Stmts.gen_stmts` take `Slot.slot` non-optionally; `~ret` and
  `?expected_ty` are gone from them.  Every call site builds its slot with
  `Slot.at ~ret ?expected_ty ?slot ()`, which restates both fields: a
  slot passed on (`{slot with in_ctor_arg = true}`) never carries its
  parent's `into`, matching the old rule that `expected_ty` was never
  inherited.  The rewrite was mechanical (a script turned each call's
  label list into the `Slot.at` arguments), so byte-identity holds by
  construction; the extraction confirmed it.  Form functions
  (`Application`, `Construction`, `Match`, ...) still take `~ret`
  and `?expected_ty` and unpack nothing yet: folding them is the next
  mechanical step, one module at a time, with `Slot.expected` reading
  `into` back.
- **An assignment hands back its value.**  `Destination.Assign` is a
  record whose `assigned` cell collects each typed value `finish`
  assigns (`Destination.assign`, `Destination.assigned d e`, by
  physical identity of the assigned node; through `Adapted` the node's
  own type).  No change to `gen_stmts`' result type: the destination is
  the caller's handle.
- **Step 3, in part.**
  - `stmts.ml`'s let binding type from a lambda: the `Closure
    {groups = [params]; result}` of the assigned value replaces the
    match on `Typed.head e`'s `Lambda {params; return_type = Some _}`.
    A probe compared both over the suite: zero disagreements, and the
    assigned value is a `Closure` exactly when the head is a lambda.
  - `Types.let_value_result` deleted: `Destination.bind_let cx env x t`
    builds the let's assignment at the binder's slot, and the right-hand
    side's `ret` is `Destination.stated` of it (two sites: `stmts.ml`,
    `local_functions.ml`'s let-lambda).
  - `Match_types.joined_at`, `iife_closure_return`,
    `iife_closure_return_at` deleted.  `declared_at ~own r` (the
    function type a lambda standing in slot `own` is declared at) keys on
    the lambda's own `Slot_type` and compares groupings with
    `Arrows.same_function` instead of a local `uncurried`; `join` and
    `join_branches` decide a lambda's annotation from its returned types.
    `value_iife` passes its own slot; matches pass `slot_of ret`;
    `Lambda.gen_lambda` passes `Free` (it passed no `ret` before).  A
    probe comparing `same_function` with the old top-chain comparison
    found no disagreement.

Not done, and why:
- `Calls.call_result_site`/`codomain_site`: the typed values do not say
  it yet.  `Typed_checks.global_value_type` spells a callee's codomain
  `Through_tvar` always, while `call_result_site` is `Declared` for a
  codomain the declaration writes out, and `application.ml`'s
  `excess_groups`/`filled_ty`/callee-arity code reads the latter.  The
  replacement is a callee `Value_type` whose result is spelled at the
  site its declaration gives it (curried only where the codomain is a
  type variable, the inline-custom rule as in `call_result_site`), then
  `excess_groups` reading `Arrows.of_type` of the call's result.  That
  changes `global_value_type`, which the census and `decide` read, so it
  needs its own probe round.
- Phase D proper: `Deduction.Not_yet_typed` is still the "node does not
  say" answer of `Typed.node_type`, later replaced by
  `Typed_checks.of_built`'s Core-derived type (`typed-untyped` census:
  zero values reach a census point untyped).  Deleting it means
  `node_type : Expr.t -> Value_type.t option` and the eleven
  `Typed.untyped`/`Deduced Not_yet_typed` producers (`application.ml`
  4, `coerce.ml` 2, `lambda.ml` 3, `match.ml`, `binders.ml`,
  `typed_checks.ml`) returning an option the form's `of_built` fills.
  Then the `gen_expr` shim, `Declare_deduced`, `Call.result` reasons,
  `Typed.expansion` and the layering rule, as in §4.

Commits: `cec9a6df8`.  Extraction byte-identical (`git status --short
tests` empty, `CRANE_CHECK_IR` on); unit tests and
`scripts/check-module-deps.sh` pass.  Full `make test` from clean at
`cec9a6df8`: 1526 passed, 16 failed (all `tests/wip`, as at the base),
`git status --short tests` empty.

Next: fold `~ret`/`?expected_ty` out of the form functions onto the
slot; `call_result_site`/`codomain_site` via a declared-site callee
type; then phase D from `Not_yet_typed`.

### Phase C/D, fourth session (2026-11-23)

Done:
- **Form functions take the slot.**  Every form function on the knot's
  path (`Lambda.gen_lambda`; `Application.gen_application`, `eta_fun`,
  `gen_call_args`, `gen_instance_projection`,
  `gen_singleton_dictionary_call`, `project_through_instance`;
  `Construction.gen_construction`, `gen_expr_custom_cons`,
  `gen_stored_value`; `Match.gen_cpp_case(_once)`, `gen_match_branch`,
  `gen_cpp_custom_body`, `gen_custom_cpp_case`, `gen_custom_match_expr`,
  `gen_record_projection`, `gen_record_match_stmts`, `record_read_once`;
  `Effects.gen_return_expr`/`gen_bind_expr`/`gen_bind_stmts`/
  `gen_return_stmts`; `Local_functions.gen_fix`/`gen_let_fix`/
  `gen_let_lambda`/`gen_applied_fix`/`gen_standalone_fix`;
  `Expr.gen_form`/`gen_crossing`) takes `Slot.slot` positionally after
  `cx` and binds `ret`/`expected_ty` from it.  A script
  (`/tmp/tcppirF/slotfold.py`) rewrote definitions and call sites (each
  call's `~ret ?expected_ty ~slot` labels became `Slot.at ...`), so
  byte-identity holds by construction; where a caller's `ret` and
  `expected_ty` were its own slot's it now passes the slot on (11 sites
  in `gen_form`, 3 elsewhere).  Safe because nothing reads `Slot.ret` or
  `Slot.into` except through `Slot.expected` and the bound names, and
  every knot call restates both (`Slot.at`).  Match's optional `?slot`
  became a slot: `branch_slot` takes and returns one; `None` behaved as
  `Slot.empty_slot` at every reader.  Local closures (`gen_ctor_arg`,
  `gen_enum_branches`, `gen_default_stmts`, `Functions.gen_body_stmts`,
  `Instances.gen_body`) and the planning functions shared with
  `Position_plan` keep `~ret`: they are not knot forms, and the plans
  have no slot.
- **The result site lives with the name's type.**  `call_result_site`
  and `codomain_site` left `Calls`: `Coerce.result_site` is the rule,
  `Coerce.name_arrows r dom cod` types a global's name with it, and
  `named_value` and `Typed_checks.global_value_type` use that instead of
  `spell_arrows Through_tvar`.  A side-by-side probe in `decide_with`
  (the decision at the old spelling versus the new, `callee-site`) had
  zero hits over the suite: the spellings differ only for a flat
  multi-argument codomain, and no such name reaches a decision point.
  The probe was then deleted.
- Deviation: `Application`'s excess groups (`cod_site`) and the
  partial-application `filled_ty` read `Coerce.result_site id`, not the
  name's `Arrows`.  Both spell the codomain at the call's instantiation
  (`cod_inst`, the eta arguments' types), which the name's type at its
  use does not carry; reading the rule the name is typed by keeps the two
  from drifting.  Reading `Arrows.of_type` of the call's result instead
  needs the call node to carry its result's `Value_type` (`Call.yields`
  as a `Value_type`, part of the `Call.result` reasons step).  The two
  codomain tests (callee arity, binder arity) read
  `core_codomain_is_tvar` directly.
- **Coercion-builder ratchet.**  `scripts/check-module-deps.sh` counts,
  per lowering file (`core_to_cpp/`, `control_to_cpp/`) other than
  `coerce.ml`, the applications (outside patterns) of `Function_value`,
  `Erase_callable`, `Box`, `Any_cast`, `Tolerant_any_cast` and
  `Erasure.box`/`unbox`/`unbox_tolerant`/`empty_box`: 41 sites in 13
  files, listed in `COERCION_BUILDERS_PENDING`.  More is an error, fewer
  must lower the count.  Deviation from §4's flat rule: that rule fails
  today (`match.ml` 10 unboxes, `application.ml` 10, `construction.ml` 7
  `Erase_callable`s and unboxes, ...); each is a phase C row still to
  route through `into_slot`.  Adapter lambdas are not counted (no
  syntactic marker distinguishes them from other lambdas).

Not done, and why (phase D proper):
- `Deduction.Not_yet_typed`: 46 `Typed.of_node` calls and 6 untyped
  producers rely on `node_type`'s "does not say" answer; an option-valued
  `node_type` needs each `of_node` caller to supply the type it knows
  (mostly the form's `of_built` Core type) or to be one of the nodes that
  carry their type (`Converting_construct`, `Box`, `Any_cast`, `Call`
  with `Yields`, ...).  Order: split `node_type` into a total
  `carried_type` over the carrying nodes and make `of_node` take a
  fallback `Value_type`, then remove the fallback per caller.
- The `gen_expr` shim, `Declare_deduced` (29 `Declare (Auto, _)` occurrences,
  22 of them in `control_to_cpp`/`cpp_passes` where no
  `Typed.t` exists), `Call.result` reasons, `Typed.expansion`: untouched.

Commits: `b96dd2a61` (form functions take the slot), `767b81c38` (result
site with the name's type), `05513b4cd` (ratchet).  Extraction
byte-identical after each (`git status --short tests` empty, 2 wip
extraction errors as at the base); unit tests and
`scripts/check-module-deps.sh` pass.  Full `make test` from clean at
`05513b4cd`: 1526 passed, 16 failed (all `tests/wip`, as at the base),
`git status --short tests` empty.

Next: phase D from `Not_yet_typed` (the `carried_type`/`of_node`
fallback split above), then `Call.yields` as a `Value_type` so the
excess groups read the call's result; then the shim, `Declare_deduced`,
and lowering the ratchet's counts by routing each site through
`into_slot`.


### Phase D, fifth session (2026-11-23)

Done:
- **No `Not_yet_typed`.**  `Typed.node_type` became `Typed.carried :
  Expr.t -> Value_type.t option`, total over the nodes that carry their
  type (casts, boxes, conversions, a call whose `yields` is `Typed`, an
  abort, a lambda whose grouping its parameters and returns give, foreign
  text, runtime helpers, requirements) and `None` elsewhere.
  `Typed.of_node ~fallback e` takes the type its caller knows;
  `Typed.untyped`, `Typed.or_type` and `Typed.not_yet` are gone
  (`or_type ty (of_node e)` was `of_node ~fallback:ty e` at all five
  sites).  `Typed.applied` returns an option; `Typed.apply` takes the
  argument expressions (it never read their types), which removed 9
  `of_node` wrappers, and `excess_groups` reads `carried` of each excess
  argument.  `Typed_checks.of_built` matches `carried x = None` instead of
  the placeholder.
  Deviation: `Not_yet_typed` did not disappear into real types
  everywhere.  It split into two honest reasons, and
  `Value_type.unstated` (replacing `not_yet_typed`) names both where a
  decision falls to the adapter's own test (`Coerce.decides`,
  `shadow`, the census, `Expr.gen_form`'s `typed_form`):
  - `Untranslated`: Core infers no type for the term, or
    `Types.cpp_of_core` fails on it (`core_value_type`,
    `Binders.read_value_type`, `named_value`, the instance method of a
    field with no type, `of_built`'s bound-variable call).
  - `Unannotated`: a node built without stating its type, read either
    by an adapter that decides from Core (its origin) or as C++ deduces
    it (a join).  This is the fallback of 37 `of_node` calls, of
    `Typed_checks.adapted_to None`, of `Typed.apply`'s call of a callee
    whose type gives no grouping, and of the four application results
    and the bound-variable callee that `Typed.untyped` typed before.
  Giving those values a real type changes what `Coerce.decides`
  answers at `into_slot` (an origin with its own test today), so each
  needs the probe round the shadow check gives: the census (unchanged
  from before) has 337 `typed-fit` lines and 146 `typed-shadow` lines
  at an unstated value (`erase_fn_arg_for_param` 88, `coerce` 40,
  `recover_carrier_result` 18).  Each such origin deleted (phase C rows)
  deletes its `Unannotated` operands.
- **The `gen_expr` shim is deleted.**  `Knot`, `Expr` and `Lower_expr`
  export only `gen_expr_typed`; 37 callers read `.expr` at the call (two
  partial applications became `fun e -> ...`).  A script
  (`/tmp/tcppirG/shim.py`) did the rewrite; same function, so
  byte-identical by construction.
- **`Call.yields` is a `Value_type`** (steps 2 and 5 together).
  `Call.result` is gone: `Yields t` is `Typed t`, `Untyped` is a
  `Deduced` reason: `Unannotated` at `Build.signature`/`Build.call`
  without `?yields`, `Analysis.call_opaque`, `Erasure.call`,
  `Depth.invoked_in_place`, `Lifting`'s self call; `Runtime_helper
  Immortal` for the call `Constants` builds of `crane::immortal`.  Map,
  Children and Resolve carry it (`Resolve.value_type`/`arrows`).
  Readers match `Typed t` where they matched `Yields t`, so no
  consumer changed.
  Not done: the two `Application` reads of `Coerce.result_site`
  (`cod_site` for the excess groups, `filled_ty` of a partial
  application) still read the rule.  Reading the call's result instead
  needs the call built with `yields` at the result spelled at the
  instantiation, which is that same rule: `Typed.applied` of the name's
  `Function_name` type gives a different spelling (`take` leaves the rest
  of a straddled group flat, where `spell_arrows Through_tvar` curries
  it), so the change is not mechanical and needs a probe comparing the
  two.

Not done, and why:
- `Declare_deduced`: a new `Binding` constructor reaches all 162
  `Declare (` match sites (48 in `frame.ml`, 17 in `inductives.ml`, 12 in
  `tmc.ml`, ...), most of which read `Declare (t, _)` uniformly with
  `t = Auto`.  The 29 `Declare (Auto, _)` builders, 22 of them in
  `control_to_cpp`/`cpp_passes`, have no `Typed.t`; `Frame.collect_type_env`
  reads a lambda's own parameters and return type there, which is what
  `Typed.carried` would give.  Plan: add `Declare_deduced of 'p
  Value_type.t * Core.Binder.t option`, have `Resolve` turn it into
  `Declare (Auto, b)` (so passes after resolution and the printer never
  see it), and port the lowered-phase readers (`frame.ml`, `tmc.ml`,
  `loopify.ml`, `view_args.ml`, `local_closures.ml`,
  `deduced_literals.ml`) one file at a time.
- `Typed.expansion`: `Typed.head` (read by `closure_arrows` and
  `carried`'s `Coerce` case) expands a coercion with finishing's
  vocabulary (`Cpp_passes.Erasure`), which `cpp_ir` may not read.
  Removing the hook needs either the expansion in `cpp_ir` or
  `carried` reading the coercion's own result type, which differs from
  the expansion's for an adapter lambda (`Closure` versus the slot's
  `Typed`), so it changes decisions.
- The ratchet's 41 sites: a direct `Erasure.unbox t e` is not
  `into_slot ~origin:Ue ~from:Any`: `ue_plan`'s `Recover_box` unboxes a
  list at its erased shape and leaves an `Any_cast` alone, and
  `into_slot` returns a `Coerce` node that the shape-reading code after
  several sites (`lifting.ml`'s match on `Any_cast`) would not see
  through.  Each site needs a plan whose expansion is exactly what it
  builds, and an extraction round.
- typed-fit fatal: no.  The census still has `unrelated` (911),
  `erase` (96), `unbox` (48), `eta`, `box`, `convert`, `regroup` verdicts
  at destinations and arguments (`/tmp/tcppirF/p4.log`, as before
  this session), each a latent mis-typing or a missing adapter.

Commits: `2d90230e5` (no `Not_yet_typed`), `8aa1b273b` (`gen_expr` shim
deleted), `190485521` (`Call.yields` a `Value_type`).  Extraction
byte-identical after the first and third (`git status --short tests`
empty, 2 wip extraction errors as at the base; the second is the same
function); unit tests and `scripts/check-module-deps.sh` pass.  Full
`make test` from clean at `190485521`: 1526 passed, 16 failed (all
`tests/wip`, as at the base), `git status --short tests` empty.

Next: `Declare_deduced` (resolved away by `Resolve`, readers ported per
file); then the ratchet sites, each with a plan whose expansion is what
it builds today; then real types for the `Unannotated` adapter operands,
origin by origin, with the shadow census as the gate.

### Phase D, sixth session (2026-11-23)

Done:
- **`Declare_deduced`.**  `Binding.t` is a GADT with the lowered-only
  `Declare_deduced : lowered Value_type.t * Core.Binder.t option -> lowered t`;
  `Resolve` writes it `Declare (Auto, b)`, so the settled passes after the
  seam still see it (finishing runs on the lowered phase up to the
  printer) but the printer never does.  Builders: `Typed.bind_deduced x e`
  (records `Typed.carried e`, else `Unannotated`) replaced the 25 literal
  `Declare (Auto, _)` builders; `Typed.bind ?binder x t e` replaced 36
  builders whose type is computed (`Bind_variable (x, Declare (t, b), e)`
  with `t` a variable or a call): a probe on `Resolve` found 1978 lowered
  `Declare (Auto, _)` left after the literal builders were converted, all
  from computed types, and zero after `Typed.bind`.  Under
  `CRANE_CHECK_IR`, `Pipeline.check_deduced_bindings` checks before and
  after the lowered passes that no lowered declaration is `Declare (Auto,
  _)`; the readers that matched `Declare (Auto, _)` now match only
  `Declare_deduced` (frame 4, loopify 2, local_closures, view_args,
  deduced_literals).  Readers that read a declared type uniformly
  (`aliased_after`, `constraints`, `return_moves`, `in_place_args`,
  `temporaries`, `simplify`'s `bind_by_reference` and constant tables,
  `erasure`'s constants, `declared_binders`, ...) read a deduced one as
  `auto`, as before; `Stmt.Binding.written` gives `(type, binder)` with
  `Auto` for a deduced one where a reader needs both.
  `Children` does not visit the recorded type (it is not written);
  `Map` rewrites it.
  Ported readers: `Frame.collect_type_env` and the resume handler's
  environment read a local's type from the record
  (`Frame.deduced_local_type`: a `Closure {groups = [ps]; result}` is
  `Function (ps stripped, result)`, anything else `Auto`, read back by
  `decltype_of_saved_local`) instead of matching the initialiser's
  `Lambda`.  A probe comparing the two: 136 disagreements, all generic
  lambdas with an `auto` parameter (local fixpoint `*_impl`s), which the
  old code typed `Function ([auto], R)` and the record types `Deduced
  Generic_lambda` (so `Auto`); no output changed (no frame keeps such a
  local at its type).  `View_args.declared_holdings` reads a deduced
  variable's canonical type from the record rather than from an
  initialiser that is a call with `yields`: 28 more variables are known
  canonical, no output changed.  `decltype_of_saved_local` itself is
  unchanged: it is the fallback for `Auto`, which is now exactly the
  deduced locals whose record is not a closure.
- **Coercion-builder ratchet: 41 sites to 1.**  New plan
  `Cast_box {into; tolerant}` (the cast a site makes of what it knows is
  boxed), built by `Coerce.unbox ?tolerant into e` through `into_slot`
  with the new origin `Built plan` (the site's own test stands, the census
  holds it to `decide`: 1084 `typed-shadow site agree`, 59 unchecked, 0
  disagree), and by `Cpp_ir.Coercion.cast_box` for control lowering
  (`frame.ml`'s resumed-result cast), which builds below `Coerce`.
  `Coerce.erase shape e` builds `Erase_as` (four `Erase_callable` sites in
  `construction.ml`, `functions.ml`).  `Analysis.converting_ctor` is
  `Erasure.converting_ctor` (it was a copy).  Rebuilding walkers
  (`Functions.return_captures_by_value`, `Lambda_params`, the
  `made_of_application` rewrite) map a cast or coercion's children with
  `Cpp_ir.Map` rather than rebuilding the cast.  The rule: `empty_box`
  is no longer counted (it builds an empty box, it adapts no value), and a
  constructor after `_,` is a pattern.  Look-through added where a
  lowering reader matched the cast a converted site now builds as a
  coercion: `lifting.ml`'s replacement strip (`Typed.head repl`),
  `match.ml`'s `should_strip` and `inductives.ml`'s phantom-cast strip
  (both on `Cast_box` only: looking through every coercion there strips
  `Ue` coercions the old code kept, changing `pair_indexed_inductive_any_cast`).
  Finding: `Cast_box` expands with `Erasure.unbox`'s structural rules
  only; whether `into` prints as a box is asked when the plan is made
  (`Coerce.unbox`), because the answer can change before the coercions
  pass runs.
  Left: `match.ml`'s field substitution for a wholesale-erased field
  (`gen_match_branch`, the `| _ -> unbox bare_ty (Local binding_name)`
  arm), `COERCION_BUILDERS_PENDING="core_to_cpp/match.ml:1"`.  As a
  coercion it changes four outputs (`mem_safety_probe12`, `free_monad`,
  `existential_closure_probe`, `type_indexed_inductive_probe`):
  `crane_call_erased(f, crane_any_cast<T2>(a0))` loses its inner cast.
  A probe in `Erasure.resolve_expr` showed the raw cast reaching the
  `casts` pass at `T2` (a named index variable) and the coerced one at a
  type written as a box, so some type rewrite between lowering and the
  `casts` pass reaches a coercion plan's types where it does not reach a
  raw cast's (or the reverse); not found yet.

Not done (steps 3-5 of this session's list), and why: the session went to
the two steps above and the `Cast_box` investigation.
- Real types for `Unannotated` operands: untouched.  The census numbers
  of the fifth session stand (`typed-shadow` at an unstated value:
  `erase_fn_arg_for_param` 88, `coerce` 40, `recover_carrier_result` 18).
  Order to take them: the `coerce` (`Ue`) operands first, since
  `Coerce.coerce` already receives `?from` from most callers; each origin
  with a census round (`/tmp/tcppir/extract.sh <log>`, then
  `grep '^typed-shadow' <log>`), no new `disagree`, byte-identical.
- The two `Coerce.result_site` reads in `Application` (`cod_site`,
  `filled_ty`): untouched; the fifth session's note stands (a probe
  comparing `Typed.applied` of the name's `Function_name` type with
  `spell_arrows (result_site id)` is the first step).
- typed-fit fatal: no; categories unchanged from the fifth session.

Commits: `3565d3dd3` (`Declare_deduced`), `c52816661` (ratchet).  Full `make test` from clean at `c52816661`: 1526 passed, 16 failed (all `tests/wip`, as at the base).  Extraction
byte-identical after each (`git status --short tests` empty, 2 wip
extraction errors as at the base); unit tests and
`scripts/check-module-deps.sh` pass.

Next: find the type rewrite that treats a `Cast_box` plan's type and a raw
cast's differently (start from `tvar_subst_stmt` / the phantom handling in
`Inductives` around the method body, and `Erasure.materialise`), convert
the last site and make the rule strict (delete
`COERCION_BUILDERS_PENDING`); then steps 3-5 as above.

### Phase D, seventh session (2026-11-23)

Done:
- **The last ratchet site; the rule is strict.**  The rewrite that treated a
  `Cast_box` plan's type differently from a raw cast's was
  `Core_plan.Head_relaxation.apply`'s `Unmentioned` case: it erases the
  type variables a function's head no longer mentions (`T2 = void` in
  `wrap_rect`) to `std::any` throughout the body, but leaves a raw
  `Any_cast`'s and `Tolerant_any_cast`'s target alone ("the cast's target
  is left alone; its operand is not").  `Map` reaches a coercion plan's
  types, so the `Cast_box`'s `into` became `std::any` and its expansion
  dropped the cast.  Found with a backtrace hook in `Map`'s `Cast_box` case
  (a named variable mapped to `Any`).  The rewrite now leaves a `Cast_box`
  coercion whole (`Coerce (({plan = Cast_box _; _} as c), e') -> Coerce (c,
  fe e')`), the same rule as for a cast; only `Cast_box`, since erasing the
  other plans' types there is what today's output relies on.  `match.ml`'s
  wholesale-erased field substitution builds `Coerce.unbox`;
  `COERCION_BUILDERS_PENDING` is deleted and `scripts/check-module-deps.sh`
  fails on any coercion builder in `core_to_cpp`/`control_to_cpp` outside
  `coerce.ml`.  Census: `typed-shadow site agree` 1196, 59 unchecked (no
  slot type), 0 disagree.
- **`Ue` operands typed where the caller had the value.**
  `Coerce.coerce ?value` takes the `Typed.t` the operand was lowered as:
  the value's type is `from` where the caller states the box, else
  `value`'s where `value.expr == expr` (the operand unchanged since), else
  what the node carries (a lambda always the latter, as before).
  `Construction.gen_stored_value_typed` keeps the value
  (`gen_stored_value` is its expression); passed at a constructor argument
  (`gen_expr_custom_cons`), a record field (`erased_domain_fun_ty` field),
  and an argument boxed for a type-variable parameter
  (`Application.gen_call_args`, `arg_typed`).  Census: `coerce unchecked
  (untyped value)` 40 -> 28, `coerce agree` 2294 -> 2306, 0 disagree.
  The 28 left are operands whose callers never had a `Typed.t` (built by
  hand: `recover_boxed_result`, `unbox_into`, `functions.ml`'s
  `needs_any_cast`, ...), each `~from:Any` callers' operand a node with no
  carried type.

Tried and reverted:
- **`Param` (`erase_fn_arg_for_param`) operands typed.**  The same change
  (`at_param ?value`, values kept at all four callers) moved 84 of the 88
  `unchecked (untyped value)` lines to `agree` but changed
  `type_level_fun_apply`: `app(..., crane_erase_fn([](Nat n) { return n;
  }), ...)` lost its adapter, which breaks the program (`app` reads `sem`
  as an erased callable).  Cause: the argument is a Core `Coerce` to `sem`
  (a value-indexed family at a function index) of a lambda, and
  `Typed_checks.of_built` types a lambda whose Core type has no arrows at
  that type (`Lambda l, Typed t, _` with `Arrows.of_type t = None` returns
  `Typed derived`), here `sem`, an opaque box; `decide` from an opaque
  source answers `none`, so the gate withholds the adapter.  The lambda's
  node carries no type either (`closure_arrows`: no return type, and
  `return n` is not read off its node).  Typing the lambda as unannotated
  in `of_built` instead fails the `CRANE_CHECK_IR` rule that a Core
  `coerce` form is typed.  So the value's type is a lie the lowering of
  the coerce tells (the Core coerce says `sem`, no box was built), not
  something `at_param` can repair.  Next: have the Core `Coerce`'s lowering
  type what it built (a closure, where it builds no box: params from the
  node, result `Deduced`), or give `closure_arrows` the body's type (the
  bound variable's `read_value_type`) so the node carries a closure; then
  redo `at_param ?value` (the script is `/tmp/tcppirI/param.py`).

Not done, and why:
- **The two `Coerce.result_site` reads in `Application`.**
  `filled_ty` (`eta_fun`, ~l.1488): the call `filled` always fills the
  callee exactly (`k = arity - |args|` eta parameters), so reading the
  callee's own type instead is `Typed.applied (Function_name (id,
  name_arrows id dom (Function (surplus, cod)))) arity`, and `name_arrows`
  spells the result at `result_site`: equal by construction
  (`Arrows.of_type`/`to_type` round-trip exactly), so the switch only moves
  the read into `name_arrows`, where the name's typing already owns it.
  One case differs: `arity = 0` (a constant whose codomain is a type
  variable, or an inline mapping with no `%aN`), where the name's type has
  an empty first group that `Typed.applied f 0` does not consume while
  `Typed.apply` does (`given >= n` with `n = 0` calls).  Smallest
  follow-up: make `applied` consume leading empty groups (as `apply`
  does), then switch `filled_ty` to the name's type (domain: the first
  `arity` of `decl_doms`).  `cod_site` (`excess_groups`, ~l.915) is not a
  call result: it spells a Core codomain the group loop re-expands per
  alias (`expand_core_fun_alias`, `core_drop_arrows`), so it needs the
  callee's `Value_type` with alias expansion in `Arrows`, not a probe.
- **typed-fit fatal: no.**  Census at `e149faefe` (`/tmp/tcppirI/p2.log`,
  same counts as the fifth session): `unrelated` 484 destination + 427
  argument (180 distinct lines), `erase` 96, `unbox` 48, `eta` 20, `box`
  12, `convert` 12, `regroup` 4.  The distinct `unrelated` lines by kind:
  a callable whose grouping or parameter types the value states
  differently (21; `coind_guard`'s `closure (T1,T2)->T3` into `fn(nat,
  nat)->nat`: a lambda typed at its own variables); a namespace
  qualification on one side only (13; a class's alias `memory_bit` against
  the class); an erased or boxed component (9); a promoted variable's
  alias against its instance member (`prom:addr` into `inst:_tcI0::addr`,
  8); a monad transformer by name against its unfolding (`stateT`, 8);
  `itreeF` against `itree` (the `observe` unfolding, 6); a type variable
  against a concrete type or carrier (5); 40 others (dead-branch
  `string` into `uint64_t`, `nat` into a record in `get_pair_bound_prop`,
  section aliases under `PIV call/2(scope)`), and 70 lines in the
  fixed-width form.  Each is a separate reconstruction defect (the value's
  type, the slot's, or the comparison's normalisation), none a census
  artefact one change removes.  Smallest follow-up: normalise the two
  spelling-only kinds in the comparison (namespace qualification, promoted
  alias against its member) and make typed-fit fatal under
  `CRANE_CHECK_IR` with a checked-in allowlist of the remaining (library,
  declaration, verdict) triples that may only shrink, the ratchet that
  closed the coercion builders.

Commits: `6776b455b` (last ratchet site, rule strict), `e149faefe`
(`Coerce.coerce ?value`).  Extraction byte-identical after each (`git
status --short tests` empty, 2 wip extraction errors as at the base);
unit tests and `scripts/check-module-deps.sh` pass.  Full `make test` from
clean at `6776b455b` and again at `e149faefe`: 1526 passed, 16 failed (all
`tests/wip`, as at the base), `git status --short tests` empty.

Next: type the Core `coerce` of a lambda as the closure it builds, then
the `Param` operands (`/tmp/tcppirI/param.py`); `Typed.applied` consuming
empty groups, then `filled_ty` from the name's type; the typed-fit
allowlist ratchet.
