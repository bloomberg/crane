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
- [ ] Phase B2
- [ ] Phase C
- [ ] Phase D
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

