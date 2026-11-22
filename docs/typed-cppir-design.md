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

- [ ] Phase A
- [ ] Phase B1
- [ ] Phase B2
- [ ] Phase C
- [ ] Phase D
- [ ] Phase E (optional)
