(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Whether a binder holds a box, planned from Core ahead of lowering: each
    binder's representation is either a value or a box ([std::any]), and the
    plan decides which from the Core body of a region before translation
    lowers it.  It runs once per region, from
    {!Translation_state.with_region} through the
    {!Translation_state.plan_representation} hook, and its answers are kept
    in {!Translation_state.lexical.representation} and
    {!Translation_state.lexical.planned_reads}; {!Position_plan} reads the
    latter.

    Lowering also records a C++ type for each binder, and reads whether it
    is a box off that ({!Translation_binders.binder_is_boxed}) only to hold
    the plan to it under [CRANE_CHECK_IR].  The plan reaches an answer for
    every pattern binder of a region from the region's Core body alone
 -- the Core types its binders are bound at, the
    type each match is annotated with, the constructors' declared fields, the
    scope's type variables -- by the same decisions lowering makes
    ({!Translation_match_types.match_scrutinee_type},
    {!Translation_match_types.custom_match_scrutinee},
    {!Translation_match_types.pattern_field_pins}), with the plan's own answers for
    the binders it reads in place of the C++ types lowering recorded.  Under
    [CRANE_CHECK_IR] translation checks the two agree for every pattern
    binder it declares: a match's branch, a custom match's, the reuse arm's
    second declaration of a branch's fields, a record projection's.  An enum
    branch binds none.

    Lowering takes whether a variable read holds a box from the plan alone
    ({!Translation_binders.read_is_boxed}); a read the plan has no answer for
    is an anomaly.  Pattern binders' declarations, and every C++ type
    lowering spells a binder at, are still its own.

    A lambda's binders are planned where lowering generates it: one a custom
    constructor stores into an erased field, rewritten as lowering rewrites
    it ({!Translation_ctor_args.erased_fn_lambda}), at the constructor's own
    drafted instantiation; one passed to a global, refined against the
    parameter's Core type at the call's reading
    ({!Translation_lambda_params.slot_refined_lambda},
    {!Core_elaborate.instantiate}).  Its parameters are declared and assigned
    as lowering declares them ({!Translation_lambda_params.lambda_binder_emitted},
    {!Translation_lambda_params.lambda_param_cpp_type},
    {!Translation_lambda_params.lambda_param_assigned}), against the C++ slot the
    plan reads off the position: a global's parameter type at the call's
    reading, its erased domains [const auto &] where the callee deduces the
    callable; a local function's declared domain; a constructor field's type
    (a record's only where it returns a function, a custom constructor's
    signature where it erased only its domain); the region's return type for
    a lambda the region is.  None reads what the position states beyond the
    term: the destination's C++ type, the Core type the call's position
    expects, whether it is a box.

    Every variable read of the region is planned too, whatever bound the
    binder it reads -- a pattern, a let, a lambda's parameter, a local
    fixpoint, the region's outer scope -- and checked against lowering's
    answer where it is read ({!Translation_binders.read_is_boxed}).  A let bound to a component read
    out of a pair recovered from a box is bound at a dummy type, as lowering
    binds it ({!Translation_erasure.stmts_yield_boxed}). *)

(** [region ctx body] -- every pattern binder of [body], a region generated
    in the translation context [ctx], planned: keyed by its site
    ({!Core_binder.site}, the match and branch) and its field's index there.
    What it reads of the context it reads off [ctx], not the global one: the
    scope [outer] its lexical environment binds, the type variables in scope
    and the return type, which are the region's; its outer binders at the
    types the head of the declaration being generated declares them at,
    where it declares them directly in [outer] ([declared_outer] in
    {!Translation_state}), the rest at the Core types [outer] gives them,
    converted.  Each read is planned at the C++ type of its binder too.  A
    binder's recorded C++ type is never read. *)
val region :
  Translation_state.t ->
  Core.Expr.t ->
  (Core_binder.site * int * Translation_state.planned_repr) list
  * (Core.Occurrence.t * Translation_state.Planned_read.t) list

(** [check ctx ~site ~field ~live ()] -- a [CRANE_CHECK_IR] violation unless
    the region's plan in [ctx] ({!Translation_state.lexical.representation}) boxes
    the pattern binder of field [field] bound at [site] exactly when lowering
    does ([live]).  A binder the plan has no answer for is a violation too.
    [as_bound]: the binder is declared at the type it is bound at, nothing
    pinned down -- the reuse arm's second declaration of a branch's fields, a
    record projection in an expression -- and checked against that answer. *)
val check :
  ?as_bound:bool -> Translation_state.translation_ctx -> site:Core_binder.site -> field:int -> live:bool -> unit -> unit
