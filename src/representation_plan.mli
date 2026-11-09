(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Whether a pattern binder holds a box, planned from Core ahead of lowering
    (docs/Pipeline-Disentangling-Plan.md, Milestone 4: a binder's
    representation, Value or Boxed).

    Transitional.  Lowering decides a binder's representation itself, by the
    C++ type it records for each binder ({!Translation_types.binder_is_boxed});
    the plan reaches an answer for every pattern binder of a region from the
    region's Core body alone -- the ML types its binders are bound at, the
    type each match is annotated with, the constructors' declared fields, the
    scope's type variables -- by the same decisions lowering makes
    ({!Translation_types.match_scrutinee_type},
    {!Translation_types.custom_match_scrutinee},
    {!Translation_types.pattern_field_pins}), with the plan's own answers for
    the binders it reads in place of the C++ types lowering recorded.  Under
    [CRANE_CHECK_IR] translation checks the two agree for every pattern
    binder it declares.  Nothing reads the plan otherwise.

    What it does not plan is a lambda's parameter: lowering types it by the
    C++ slot the lambda fills.  An answer that rests on one -- a match over
    such a parameter, or over a field matched out of one -- is marked so,
    and not checked. *)

(** [region ~outer body] -- every pattern binder of [body], a region generated
    in the scope [outer] binds, planned: keyed by its site
    ({!Core_binder.site}, the match and branch) and its field's index there.
    Reads types in the type-variable scope current when it is called, which
    is the region's; its outer binders at the ML types [outer] gives them,
    converted.  A binder's recorded C++ type is never read. *)
val region : outer:Lexenv.t -> Miniml.ml_ast -> (Core_binder.site * int * Translation_state.planned_repr) list

(** [check ~site ~field ~live] -- a [CRANE_CHECK_IR] violation unless the
    region's plan ({!Translation_state.translation_ctx.representation}) boxes
    the pattern binder of field [field] bound at [site] exactly when lowering
    does ([live]), or marks its answer as resting on a lambda's parameter.  A
    binder the plan has no answer for is a violation too. *)
val check : site:Core_binder.site -> field:int -> live:bool -> unit
