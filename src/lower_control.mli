(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** LowerControl (docs/Pipeline-Disentangling-Plan.md, Milestone 6): the
    {!Control_ir} of a normalized program, from its Core bodies and its
    recursion plan.

    This first version lowers the loops of direct tail recursion
    ({!Recursion_plan.tail_loops}): a function, or a local fixpoint of one
    member, that recurses only by tail calls and inlines no partner.  Its
    body is read as {!Recursion_plan} reads it -- applications whole, a
    let's body, a match's branches, a coercion's operand, a beta-redex's
    body, a sequential bind's continuation and a ret's value, and a custom
    that is its argument, standing where the term does -- and each of its
    recursive calls there is a [Continue]; a term no recursive call is made
    in is a [Return] of it as it is.

    The loop of a top-level function that inlines no partner, and is
    inlined into none, is made from here as the function is generated
    ({!Control_to_legacy_minicpp}).  Loopify still makes the others; under
    [CRANE_CHECK_IR] it compares the calls it turns into jumps with the
    [Continue]s here ({!Loopify.transform_decl}). *)

type t

val empty : t

(** [tail_loop ~effects ~target ~callee body] is [body], standing under the
    parameters of the loop [target], as that loop's body: [callee ~depth f]
    is the number of parameters of the loop's function where [f], under
    [depth] binders inside them, names it, [effects] says which binds and
    rets are sequential, and [inlined use] is the parameters, innermost
    first, and the body of the partner whose call [use] heads, where Loopify
    continues in that partner's body. *)
val tail_loop :
  ?inlined:(Miniml.global_use -> ((Miniml.ml_ident * Miniml.ml_type) list * Miniml.ml_ast) option) ->
  effects:Core_effects.t ->
  target:Control_ir.Loop.t ->
  callee:(depth:int -> Miniml.ml_ast -> int option) ->
  Miniml.ml_ast ->
  Control_ir.Term.t

(** [lower plan p] lowers the loops the plan [plan] of the normalized
    program [p] takes. *)
val lower : Recursion_plan.t -> Core.normalized Core.program -> t

(** Make [t] the extraction's, the one {!loop} reads. *)
val install : t -> unit

(** The loop [l], if it is lowered: a [Control_ir.Term.Loop]. *)
val loop : Control_ir.Loop.t -> Control_ir.Term.t option
