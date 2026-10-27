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

    It also lowers the loops of tail modulo cons
    ({!Recursion_plan.modulo_cons_loops}): a function, or a local fixpoint
    of one member, whose every recursive
    call that is not a tail call is held in the hole of a chain of
    constructors returned is a loop whose turn there is a [Continue_into],
    its body read with Normalize's temporaries put back as the plan reads
    it.  Loopify lowers these, and under [CRANE_CHECK_IR] the calls its
    tail-modulo-cons transform rewrites must be their [Continue]s and
    [Continue_into]s.

    And the loops of the machines with a stack of frames
    ({!Recursion_plan.frame_loops}): a function recursing by a call that is
    not a tail call is a loop where each let, or sequential bind, whose
    right-hand side makes a recursive call is a [Resume].  What its machine
    adopts, a local fixpoint calling back into it or a partner's body run
    in place of a call, is an [Entry] of it.  Loopify lowers
    these, and under [CRANE_CHECK_IR] the calls its frame transform enters
    the machine by must be their [Continue]s, those it resumes after the
    [Continue]s in a [Resume]'s value.

    The loop of a top-level function is made from here as its recursive
    group is generated, that of a method as its struct's methods are, and
    that of a local fixpoint as translation generates it
    ({!Control_to_legacy_minicpp}), a machine's entry with it, and that of
    a helper lifted for a local fixpoint's function where translation makes
    the helper.  Loopify still makes the others -- a local fixpoint's that a
    machine may adopt or is lowered inside -- and under [CRANE_CHECK_IR]
    compares the calls it turns into jumps with the [Continue]s here
    ({!Loopify.lower_local_tail_loops}). *)

type t

val empty : t

(** What the machine of a loop adopts as a further entry
    ({!Control_ir.Term.entry}), as the recursion plan has it: the local
    fixpoint of one member at an occurrence ({!Recursion_plan.adoptable}),
    or the body of the partner [partner], its [parameters] innermost first,
    run in place of its calls [invoked]
    ({!Recursion_plan.adopted_invocations}). *)
type adoption =
  | Fixpoint of Miniml.Occurrence.t
  | Partner of {
      partner : Names.GlobRef.t;
      invoked : Miniml.Occurrence.t list;
      parameters : (Miniml.ml_ident * Miniml.ml_type) list;
      body : Miniml.ml_ast;
    }

(** [tail_loop ~effects ~target ~callee body] is [body], standing under the
    parameters of the loop [target], as that loop's body: [callee ~depth f]
    is the number of parameters of the loop's function where [f], under
    [depth] binders inside them, names it, [effects] says which binds and
    rets are sequential, and [inlined use] is the parameters, innermost
    first, and the body of the partner whose call [use] heads, where Loopify
    continues in that partner's body.  With [modulo_cons], a constructor
    application holding a recursive call as the one call of a chain of
    them is a [Continue_into], the chain read as
    {!Recursion_plan.strategy} reads it.  With [frames], a let or a
    sequential bind whose right-hand side calls the function is a [Resume]
    of its continuation, the right-hand side read as a body is.  A machine
    [adopted] has a further entry: the adopted fixpoint is an [Entry] where
    it is applied, entered by a [Continue] of it, or where a let binds it,
    the reads of the let's binder in its scope continuing it; the adopted
    partner's body is an [Entry] around the whole body, its calls run in
    place continuing it.  An entry's body continues the loop too. *)
val tail_loop :
  ?inlined:(Miniml.global_use -> ((Miniml.ml_ident * Miniml.ml_type) list * Miniml.ml_ast) option) ->
  ?modulo_cons:bool ->
  ?frames:bool ->
  ?adopted:adoption ->
  effects:Core_effects.t ->
  target:Control_ir.Loop.t ->
  callee:(depth:int -> Miniml.ml_ast -> int option) ->
  Miniml.ml_ast ->
  Control_ir.Term.t

(** [lower ~methods plan p] lowers the loops the plan [plan] of the
    normalized program [p] takes.  A function generated as a method,
    [methods] says, adopts nothing into its machine, as Loopify lowers a
    method ({!Loopify.transform_method_own}); nor does a machine adopt a
    fixpoint or a partner returning another type than its function -- told
    apart with every abbreviation unfolded, as the C++ does not spell them
    -- for a machine has one result. *)
val lower : methods:(Names.GlobRef.t -> bool) -> Recursion_plan.t -> Core.normalized Core.program -> t

(** Make [t] the extraction's, the one {!loop} reads. *)
val install : t -> unit

(** The loop [l], if it is lowered: a [Control_ir.Term.Loop]. *)
val loop : Control_ir.Loop.t -> Control_ir.Term.t option

(** The {!Control_ir.continues} of [t] the code made of it keeps no call of: those
    made of an occurrence no other [Continue] shares, nor any Core term [t]
    holds -- what it returns, binds, matches on, or passes a turn or a cell.
    A call Core copied shares its occurrence with its copies, any of which
    may stay a call where the others are turns: only by position is it
    told apart from them, and these are the occurrences that are not. *)
val taken_continues : Control_ir.Term.t -> Miniml.Occurrence.t list
