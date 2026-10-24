(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Control_to_legacy_minicpp (docs/Pipeline-Disentangling-Plan.md,
    Milestone 6, its compatibility bridge): a function's {!Control_ir}
    lowered, as the function is generated, to the MiniCpp loop the passes
    after it already read, so that {!Cpp_pipeline.finish} does not call
    Loopify for that function at all.

    This version lowers the loop of direct tail recursion of a top-level
    function ({!Control_ir.Loop.Function}) that the configuration loopifies
    ({!Table.should_loopify}) and that the recursion plan lowers so
    ({!Recursion_plan.Tail_loop}).  A recursive group is lowered as a unit,
    once all of its members are generated: a member continues in the bodies
    of the partners the plan inlines into it ({!Recursion_plan.inlinings}),
    read as they were generated.  Its jumps are the C++ calls made of the
    loop's [Continue]s, by the occurrence each records
    ({!Minicpp.call_sig.cs_occurrence}); the parameters a jump leaves alone
    are those every [Continue] passes on unchanged
    ({!Control_ir.invariant_parameters}).  What is left to the C++ is how
    each is spelled: the arguments the call was translated with, the
    statements of a partner continued in, and the shadow each varying
    parameter is kept in ({!Loopify_tail}).  The local fixpoints in the
    loop are lowered as Loopify lowers them after its own transform
    ({!Loopify.after_tail_loop}).

    So is the loop of a top-level function the plan lowers tail modulo cons
    ({!Recursion_plan.Modulo_cons}): its turns that build what they return
    ({!Control_ir.Term.Continue_into}) are the branches its cells are made
    in, each read along the constructors of its chain around the call its
    occurrence names ({!Loopify_tmc.branch_along}), and the others its
    jumps.  It is left to Loopify where Loopify would do anything else with
    the function ({!Loopify.modulo_cons_loop}): tie an Equations knot,
    adopt a local fixpoint into a machine, or fall back to a frame stack.
    So is the machine with a stack of frames of a function the plan lowers
    so ({!Recursion_plan.Frame_stack}): the calls entering it are those made
    of its loop's [Continue]s, those it resumes after the [Continue]s in a
    [Resume]'s value ({!Loopify.frame_machine}).  A machine whose ControlIR
    has an entry ({!Control_ir.Term.Entry}) takes the body Loopify finds
    for it -- the adopted local fixpoint's lambdas, or the partner's body
    invoked in place -- as its second entry, where that body is the
    entry's.  It is left to Loopify where Loopify would adopt another body,
    tie an Equations knot, or leave a call behind.

    The loop of a local fixpoint of one member ({!Control_ir.Loop.Member})
    is lowered so too, as translation generates the fixpoint: the lambda it
    is declared as is that loop, where it was the pair of lambdas tying the
    knot of a Y-combinator that Loopify recognised ({!local_loop}).  So is a
    method's, once its struct's methods are generated: its receiver is the
    loop's first variable; a tail loop's parameters a jump leaves alone are
    read off the Core binders of the receiver and the parameters, and a loop
    tail modulo cons or a machine takes the calls its ControlIR continues by
    ({!lower_methods}).

    Under [CRANE_CHECK_IR] Loopify's own transform runs beside it, and must
    make the same loop ({!Loopify.checker_tail_loop},
    {!Loopify.checker_modulo_cons}, {!Loopify.lower_local_tail_loops}). *)

(** [local_loop ~owner ~function_ ~member ~tparams ~name ~self_passing l]
    is the statement declaring the local fixpoint [name], the function
    [member] of a Core fixpoint of one member, generated in the body of the
    definition [owner], a function's where [function_], as the loop of its
    ControlIR, where the recursion plan lowers it so and Loopify would: [l]
    its lambda, its body calling the fixpoint by [name] and its type
    parameters [tparams], with the loop as its body.  A tail loop is
    lowered so in any body; a machine with a stack of frames in the body of
    a function Loopify loopifies, as Loopify lowers it
    ({!Loopify.local_frame_machine}), even where that function is a
    machine itself, whose transform takes the local machine as the closure
    it is.  [None] where it is not one: a fixpoint that may be adopted into
    a machine ({!Recursion_plan.adoptable_somewhere}), a tail loop in a
    definition Loopify makes a machine with a stack of its own of, one whose
    loop leaves one of its calls behind, or that Loopify declines; it is
    then generated as the Y-combinator [self_passing ()] Loopify
    recognises.  Under
    [CRANE_CHECK_IR] the statement must be the one Loopify makes of that
    Y-combinator. *)
val local_loop :
  owner:Names.GlobRef.t option ->
  function_:bool ->
  member:Miniml.Occurrence.t * int ->
  tparams:(Minicpp.template_type * Names.Id.t) list ->
  name:Names.Id.t ->
  self_passing:(unit -> Minicpp.cpp_stmt list) ->
  Minicpp.cpp_lambda ->
  Minicpp.cpp_stmt option

(** [lower_methods ~merged r vars fields] is [fields], members of the struct
    of the inductive [r] of variables [vars], with each method made of a
    function the recursion plan lowers to a loop -- a tail loop, one tail
    modulo cons, or a machine with a stack -- and Loopify would loopify,
    lowered to that loop, recording it ({!Minicpp.method_field.mf_loop}),
    as Loopify lowers a method: its receiver the loop's first variable.
    [merged] says whether the struct is merged into its module's, whose
    members Loopify loopifies only where it loopifies everything.  Under
    [CRANE_CHECK_IR] Loopify's own transform runs beside it and must make the
    same method. *)
val lower_methods :
  merged:bool ->
  Names.GlobRef.t ->
  Names.Id.t list ->
  (Minicpp.cpp_field * Minicpp.cpp_visibility * Minicpp.section_tag) list ->
  (Minicpp.cpp_field * Minicpp.cpp_visibility * Minicpp.section_tag) list

(** [lower_lifted d] is the helper [d], lifted out of a body for the
    function of a local fixpoint ({!Lifted.fixpoint}), lowered as a
    function is above, where Loopify would loopify it: to the loop of that
    member's ControlIR ({!Control_ir.Loop.Member}), entered by the member's
    calls, the variables the helper captures, its first parameters, passed
    on unchanged by every one of them. *)
val lower_lifted : Minicpp.cpp_decl -> Minicpp.cpp_decl

(** [lower_group ds] is the declarations [ds], generated for the members of
    one recursive group, in its order, with each function lowered as above
    where it is one, recording its loop ({!Minicpp.dfun.df_loop}).  The
    members that inline one another and that Loopify would loopify are
    lowered all of them or none: Loopify, which lowers the others when the
    unit is finished, inlines a partner as it was generated. *)
val lower_group : Minicpp.cpp_decl list -> Minicpp.cpp_decl list
