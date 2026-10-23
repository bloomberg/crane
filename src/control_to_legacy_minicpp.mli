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

    The loop of a local fixpoint of one member ({!Control_ir.Loop.Member})
    is lowered so too, as translation generates the fixpoint: the lambda it
    is declared as is that loop, where it was the pair of lambdas tying the
    knot of a Y-combinator that Loopify recognised ({!local_loop}).

    Under [CRANE_CHECK_IR] Loopify's own transform runs beside it, and must
    make the same loop ({!Loopify.checker_tail_loop},
    {!Loopify.lower_local_tail_loops}). *)

(** [local_loop ~owner ~member ~tparams ~name ~self_passing l] is the
    statement declaring the local fixpoint [name], the function [member] of
    a Core fixpoint of one member, generated in the body of the definition
    [owner], as the loop of its ControlIR, where the recursion plan lowers it
    so and Loopify would: [l] its lambda, its body calling the fixpoint by
    [name] and its type parameters [tparams], with the loop as its body.
    [None] where it is not one: a fixpoint that may be adopted into a
    machine ({!Recursion_plan.adoptable_somewhere}), one in a definition
    Loopify makes a machine with a stack of its own of, whose loop leaves
    one of its calls behind, or that Loopify declines; it is then generated
    as the Y-combinator [self_passing ()] Loopify recognises.  Under
    [CRANE_CHECK_IR] the statement must be the one Loopify makes of that
    Y-combinator. *)
val local_loop :
  owner:Names.GlobRef.t option ->
  member:Miniml.Occurrence.t * int ->
  tparams:(Minicpp.template_type * Names.Id.t) list ->
  name:Names.Id.t ->
  self_passing:(unit -> Minicpp.cpp_stmt list) ->
  Minicpp.cpp_lambda ->
  Minicpp.cpp_stmt option

(** [lower_group ds] is the declarations [ds], generated for the members of
    one recursive group, in its order, with each function lowered as above
    where it is one, recording its loop ({!Minicpp.dfun.df_loop}).  The
    members that inline one another and that Loopify would loopify are
    lowered all of them or none: Loopify, which lowers the others when the
    unit is finished, inlines a partner as it was generated. *)
val lower_group : Minicpp.cpp_decl list -> Minicpp.cpp_decl list
