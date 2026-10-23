(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Control_to_legacy_minicpp (docs/Pipeline-Disentangling-Plan.md,
    Milestone 6, its compatibility bridge): a function's {!Control_ir}
    lowered, as the function is generated, to the MiniCpp loop the passes
    after it already read, so that {!Cpp_pipeline.finish} lowers none of
    that function's control itself.

    This version lowers the loop of direct tail recursion of a top-level
    function ({!Control_ir.Loop.Function}) that the configuration loopifies
    ({!Table.should_loopify}), that the recursion plan lowers so
    ({!Recursion_plan.Tail_loop}), and that neither inlines a partner nor is
    inlined into one ({!Recursion_plan.inlinings}).  Its jumps are the C++
    calls made of the loop's [Continue]s, by the occurrence each records
    ({!Minicpp.call_sig.cs_occurrence}); the parameters a jump leaves alone
    are those every [Continue] passes on unchanged
    ({!Control_ir.invariant_parameters}).  What is left to the C++ is how
    each is spelled: the arguments the call was translated with, and the
    shadow each varying parameter is kept in ({!Loopify_tail}).

    Under [CRANE_CHECK_IR] Loopify's own transform runs beside it, and must
    make the same loop ({!Loopify.checker_tail_loop}). *)

(** [lower_decl d] is the generated declaration [d], a function lowered as
    above where it is one, the function recording its loop
    ({!Minicpp.dfun.df_loop}). *)
val lower_decl : Minicpp.cpp_decl -> Minicpp.cpp_decl
