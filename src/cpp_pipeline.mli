(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The passes a MiniCpp declaration goes through between translation and the
    printer.

    Control was lowered as the declaration was generated
    ({!Control_to_legacy_minicpp}), and is only checked here, under
    [CRANE_CHECK_IR] ({!Control_to_legacy_minicpp.check_lowered}).  Depth flattening and the {!Cpp_erasure} seam
    have to run in that order, and both have to run: a declaration that skipped
    flattening crashes the C++ parser, and one that skipped the seam is not a
    {!Cpp_erasure.settled} declaration at all.  So the sequence is a single
    function rather than a sequence its callers spell out -- there are no
    intermediate declarations to hand to the wrong pass, because none of them
    is nameable from outside. *)

(** [finish decl] runs every pass between translation and printing and
    hands back the printable declaration.  Under [CRANE_TRACE_PASSES] ([1], or a substring of the
    declaration's name) it reports which passes changed [decl] and its node
    count before and after each.  Under [CRANE_CHECK_IR] it fails if [decl]
    is not what control lowering recorded deciding of it, or if the result still owes
    the printer a decision one of its passes makes: an
    unspellable type, an unsettled constraint, an unresolved cast, an
    undeclared type variable, a mapping's unsupplied type argument, or a
    method or projection called as a function. *)
val finish : Minicpp.cpp_decl -> Cpp_erasure.settled


(** The names of the passes {!finish} runs, in order, the {!Cpp_erasure} seam
    among them.  Read by [unit_tests/pipeline_manifest.ml]. *)
val pass_names : string list
