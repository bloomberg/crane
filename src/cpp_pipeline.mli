(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The passes a declaration goes through between generation and the
    printer.  It reaches them in CppIR ({!Cpp_ir.Lowered}), every pass
    runs over CppIR, and the declaration handed back is resolved
    ({!Cpp_ir.Resolved}).

    Control was lowered as the declaration was generated
    ({!Control_to_cpp_ir}), and is only checked here, under
    [CRANE_CHECK_IR] ({!Control_to_cpp_ir.check_lowered}).  Depth flattening and the {!Cpp_erasure} seam
    have to run in that order, and both have to run: a declaration that skipped
    flattening crashes the C++ parser, and one that skipped the seam is not a
    {!Cpp_erasure.settled} declaration at all.  So the sequence is a single
    function rather than a sequence its callers spell out -- there are no
    intermediate declarations to hand to the wrong pass, because none of them
    is nameable from outside. *)

(** The check the "control" pass runs under [CRANE_CHECK_IR]: that what a
    declaration of the unit emits is what control lowering recorded deciding
    ({!Control_to_cpp_ir.check_lowered}).  Control lowering comes before
    finishing, so its caller hands the check in. *)
type control_check = unit:Unit_plan.Context.t -> Cpp_ir.Lowered.Decl.t -> unit

(** [finish u decl] runs every pass between translation and printing over
    [decl], a declaration of the unit [u], and hands back the printable
    declaration.  Under [CRANE_TRACE_PASSES] ([1], or a substring of the
    declaration's name) it reports which passes changed [decl] and its node
    count before and after each.  Under [CRANE_CHECK_IR] it fails if [decl]
    is not what control lowering recorded deciding of it, if the result
    still owes the printer a decision one of its passes makes (an
    unspellable type, an unsettled constraint, an unresolved cast, an
    undeclared type variable, a mapping's unsupplied type argument, a method
    or projection called as a function, and the rest of
    {!Cpp_ir.Representation_obligation.t}), or if what it borrows and moves
    fails {!Borrow_projection.check_decl} or {!Move_check.check_decl}. *)
val finish : check_control:control_check -> Unit_plan.Context.t -> Cpp_ir.Lowered.Decl.t -> Cpp_ir.Resolved.Decl.t


(** [resolve_type ~what t] is the lowered type [t], written outside every
    declaration {!finish} resolves -- a record field's type generated ahead
    of its declaration, a module type's concept -- at the resolved phase.
    With {!finish}, these are the one conversion from {!Cpp_ir.Lowered} to
    {!Cpp_ir.Resolved}.  A form only a lowered value may hold is an anomaly
    naming [what]. *)
val resolve_type : what:string -> Cpp_ir.Lowered.Type.t -> Cpp_ir.Resolved.Type.t

(** {!resolve_type} for an expression. *)
val resolve_expr : what:string -> Cpp_ir.Lowered.Expr.t -> Cpp_ir.Resolved.Expr.t

(** [spell_type t] is {!resolve_type} of [t] with every opaque type written
    as the erased type it would be printed as: a type no declaration holds,
    spelled for a diagnostic. *)
val spell_type : Cpp_ir.Lowered.Type.t -> Cpp_ir.Resolved.Type.t

(** The names of the passes {!finish} runs, in order, the {!Cpp_erasure} seam
    among them.  Read by [unit_tests/pipeline_manifest.ml]. *)
val pass_names : string list
