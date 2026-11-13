(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The conversion of MiniCpp into CppIR, at the seams where code still
    built as MiniCpp meets code that reads CppIR.

    A translated declaration is lowered ({!Cpp_ir.Lowered}) by
    {!Cpp_pipeline.lower} before {!Cpp_pipeline.finish}, and every pass after
    that reads CppIR.  Control lowering ({!Control_to_cpp_ir}) converts at its
    entry points, and the declaration generators convert the MiniCpp types,
    expressions and members translation hands them.  A type or value written
    outside every declaration converts to
    {!Cpp_ir.Resolved} on its own: a form that exists only in a lowered
    program -- a type with no C++ spelling, an unsettled callable parameter,
    an undecided capture or [constexpr], an uninstantiated mapping -- has no
    constructor to convert to, and fails the conversion. *)

(** Why a declaration did not convert. *)
type failure =
  | Lowered_only of string
      (** It holds the named form, which only a lowered declaration may. *)
  | Dead of string
      (** It holds the named MiniCpp form, which nothing produces and so
          CppIR has no constructor for. *)

(** [describe f] is the message an anomaly reports for [f]. *)
val describe : failure -> string

(** [lower d] is [d] in CppIR, at the phase that may still owe resolution
    decisions.
    @raise Anomaly if [d] holds a form nothing produces. *)
val lower : Minicpp.cpp_decl -> Cpp_ir.Lowered.Decl.t

(** [lower_stmt s] is [s] in CppIR, as {!lower} converts a declaration. *)
val lower_stmt : Minicpp.cpp_stmt -> Cpp_ir.Lowered.Stmt.t

(** [lower_expr e] is [e] in CppIR, as {!lower} converts a declaration. *)
val lower_expr : Minicpp.cpp_expr -> Cpp_ir.Lowered.Expr.t

(** [lower_template_parameters ps] is the template parameter list [ps] in
    CppIR, as {!lower} converts a declaration's. *)
val lower_template_parameters :
  (Minicpp.template_type * Names.Id.t) list -> Cpp_ir.Lowered.phase Cpp_ir.Template.parameters

(** [lower_member m] is the struct member [m] in CppIR, as {!lower} converts
    a struct's. *)
val lower_member :
  Minicpp.cpp_field * Minicpp.cpp_visibility * Minicpp.section_tag -> Cpp_ir.Lowered.phase Cpp_ir.Field.member

(** [lower_type t] is [t] in CppIR, as {!lower} converts a declaration. *)
val lower_type : Minicpp.cpp_type -> Cpp_ir.Lowered.Type.t

(** [inline_template t] is the classified replacement text [t] in CppIR. *)
val inline_template : Minicpp.inline_template -> Cpp_ir.Foreign.template

(** The types and values written outside every finished declaration -- a
    merged record's field types, a module type's concept, a synthesised
    template's body -- convert one at a time: [type_ t] is [t] in CppIR,
    or why it is not expressible there, and likewise [expr e]. *)
val type_ : Minicpp.cpp_type -> (Cpp_ir.Resolved.Type.t, failure) result

(** [expr e] is [e] in CppIR, or why it is not expressible there. *)
val expr : Minicpp.cpp_expr -> (Cpp_ir.Resolved.Expr.t, failure) result

(** [type_ t], where [t] has to convert.
    @raise Anomaly if it does not. *)
val type_exn : Minicpp.cpp_type -> Cpp_ir.Resolved.Type.t

(** [instantiated_type_exn instantiate t] is [t] in CppIR, as [instantiate]
    rewrites it, at the phase that owes resolution nothing: a type written
    outside every finished declaration, whose mappings are instantiated where
    it is converted.
    @raise Anomaly if the rewritten type still owes resolution a decision. *)
val instantiated_type_exn :
  (Cpp_ir.Lowered.Type.t -> Cpp_ir.Lowered.Type.t) -> Minicpp.cpp_type -> Cpp_ir.Resolved.Type.t
