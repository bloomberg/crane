(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Lowered CppIR back into MiniCpp: what control lowering hands back to
    translation, which still generates MiniCpp, and what
    {!Cpp_pipeline}'s round-trip check under [CRANE_CHECK_IR] compares.

    The conversion inverts {!Legacy_minicpp_to_cpp_ir.lower}: lowering a
    declaration and converting it back gives the declaration back. *)

(** [decl d] is [d] in MiniCpp. *)
val decl : Cpp_ir.Lowered.Decl.t -> Minicpp.cpp_decl

(** [ty t] is [t] in MiniCpp. *)
val ty : Cpp_ir.Lowered.Type.t -> Minicpp.cpp_type

(** [expr e] is [e] in MiniCpp. *)
val expr : Cpp_ir.Lowered.Expr.t -> Minicpp.cpp_expr

(** [stmt s] is [s] in MiniCpp. *)
val stmt : Cpp_ir.Lowered.Stmt.t -> Minicpp.cpp_stmt

(** [template_parameters ps] is the template parameter list [ps] in
    MiniCpp. *)
val template_parameters : Cpp_ir.Lowered.phase Cpp_ir.Template.parameters -> (Minicpp.template_type * Names.Id.t) list

