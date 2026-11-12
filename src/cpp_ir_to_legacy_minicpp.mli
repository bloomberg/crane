(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Lowered CppIR back into MiniCpp, for the readers still written over
    MiniCpp: the control check and {!Move_check} under [CRANE_CHECK_IR], and
    Loopify's and local closures' statement rewrites, which convert around
    themselves.

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
