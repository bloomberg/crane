(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The one-way conversion of finished MiniCpp declarations into
    {!Cpp_ir.Resolved}.

    A finished declaration has crossed every resolution pass, so what it
    converts to is resolved: a form that exists only in a lowered program --
    a type with no C++ spelling, an unsettled callable parameter, an
    undecided capture or [constexpr], an uninstantiated mapping block or
    match -- has no constructor to convert to, and fails the conversion.

    {!Unit_program.finish} converts every declaration it finishes, and a
    declaration that does not convert is an anomaly; the program keeps only
    the conversion, so everything after the finish seam reads CppIR. *)

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

(** [lower_type t] is [t] in CppIR, as {!lower} converts a declaration. *)
val lower_type : Minicpp.cpp_type -> Cpp_ir.Lowered.Type.t

(** [inline_template t] is the classified replacement text [t] in CppIR. *)
val inline_template : Minicpp.inline_template -> Cpp_ir.Foreign.template

(** [convert d] is [d] in CppIR, or why it is not expressible there. *)
val convert : Minicpp.cpp_decl -> (Cpp_ir.Resolved.Decl.t, failure) result

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

(** [foreign_piece p] is the piece [p] of a mapping's instantiated text in
    CppIR; every piece converts. *)
val foreign_piece : Minicpp.foreign_piece -> Cpp_ir.Foreign.piece
