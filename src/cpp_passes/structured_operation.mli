(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A call to an operation mapping with a structured body
    ({!Base.Mapping_operation.t.structured}), lowered where the mapping's
    applications are instantiated ({!Erasure.instantiate_foreign}): the body
    as CppIR, each [Arg] the call's argument at its position, already
    evaluated once where the body names it more than once
    ({!Shared_args}, which counts the holes of the body's text).

    Conversions are folded again at the use ({!Base.Mapping_term.fold}),
    where an argument the call supplies as an integer literal is known: R1
    makes a conversion of it a literal of the target type.

    The lowered body is wrapped in {!Cpp_ir.Expr.Mapped_operation}, which
    names the operation, so that its headers are included. *)

type ty = Cpp_ir.Lowered.Type.t
type expr = Cpp_ir.Lowered.Expr.t

(** Whether a call of [r] to [values] is lowered from its structured body:
    [r] has one, and no argument is a string literal or a character array
    (which the text path writes as the string object an operator or member
    access needs). *)
val lowers : Names.GlobRef.t -> expr list -> bool

(** The call of [r] to [values], at the type arguments [types], yielding
    [yields]. *)
val lower : Names.GlobRef.t -> types:ty list -> yields:ty option -> values:expr list -> expr
