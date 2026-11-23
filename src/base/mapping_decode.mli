(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Reading a resolved typed mapping out of Rocq.

    A descriptor term is read node by node: each node is put in weak head
    normal form and must then be a constructor of the descriptor inductive
    expected there (found through its [Register ... as crane.mapping.X]
    name, by position), of [list], [option], [prod] or [nat], or a primitive
    string literal.  Nothing is normalised ahead: the argument of [Ref] is
    therefore read as written and keeps its identity even when the
    declaration has a body.  A term that does not reduce to the expected
    shape, or a [Ref] whose argument is not a reference, is a user error. *)

open Mapping_descriptor

(** The global registered as [crane.mapping.<name>], if
    [Crane.Mapping.Descriptor] is loaded. *)
val registered : string -> Names.GlobRef.t option

(** The dictionary of a [TypeMapping T] instance, without undefined
    evars. *)
val type_mapping : Environ.env -> Evd.evar_map -> EConstr.t -> type_mapping

(** The dictionary of an [OperationMapping (Ref d)] instance. *)
val operation_mapping :
  Environ.env -> Evd.evar_map -> EConstr.t -> operation_mapping

(** The argument of a [Ref], as a declaration; [None] if it is not a
    reference possibly applied to parameters. *)
val reference_of :
  Environ.env -> Evd.evar_map -> EConstr.t -> declaration option

val pr_declaration : Environ.env -> declaration -> Pp.t
val pr_type_expr : Environ.env -> Cpp.type_expr -> Pp.t
val pr_type_mapping : Environ.env -> type_mapping -> Pp.t
val pr_operation_mapping : operation_mapping -> Pp.t
