(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Finding the typed mapping of a source type or operation (plan D1).

    {!discover} runs when an extraction starts: it enumerates the instances
    of [TypeMapping] and [OperationMapping] that are active (an [#[export]]
    instance is active once its module is imported) and records each under
    its head: the head reference of [T] in [TypeMapping T], the referenced
    declaration in [OperationMapping (Ref d)].

    Resolution is lazy and per instantiation: every recorded instance with
    the head is tried by unifying its class argument with the query; none
    applying means unmapped, more than one is an ambiguity error naming all
    of them (instance priority is never consulted), and the one that applies
    is decoded ({!Mapping_decode}), validated ({!Mapping_validate}) and
    cached by the query in an [Extraction]-scoped table.

    [CRANE_TRACE_MAPPINGS=1] reports the discovered heads and every resolved
    descriptor. *)

open Mapping_descriptor

type resolved_type_mapping = {
  type_instance : Names.GlobRef.t;
  type_source : Constr.t;
  type_mapping : type_mapping;
}

type resolved_operation_mapping = {
  operation_instance : Names.GlobRef.t;
  operation_source : declaration;
  operation_mapping : operation_mapping;
}

(** Record the heads of the active instances, emptying the caches. *)
val discover : unit -> unit

(** Whether a [TypeMapping] or [OperationMapping] instance is recorded for
    this head. *)
val has_new_style_mapping : Names.GlobRef.t -> bool

(** The mapping of a concrete source type, if one applies. *)
val resolve_type_mapping :
  Environ.env -> Evd.evar_map -> EConstr.types -> resolved_type_mapping option

(** The mapping of a source operation: a reference applied to at least as
    many arguments as the instance's [Ref] names. *)
val resolve_operation_mapping :
  Environ.env -> Evd.evar_map -> EConstr.t -> resolved_operation_mapping option

(** {1 Debug commands} *)

(** [Crane Show Mapping c]: print the mapping of [c], a type or an
    operation. *)
val show : Constrexpr.constr_expr -> unit

(** [Crane Check Mapping c Selects inst]: fail unless [inst] maps [c]. *)
val check_selects : Constrexpr.constr_expr -> Libnames.qualid -> unit

(** [Crane Check Mapping c Unmapped]: fail if a mapping applies to [c]. *)
val check_unmapped : Constrexpr.constr_expr -> unit

(** [Crane Check Mapping c Fails With "text"]: fail unless resolving the
    mapping of [c] fails with a message containing [text] (spacing
    ignored). *)
val check_fails : Constrexpr.constr_expr -> string -> unit
