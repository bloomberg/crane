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

(** Whether a [TypeMapping] instance is recorded for this head. *)
val has_type_mapping : Names.GlobRef.t -> bool

(** Every head with a recorded [TypeMapping] instance, with its instances. *)
val type_mapping_heads : unit -> (Names.GlobRef.t * Names.GlobRef.t list) list

(** The mapping of a concrete source type, if one applies. *)
val resolve_type_mapping :
  Environ.env -> Evd.evar_map -> EConstr.types -> resolved_type_mapping option

(** The mapping of a source operation: a reference applied to at least as
    many arguments as the instance's [Ref] names. *)
val resolve_operation_mapping :
  Environ.env -> Evd.evar_map -> EConstr.t -> resolved_operation_mapping option

(** {1 Operation binders} *)

(** What Crane makes of a binder of an operation's type: a type parameter
    (its [%tN] position among the type parameters), a retained runtime
    argument (its [%aN] position among those), a type-class instance (passed
    by Crane apart from the runtime arguments), or erased (a proof, or an
    [Extraction Implicit] position). *)
type binder_role = Type_parameter of int | Runtime of int | Instance | Erased

type operation_binder = {
  binder_id : Names.Id.t;  (** the variable standing for it in {!binders_env} *)
  binder_name : Names.Name.t;  (** its name in the source *)
  binder_type : EConstr.types;  (** over the variables of the binders before it *)
  role : binder_role;
}

type operation_binders = {
  binders_env : Environ.env;  (** declares one variable per binder *)
  binders : operation_binder list;  (** in source order *)
  result_type : EConstr.types;
  generic_use : EConstr.t;  (** the operation applied to every variable *)
}

(** [Table.implicits_of_global], set by [Table]: the positions, from 1, of
    the [Crane Extraction Implicit] arguments of a global. *)
val implicit_positions : (Names.GlobRef.t -> Int.Set.t) ref

(** Whether a class is one Crane skips ([Crane Extract Skip], a mapping to
    the empty string), set by [Table]: its instances are passed at no
    template parameter. *)
val skipped_class : (Names.GlobRef.t -> bool) ref

(** Whether an instance binder of type [t] is a dictionary a call passes as
    a template argument: its class is not one Crane skips. *)
val is_kept_instance : Environ.env -> Evd.evar_map -> EConstr.types -> bool

(** The binders of the type of the operation [g], classified as Crane's
    erasure classifies them. *)
val operation_binders : Environ.env -> Evd.evar_map -> Names.GlobRef.t -> operation_binders

(** Whether an [OperationMapping] instance is recorded for this head. *)
val has_operation_mapping : Names.GlobRef.t -> bool

(** Every head with a recorded [OperationMapping] instance, with its
    instances. *)
val operation_mapping_heads : unit -> (Names.GlobRef.t * Names.GlobRef.t list) list

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
