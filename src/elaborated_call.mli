(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A global call as Core elaborates it, before anything about its C++ is
    decided (docs/Pipeline-Disentangling-Plan.md, section 3.4): its callee,
    the role each argument the call gives the callee has, and the call's
    reading of the callee's scheme variables.  It holds no C++ type and no
    template argument.

    Transitional.  Its roles are elaborated from Core ahead of translation
    ({!Core_elaborate}) where translation meets the call as written, and
    where it is translated otherwise; the holes its context states are
    resolved where it is translated ({!Translation_calls.resolve_from_context}),
    and the C++ part of planning the call ({!Translation_calls.plan_call})
    starts from it. *)

(** The role an argument the call writes has. *)
type role =
  | Dictionary  (** A dictionary the callee takes as a template argument. *)
  | Erased_dictionary
      (** A dictionary the call erased whose parameter the callee still
          declares. *)
  | Regular  (** A value argument at one of the callee's parameters. *)
  | Excess  (** A value argument past the callee's arity, applied to its result. *)
  | Dropped
      (** An argument at no value position: a dummy, or a variable bound at
          an erased type, at a domain the declaration erased. *)

(** How the callee numbers its dictionary parameters against the order the
    call writes its dictionaries in. *)
type dictionary_order =
  | Source_order
  | Reversed

type t = private {
  callee : Names.GlobRef.t;
  callee_type : Miniml.ml_type;  (** As the callee is declared. *)
  args : Miniml.ml_ast list;  (** The arguments the call writes. *)
  roles : role list;  (** The role of each of {!args}, in order. *)
  primary : Miniml.ml_ast list;
      (** The arguments the callee takes, dictionaries among them, in
          source order. *)
  excess : Miniml.ml_ast list;  (** The [Excess] arguments. *)
  instances : Miniml.ml_ast list;
      (** The [Dictionary] arguments, in the order the callee numbers its
          dictionary parameters. *)
  erased_instances : int;  (** How many arguments are [Erased_dictionary]. *)
  regular : Miniml.ml_ast list;  (** The [Regular] arguments. *)
  tyargs : Call_tyargs.t;
      (** The callee's scheme variables as the call reads them, before they
          are spelled in the caller's scope. *)
}

(** [of_roles ~callee ~callee_type ~dictionaries ~tyargs args roles] -- the
    call of [callee] to [args], each with the role in [roles] at its
    position. *)
val of_roles :
  callee:Names.GlobRef.t ->
  callee_type:Miniml.ml_type ->
  dictionaries:dictionary_order ->
  tyargs:Call_tyargs.t ->
  Miniml.ml_ast list ->
  role list ->
  t

(** [with_tyargs c tyargs] is [c] reading its scheme variables as [tyargs]:
    a reading the call's context has refined. *)
val with_tyargs : t -> Call_tyargs.t -> t

(** Whether [a] and [b] elaborate one call alike: the same callee, the same
    argument nodes, each in the same role. *)
val same_roles : t -> t -> bool

(** How many of the callee's declared parameters the dictionaries occupy,
    erased ones included: a regular argument's declared position starts
    after them. *)
val leading_params : t -> int

(** Whether a dictionary stated a scheme variable the call had erased
    ({!Call_tyargs.Argument_heads}): the arguments at it are then built at
    that type, so the call has to write it. *)
val dictionary_filled : t -> bool
