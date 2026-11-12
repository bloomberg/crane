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
    resolved, and the callee's types instantiated, by
    {!Core_elaborate.instantiate} ({!instantiated}), which the C++ part of
    planning the call ({!Translation_calls.plan_call}) starts from. *)

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

(** A call whose reading of its callee's scheme variables is complete, and
    the callee's types at that reading: section 3.4's [ElaboratedCall], the
    semantic half of planning a call ({!Core_elaborate.instantiate}).  It
    holds no C++ type, and is decided before, and without, anything about
    the call's C++: the C++ half of planning
    ({!Translation_calls.plan_call}) reads it and adds to it, never the
    other way.

    Planned ahead of translation by the Core walk
    ({!Core_elaborate.structure}), in the walk's lexical environment and
    with the ML types it gives the call's position, and taken at the
    argument nodes translation meets ({!at_call}).  Transitional: a call
    translation builds itself is instantiated where it is translated, in the
    traversal's environment and position. *)
type instantiated = private {
  call : t;  (** The call, with the holes its context states resolved. *)
  reading : Call_tyargs.t;
      (** The scheme variables as the call reads them in the end: {!call}'s
          reading, plus a partial application's variables resolved for the
          lambda it is eta-expanded into. *)
  tys : Mlutil.Var_types.t;  (** {!reading} as substitutions take it ({!Call_tyargs.by_variable}). *)
  callee_type_at_call : Miniml.ml_type;  (** The callee's type at {!reading}. *)
  params : Param_pos.subst Param_pos.params;  (** The parameters of {!callee_type_at_call}. *)
  params_orig : Param_pos.orig Param_pos.params;  (** The parameters the callee declares. *)
  subst_index_of_orig : Param_pos.orig Param_pos.pos -> Param_pos.subst Param_pos.pos option;
      (** A declared parameter's position among {!params}, where it has one
          ({!Param_pos.subst_of_orig}). *)
}

(** [instantiate call ~reading ~at_call ~expand ~erased] -- [call] reading
    its variables as [reading]: [at_call tys] instantiates a type the
    callee declares at the reading's substitution, [expand] unfolds an
    alias for an arrow, and [erased] says of an instantiated parameter
    whether the instantiation erased it. *)
val instantiate :
  t ->
  reading:Call_tyargs.t ->
  at_call:(Mlutil.Var_types.t -> Miniml.ml_type -> Miniml.ml_type) ->
  expand:(Miniml.ml_type -> Miniml.ml_type) ->
  erased:(Miniml.ml_type -> bool) ->
  instantiated

(** Whether [a] and [b] instantiate one call alike: the same callee, its
    arguments in the same roles, the same readings -- each variable's type,
    its holes, and what each resolution was read from -- and the same
    instantiated callee type.  The argument nodes are not compared. *)
val same_instantiation : instantiated -> instantiated -> bool

(** [at_call inst call] -- [inst], planned for an application elsewhere
    built from the same Core, as the instantiation of [call]: its argument
    nodes [call]'s, its readings [inst]'s.  [Invalid_argument] unless both
    have one callee and one role per argument. *)
val at_call : instantiated -> t -> instantiated

(** A class field called as a static member of the instance it projects
    through, rather than through the field's dispatcher. *)
type static_projection = {
  instance : int;  (** The instance's position among the arguments the call writes. *)
  domains : Miniml.ml_type list;  (** The member's value parameters, at the call. *)
  missing : Miniml.ml_type list;
      (** The trailing ones of {!domains} the call gives no operand for, which a
          partial application closes over. *)
}

(** Whether two static projections project through the same argument, at the
    same parameters. *)
val same_static_projection : static_projection -> static_projection -> bool
