(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A global call as Core elaborates it, before anything about its C++ is
    decided (docs/Pipeline-Disentangling-Plan.md, section 3.4): its callee,
    the role each argument the call gives the callee has, and the call's
    reading of the callee's scheme variables.  It holds no C++ type and no
    template argument.

    Transitional.  It is elaborated while the call's enclosing body is
    translated ({!Translation_calls.elaborate_call}), from the lexical
    environment the arguments are generated in, and the C++ part of
    planning the call ({!Translation_calls.plan_call}) starts from it. *)

type t = private {
  callee : Names.GlobRef.t;
  callee_type : Miniml.ml_type;  (** As the callee is declared. *)
  primary : Miniml.ml_ast list;
      (** The arguments the callee takes, dictionaries among them, in
          source order.  One a declared erased domain drops is not among
          them. *)
  excess : Miniml.ml_ast list;
      (** The arguments past the callee's arity, applied to its result. *)
  instances : Miniml.ml_ast list;
      (** The dictionaries among {!primary}, in the order the callee numbers
          its dictionary parameters. *)
  erased_instances : int;
      (** How many dictionaries the call erased whose parameters the callee
          still declares. *)
  regular : Miniml.ml_ast list;  (** {!primary} less its dictionaries. *)
  tyargs : Call_tyargs.t;
      (** The callee's scheme variables as the call reads them, before they
          are spelled in the caller's scope. *)
}

val make :
  callee:Names.GlobRef.t ->
  callee_type:Miniml.ml_type ->
  primary:Miniml.ml_ast list ->
  excess:Miniml.ml_ast list ->
  instances:Miniml.ml_ast list ->
  erased_instances:int ->
  regular:Miniml.ml_ast list ->
  tyargs:Call_tyargs.t ->
  t

(** How many of the callee's declared parameters the dictionaries occupy,
    erased ones included: a regular argument's declared position starts
    after them. *)
val leading_params : t -> int

(** Whether a dictionary stated a scheme variable the call had erased
    ({!Call_tyargs.Argument_heads}): the arguments at it are then built at
    that type, so the call has to write it. *)
val dictionary_filled : t -> bool
