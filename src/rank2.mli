(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Rank-2 arguments, spelled as polymorphic function objects.

    A lambda standing for a rank-2 argument -- [fun _ e => ...] at a parameter
    of type [forall X, E X -> M X] -- is handed a type the caller has not
    chosen yet.  Extraction leaves that type as {!Miniml.Tunknown}, which
    prints as [std::any], and a lambda written against [std::any] is a claim
    the body cannot keep: it would have to name a concrete result where only
    the caller knows one.

    The honest spelling is a polymorphic function object: the erased positions
    become the lambda's own template parameter -- the {e carrier} -- so the
    parameter reads [const E<_X> &] and the body says [_X] where it would
    otherwise guess.  The callee recovers the result with
    [std::invoke_result_t]; see {!Gen_decls.relax_tt_applied_return}.

    The carrier's extent is the lambda's body, and is carried by
    {!Translation_state.with_rank2_carrier}: every erased type inside denotes
    that one parameter, so a producer with nothing else to say about a type
    argument says the carrier rather than [std::any]. *)

(** The name a carrier goes by.  There is one per lambda and lambdas do not
    nest polymorphically, so the name need not be fresh. *)
val carrier_name : Names.Id.t

(** [carrier_type x] is the carrier as a type: a type variable with no index,
    since it numbers against no declaration's parameter list. *)
val carrier_type : Names.Id.t -> Minicpp.cpp_type

(** Whether an argument's ML type quantifies a type extraction erased -- the
    mark of a rank-2 (or higher) argument. *)
val quantifies_erased_type : Miniml.ml_type -> bool

(** [at_carrier x ty] is [ty] with every erased position read as the carrier:
    inside a polymorphic function object that is what those positions denote. *)
val at_carrier : Names.Id.t -> Minicpp.cpp_type -> Minicpp.cpp_type

(** Whether a type is {e nothing but} an erased position, modulo [const] and
    [&].  Such a parameter is a box being passed through: naming it [_X]
    deduces [std::any] and says less than [std::any] did, so the carrier is
    only worth naming inside a type. *)
val is_bare_box : Minicpp.cpp_type -> bool

(** [type_args_at_carrier x r] is the type-argument list an inductive (or one
    of its constructors) takes, every argument read as the carrier -- what to
    say when the ML annotation was erased down to nothing.  [None] when [r]
    takes no type parameters, so a caller keeps whatever it had. *)
val type_args_at_carrier :
  Names.Id.t -> Names.GlobRef.t -> Minicpp.cpp_type list option
