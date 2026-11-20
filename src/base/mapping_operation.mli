(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Compiled operation mappings (design 11, 21.4; plan M4): what the
    pipeline reads of an [OperationMapping (Ref source)] instance.

    A plan is compiled once per operation, from the instance that maps the
    operation applied to one fresh variable per binder of its type.  The
    binders are classified as Crane's erasure classifies them
    ({!Mapping_discovery.operation_binders}): type parameters, retained
    runtime arguments, and erased binders (proofs, type-class instances,
    [Crane Extraction Implicit] positions).  The contract's [ArgumentSpec]s
    are bound to the retained runtime binders one to one, in source order
    (validation rule 19.6.2, checked when the mapping is resolved).

    The template is compiled into the legacy term-template vocabulary of
    {!Cpp_ir.Foreign_template}, so that a call is lowered by the existing
    inline-call path: [%arg(x)] becomes the [%aN] of the binder [x] is bound
    to (N counts the retained runtime binders), [%stored(c)] the [%tN] of the
    type parameter component [c] is stored at, and a [WithBody] the block
    template [%result = init; body].  [%stored(c)] is resolved against the
    mapped types of the arguments, in source order, and then of the result
    (looking inside the result type, so that a monadic result is searched
    too): the first mapped type declaring a component [c] decides, and that
    component's type argument there must be one of the operation's type
    parameters.

    A call evaluates every retained argument once, in source order, before
    the template is expanded ({!Cpp_passes.Shared_args}). *)

open Mapping_descriptor

type purity = Pure | Effectful | Opaque

type argument = {
  name : string;
  use : input_use;
  position : int;  (** among the retained runtime binders: its [%aN] *)
  binder : int;  (** among all the binders of the operation's type *)
  in_place : bool;
      (** the template receives it as a mutable lvalue: a [Replace] of a
          mapped type, or a write of one whose write-through form is [T&]
          ({!Mapping_plan.write_through}) *)
}

type t = {
  instance : Names.GlobRef.t;
  source : Names.GlobRef.t;
  template : string;  (** in the legacy term-template vocabulary *)
  arguments : argument list;  (** one per retained runtime binder, in order *)
  binder_count : int;  (** every binder of the operation's type *)
  call_binders : int list;
      (** those a call passes in Core: the retained runtime binders and the
          type-class instances (type parameters become type variables,
          proofs and [Extraction Implicit] positions are dropped) *)
  result : result_spec;
  facts : operation_fact list;
  purity : purity;
  headers : string list;
}

(** Whether an [OperationMapping] instance names [g]. *)
val is_operation_head : Names.GlobRef.t -> bool

(** The plan of the operation [g]; a user error when no instance applies to
    every instantiation of its parameters, or the template uses what this
    stage does not compile. *)
val find : Names.GlobRef.t -> t

(** The number of retained runtime arguments a call supplies. *)
val arity : t -> int

(** Whether the operation keeps argument [a] (design 12.3): [Take],
    [OpaqueUse], or named by a [RetainsArgument] fact.  [Read],
    [ReadCanonical], [Write], [WriteCanonical], [Replace] and [Ignore] only
    borrow it for the call. *)
val owns : t -> argument -> bool

(** One flag per argument of a call in Core ([call_binders]), in order:
    whether the operation owns the argument passed there ({!owns}); a
    type-class instance is not owned. *)
val owned_call_arguments : t -> bool list

(** The headers of the operation [g], if it is mapped. *)
val headers : Names.GlobRef.t -> string list

(** One entry per argument of a call in Core ([call_binders]), in order:
    the use the contract declares for the argument passed there, [None]
    for a type-class instance. *)
val call_argument_uses : t -> input_use option list

(** The positions ([%aN]) of the arguments the template receives as
    mutable lvalues ([in_place]). *)
val in_place_positions : t -> int list
