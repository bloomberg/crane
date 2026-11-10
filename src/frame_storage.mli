(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** How the frames of a machine with a stack hold the parameters of its
    loops, decided over its ControlIR: for each parameter, the storage the
    value a frame holds for it lies in ({!Ownership_ir.Storage}).  Loopify
    and {!Control_to_legacy_minicpp} read the plan when they lay out the
    frames of a machine with a stack.

    A machine runs on what its caller passed, which outlives it and which
    nothing changes while it runs.  A frame can hold a parameter by pointer
    wherever every value passed for it lies in that storage: a parameter
    held so, a field a match binds by reference into such a value, or a cell
    a field stored behind the pointer of anything derived from that storage
    points at -- its handle copied into a let or a frame still points there.
    A let's copy of a value, a frame's copy of one, a call's result or a
    construction is a value of its own, which a frame holding a pointer to
    it would outlive.  Holding parameters so is the greatest fixed point:
    each parameter of the loop and of the loops its entries enter is held by
    pointer until a turn passes it a value that lies elsewhere, given those
    still held so. *)

(** [own], for each parameter of the loop, where the value its frames hold
    is stored: [Local], where the machine's caller keeps it, a frame holding
    a pointer to it, or [Frame], in the frame itself; [entered], for each
    parameter of a loop an entry enters, by the Core level it is bound at
    under the loop's parameters, the same. *)
type t = {
  own : Ownership_ir.Storage.t list;
  entered : (int * Ownership_ir.Storage.t) list;
}

(** A parameter of the loop, by its position, or of a loop an entry enters:
    the loop, the parameter's position there, and the Core level it is
    bound at under the machine's loop's parameters. *)
type parameter =
  | Own of int
  | Entered of {
      loop : Control_ir.Term.loop;
      index : int;
      level : int;
    }

(** Whether the program holds a value of the Core type [ty] as a value -- an
    inductive neither coinductive, custom, nor an enum, which is passed by
    value however it is lent -- so that a pointer may stand for one
    ({!Loopify_analysis.is_value_type_ret}); with [~abbreviations], an
    abbreviation as what it abbreviates ([Definition t := list (key * elt)]).
    An abstract type -- a functor parameter's [X.t] -- is no value inductive
    the program knows. *)
val value_inductive : abbreviations:bool -> Miniml.ml_type -> bool

(** Whether a frame can hold by pointer a parameter of Core type [ty] that
    its callable passes as [passing] says: lent by const reference, or under
    Reuse with NonAtomicRc owned by value -- either lives for the call, and
    nothing moves out of it -- at a value inductive, named as itself or
    through an abbreviation ({!Translation_support.wrap_param_by_ownership}
    declares either by reference).  A parameter of no runtime value
    ([None]) is held by none. *)
val passed_holdable : Callable_abi.passing option -> Miniml.ml_type -> bool

(** Whether a frame can hold the parameter at position [i] of the loop [l]
    by pointer, as the plan of the local fixpoint's function [l] is made
    from passes it ({!Ownership_ir.Local_passing}, {!passed_holdable});
    [None] where [l] is a function's loop, or no plan says. *)
val local_holdable : Control_ir.Term.loop -> int -> bool option

(** [check_local i ~planned ~declared]: under [CRANE_CHECK_IR], where the
    plan of a local fixpoint has a frame hold the parameter at [i] of its
    loop by pointer ([planned]), the C++ type its lambda declares it at must
    be one a pointer spells ([declared ()]).  The converse does not hold:
    under Reuse with NonAtomicRc the declared type takes any value it does
    not recognise as boxed -- an enum, an alias of an erased type -- for a
    value inductive, which the plan does not hold by pointer (as
    {!Control_to_legacy_minicpp}'s machines of functions). *)
val check_local : int -> planned:bool -> declared:(unit -> bool) -> unit

(** [plan ~pointer_fields ~in_place ~holdable l]: how the frames of the
    machine of [l] hold its parameters; [pointer_fields c] are the declared
    arguments of the constructor [c] stored behind the pointer, and an
    in-place coercion ([in_place from into]) changes nothing about where a
    value lies.  A parameter [holdable] rejects is represented so that no
    frame can hold it by pointer: it is held by value, and what derives from
    it lies in the frame. *)
val plan :
  pointer_fields:(Names.GlobRef.t -> int list option) ->
  in_place:(Miniml.ml_type -> Miniml.ml_type -> bool) ->
  holdable:(parameter -> bool) ->
  Control_ir.Term.loop ->
  t
