(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** How the frames of a machine with a stack hold the parameters of its
    loops, decided over its ControlIR (docs/Pipeline-Disentangling-Plan.md,
    section 4.10: [Storage.Frame]).

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

(** [own], for each parameter of the loop, whether its frames hold it by
    pointer; [entered], for each parameter of a loop an entry enters, by the
    Core level it is bound at under the loop's parameters, the same. *)
type t = {
  own : bool list;
  entered : (int * bool) list;
}

(** A parameter of the loop, by its position, or of a loop an entry enters,
    by the Core level it is bound at. *)
type parameter =
  | Own of int
  | Entered of int

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
