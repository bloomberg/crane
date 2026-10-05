(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A right fold of a map, fused into one traversal.

    {v foldr step z (map f xs)  ~>  foldr (fun x acc => step (f x) acc) z xs v}

    One local rule.  [map] and [foldr] are recognised by their bodies, not
    their names -- the structural equations of a map and of a right fold over
    the same two-constructor datatype -- and the mapped list is the fold's
    argument directly, so nothing else can see it.  Fusion changes when [f]
    runs relative to [step], so both must be pure under the declared meanings
    ({!Ml_declared.pure}): a declared operation, possibly partly applied, or
    a lambda whose body is one.  The fold keeps its association and initial
    value, and [f] is applied once per element, as before; only the
    intermediate list is gone. *)

val structure : Miniml.ml_structure -> Miniml.ml_structure
