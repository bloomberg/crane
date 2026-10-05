(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A definition whose body is another's, written once.

    Rocq gives an inductive both [_rect] and [_rec], and extraction makes the
    two the same recursive function; any two definitions of one module can
    coincide the same way.  A later fixpoint whose body is an earlier one's --
    up to the names of its binders and its own name in its recursive calls --
    and whose type is the same, becomes a forwarder to the earlier: it keeps
    its name and signature, and its body is the call.  This compares bodies,
    not behaviour: two algorithms for one function stay two. *)

val structure : Miniml.ml_structure -> Miniml.ml_structure
