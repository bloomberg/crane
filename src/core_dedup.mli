(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A definition whose body is another's, written once.

    Rocq gives an inductive both [_rect] and [_rec], and extraction makes the
    two the same recursive function; any two definitions of one module can
    coincide the same way.  A later function definition (a fixpoint, or a
    term that is a lambda) whose body is an earlier one's in the same module
    -- up to the names of its binders and its own name in its recursive
    calls -- and whose type and precondition checks are the same, becomes a
    forwarder to the earlier: it keeps its name and signature, and its body
    is the call.  This compares bodies, not behaviour: two algorithms for one
    function stay two.  Mapped definitions and projections are left alone.

    One of the Core passes run before the program is frozen ([core_passes]
    in [extract_env.ml], under {!Core_phase.optimize}): after
    [Modutil.optimize_struct], just before {!Core_specialize}. *)

(** Every module of the structure with its coinciding definitions made
    forwarders. *)
val structure : Core.Program.t -> Core.Program.t
