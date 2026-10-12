(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Which parameters of each function are owned and which borrowed, settled
    across calls.

    {!Escape.infer_owned_params} decides one function at a time, and reads a
    parameter handed to a callee as merely read.  But when the callee owns
    that parameter -- stores it, captures it, returns it -- a borrowed
    argument is copied at the call, where an owned one would have been
    moved: a retain, and a release when the callee is done with its copy.
    So a parameter passed directly to an owned parameter is owned too, and
    since owning one parameter can make a caller own its own, the flags are
    the least fixed point over every function of the structure, starting
    from every parameter borrowed. *)

(** Settle the flags of [struc]'s functions, for {!Escape} to consult, and
    which of their callable parameters each generalises, for
    {!generalises_callable}. *)
val settle : Miniml.ml_structure -> unit

(** Whether the function [r] takes its callable parameter at the declared
    position [pos], of C++ type [f], as a deduced [F &&] rather than a
    [crane::fn] -- {!Translation.generalises_callable}, with which callables
    [r]'s body holds on to settled before any of it is generated, so that a
    call site can write an argument the way the callee will take it.  [primary]
    is the callee's signature's deducible type variables.  [false] for a
    function [settle] did not see. *)
val generalises_callable :
  Names.GlobRef.t -> Param_pos.orig Param_pos.pos -> primary:Escape.IntSet.t -> Minicpp.cpp_type -> bool
