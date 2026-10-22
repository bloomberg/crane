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

(** The flags of [struc]'s functions, settled across calls: each
    function's, innermost first. *)
val summarize : Miniml.ml_structure -> (Names.GlobRef.t * bool list) list

(** Install a {!summarize}d program's flags for {!Escape} to consult. *)
val install : (Names.GlobRef.t * bool list) list -> unit

(** The installed flags of a global's parameters, innermost first: [None]
    for one {!summarize} did not settle. *)
val settled : Names.GlobRef.t -> bool list option
