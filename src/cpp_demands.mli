(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The headers a finished declaration needs for what it writes down
    (docs/Pipeline-Disentangling-Plan.md, Milestone 9): read off the
    declaration, rather than raised by the pass that happened to build each
    construct.  A generator or a lowering pass builds a [crane::small_vector]
    or an acquire fence and says nothing about headers; the driver demands
    them for every declaration it finishes ({!Finished_program.finish}).

    Transitional.  Only the constructs below are read here; the printer still
    raises the rest of a file's demands as it writes them. *)

(** The text of the acquire fence a destructor's drain issues before it
    takes a node it owns alone, which needs [<atomic>]. *)
val acquire_fence : string

(** [demand d] raises the headers [d]'s types and statements need: the
    runtime's [crane::small_vector] and [crane::field], the standard
    [optional], and the acquire fence. *)
val demand : Minicpp.cpp_decl -> unit
