(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The headers a finished declaration needs for what it writes down
    (docs/Pipeline-Disentangling-Plan.md, Milestone 9): read off the
    declaration, rather than raised by the pass that happened to build each
    construct.  A generator or a lowering pass builds a [crane::small_vector]
    or an acquire fence and says nothing about headers; the finished program
    holds what its declarations need ({!Finished_program.demands}), and the
    driver demands that.

    Transitional.  Only the constructs below are read here; the printer still
    raises the rest of a file's demands as it writes them. *)

(** The text of the acquire fence a destructor's drain issues before it
    takes a node it owns alone, which needs [<atomic>]. *)
val acquire_fence : string

(** [of_decl d] is the headers [d]'s types, expressions and statements
    need: the runtime's [crane::small_vector], [crane::field] and [ITree],
    the standard [optional], the acquire fence, a pointer read at another
    instantiation of its pointee, and [crane::obj] where [d] may build one --
    a conversion at a type parameter, an axiom's erased type. *)
val of_decl : Minicpp.cpp_decl -> Table.header list
