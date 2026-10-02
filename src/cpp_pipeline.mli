(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The passes a MiniCpp declaration goes through between translation and the
    printer.

    Loopification, depth flattening and the {!Cpp_erasure} seam have to run in
    that order, and every one of them has to run: a declaration that skipped
    flattening crashes the C++ parser, and one that skipped the seam is not a
    {!Cpp_erasure.settled} declaration at all.  So the sequence is a single
    function rather than a sequence its callers spell out -- there are no
    intermediate declarations to hand to the wrong pass, because none of them
    is nameable from outside. *)

(** [should_loopify decl] -- whether [decl] is loopified, given what the user
    asked for and what kind of declaration it is. *)
val should_loopify : Minicpp.cpp_decl -> bool

(** [finish decl] runs every pass between translation and printing --
    loopifying where {!should_loopify} says so -- and hands back the printable
    declaration.  Under [CRANE_TRACE_PASSES] ([1], or a substring of the
    declaration's name) it reports which passes changed [decl] and its node
    count before and after each. *)
val finish : Minicpp.cpp_decl -> Cpp_erasure.settled

(** [finish_group decls] finishes declarations that may call one another:
    every function among them is known to loopification before any is
    transformed, so a mutual partner can be inlined whichever comes first. *)
val finish_group : Minicpp.cpp_decl list -> Cpp_erasure.settled list
