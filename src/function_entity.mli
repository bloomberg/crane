(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A function definition finalized once, and the two views of it a file
    writes: its declaration and its definition.

    The body decides which callback constraints the signature may state (see
    {!Minicpp.drop_stored_callback_constraints}), and a declaration is written
    without the body, so the decision is taken when the entity is finalized
    and written into both views.  Deriving them from one value is what makes
    them state one template head: a declaration and a definition that differ
    in a constraint are two different functions. *)

type t

(** [finalize d] is the entity [d] defines, or [None] when [d] defines no
    function -- a declaration already, a value, a struct. *)
val finalize : Minicpp.cpp_decl -> t option

val declaration : t -> Minicpp.cpp_decl
val definition : t -> Minicpp.cpp_decl

(** [d]'s declaration where [d] defines a function, and [d] itself
    otherwise.  Sound only where the definition is not also emitted, or is
    emitted from the same entity. *)
val declaration_of : Minicpp.cpp_decl -> Minicpp.cpp_decl
