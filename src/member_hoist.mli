(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Writing a cycle of structs in an order C++ accepts.

    A mutually recursive group of inductives reaches through its siblings by
    value -- a [list] of the other type, or the other type itself -- and then
    no order in which each struct is written whole satisfies all of them:
    whichever comes first names a type that is still only forward-declared.
    Laying out every struct in the group first and writing the members that
    cross the cycle afterwards is the order that exists. *)

(** [split_group decls] is the group's structs, each with the members that
    name a sibling left as declarations, followed by those members'
    definitions.  A member that names no sibling stays where it was. *)
val split_group : Minicpp.cpp_decl list -> Minicpp.cpp_decl list
