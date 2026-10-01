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
    definitions.  A member that names no sibling stays where it was.

    Each declaration carries a payload -- the environment it is rendered in --
    and a hoisted definition inherits the payload of the struct it came out
    of. *)
val split_group : ('a * Minicpp.cpp_decl) list -> ('a * Minicpp.cpp_decl) list

(** [split_named ~names decls] is the same surgery for a cycle that is not
    between siblings: every member naming a global that satisfies [names] is
    left as a declaration and its definition written after all the structs.

    [body_only] asks the question of the member's body alone, which is what a
    caller wants when the obstacle is a name that appears later in the file
    rather than a type that is incomplete: out-lining moves the body and
    leaves the signature where it was, so a signature naming the obstacle is
    not helped by moving anything.
    Returns the structs and the hoisted definitions separately, because where
    those definitions go is the caller's question: after the group is enough
    for a cycle between siblings, and not enough for one with a struct emitted
    later in the file. *)
val split_named :
  ?body_only:bool ->
  names:(Names.GlobRef.t -> bool) ->
  ('a * Minicpp.cpp_decl) list ->
  ('a * Minicpp.cpp_decl) list * ('a * Minicpp.cpp_decl) list
