(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A coinductive's field projection -- [observe] on an interaction tree --
    hands out a reference into its receiver instead of a copy of the field.

    A method that returns a reference into [*this] dangles when the receiver
    is a temporary, [f(x).observe()], whose only owner dies at the end of the
    full expression.  So the projection becomes a pair of overloads on the
    receiver: [const T &m() const &] for an lvalue, which copies nothing, and
    [T m() const &&] for a temporary, which copies.  No call reaches the
    reference through a temporary.

    Input: a declaration whose struct methods are all {!Minicpp.Rq_any}.
    Output: the same declaration, with each projection of a coinductive split
    in two. *)

val transform_decl : Minicpp.cpp_decl -> Minicpp.cpp_decl
