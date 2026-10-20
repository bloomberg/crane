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

    Which methods are projections is not read off their C++ bodies: it was
    decided from the Core function each method is made of, and recorded on
    its receiver ({!Escape.returns_receiver_field}).  Under [CRANE_CHECK_IR]
    the body is checked to agree.

    The split is made where the method is generated, so every pass after
    that sees the overloads the struct declares. *)

(** [lend ~coinductive field] is the struct field [field] as declared: a
    projection of a coinductive, still {!Minicpp.Rq_any}, as its two
    overloads; any other field as it is. *)
val lend :
  coinductive:bool ->
  Minicpp.cpp_field * Minicpp.cpp_visibility * Minicpp.section_tag ->
  (Minicpp.cpp_field * Minicpp.cpp_visibility * Minicpp.section_tag) list

(** [check_decl d] -- a {!Probe.violation} for each projection of a
    coinductive [d] declares unsplit. *)
val check_decl : Minicpp.cpp_decl -> unit
