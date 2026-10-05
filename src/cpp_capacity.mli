(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Capacity for a vector reserved from the count of the loop that fills it.

    A fresh, empty vector ({!Mapping_semantics.Vec_new}) whose first use is a
    count-controlled loop -- one over an unsigned [nat] counter, leaving at
    zero and otherwise stepping it down by one -- that appends to the vector
    exactly once per iteration, unconditionally, and touches it no other way,
    ends with exactly as many elements as the counter holds when the loop
    starts.  A reserve of that count ({!Mapping_semantics.Vec_reserve}) goes
    in front of the loop: one allocation instead of a geometric series of
    them, and no element moved by growth.

    The count is the loop's own, read where the loop starts, never an
    estimate.  Any other use of the vector in the loop, an early exit, a
    second append or one under a condition, and the loop is left as it is. *)

val transform_decl : Minicpp.cpp_decl -> Minicpp.cpp_decl
