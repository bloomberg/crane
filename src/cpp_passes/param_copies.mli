(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A copy of a by-value parameter that is the parameter's last use is the
    parameter itself.

    A loop made of a tail recursion keeps each parameter it varies in a
    variable of its own -- [uint64_t _loop_k = k; while (true) { ...
    _loop_k = k_; }] -- and so does the body of a loop helper inlined into
    its caller, where the parameter stands for the caller's own
    ([uint64_t _lc1_loop_k = n;]).  When nothing reads the parameter after
    the copy, the copy is dropped and the variable is the parameter: [while
    (true) { ... k = k_; }].

    The parameter must be passed by value -- the function's own copy, so
    that writing it is seen by no caller -- and declared at the copy's
    type, and no lambda of the function may name it: a lambda capturing it
    by reference would see the writes.  Nothing may read it after the copy,
    in the statements after the copy's or after any statement enclosing
    it; within a loop, anything the loop reads counts, as it runs again.
    A lambda's own by-value parameters are treated the same way in its
    body.

    A pass of {!Pipeline}, after {!Local_storage}. *)

val transform_decl : Cpp_ir.Lowered.Decl.t -> Cpp_ir.Lowered.Decl.t
