(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A function's constants as named locals.

    Translation marks a closed constructor term of a shared variant
    ({!Crane_rt.Constant}) where it builds one.  This pass, run once a
    declaration's bodies are final, declares each distinct constant of a
    function body once, at its top --
    [static const auto pos_10 = crane::immortal(Positive::xo(...));] -- and
    reads it by name where it was built.  A static local is built the first
    time control reaches it and kept: evaluated again, the term is a count
    bump rather than an allocation per node.  [crane::immortal] makes its
    blocks immortal, since it is read from every thread. *)

val decl : Minicpp.cpp_decl -> Minicpp.cpp_decl
