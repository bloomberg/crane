(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** MiniCpp read through declared meanings ({!Mapping_semantics}): the
    counterpart of {!Ml_declared} for the passes over C++. *)

(** The declared meaning of the mapping [e] applies, and its arguments by
    template position; a mapped constant standing alone has none. *)
val applied : Minicpp.cpp_expr -> (Mapping_semantics.t * Minicpp.cpp_expr list) option
