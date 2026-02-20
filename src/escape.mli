(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(*s Escape analysis for MiniML AST.

    Determines which MLletin bindings are safe for unique_ptr
    instead of shared_ptr. A binding is safe when:
    1. Its type is a non-enum, non-coinductive inductive
    2. It is not Dummy
    3. It occurs at most once in its continuation (max-over-branches)
    4. It does not escape (stored in constructor, captured by lambda,
       returned from function, passed to function call, captured by fix) *)

open Miniml

(** [analyze body] returns the list of MLletin depth indices (0-based)
    in [body] whose bindings are safe for unique_ptr. *)
val analyze : ml_ast -> int list
