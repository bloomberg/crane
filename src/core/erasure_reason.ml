(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** [Core.Erasure_reason]: why extraction erased an argument or subterm (a
    type argument, a proof, or a user-configured implicit), as carried by
    [Core.Type.Erased] and [Core.Expr.Erased_value]. *)

include Grammar.Erasure_reason
