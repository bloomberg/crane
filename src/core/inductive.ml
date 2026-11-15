(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** [Core.Inductive]: Core inductive definitions -- their packets, how one
    is treated by the backend ([Core.Inductive.Kind]) and how it relates to
    an inductive already extracted ([Core.Inductive.Equivalence]). *)

include Grammar.Inductive
