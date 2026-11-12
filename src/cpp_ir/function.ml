(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Function declarations and definitions ({!Grammar.Function}). *)

include Grammar.Function

(** The entries of a qualified name, outermost first. *)
let path_entries (p : 'p path) = p.outer :: p.inner
