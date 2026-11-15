(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Core terms ({!Grammar.Expr}). *)

include Grammar.Expr

(** A read of the [i]th enclosing binder, for a term built rather than
    copied. *)
let fresh_rel i = Bound_variable {index = i; occurrence = Occurrence.fresh ()}
