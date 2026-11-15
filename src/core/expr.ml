(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Core terms ({!Grammar.Expr}). *)

include Grammar.Expr

(** A read of the [i]th enclosing binder, for a term built rather than
    copied. *)
let fresh_rel i = Bound_variable {index = i; occurrence = Occurrence.fresh ()}

(** [e] under every crossing around it: the value inside its outermost
    [Coerce], [Boxed_value] and [Lambda_group_barrier] nodes, for a reader
    that looks through all three alike. *)
let rec strip_crossings = function
  | Coerce {value; _} | Boxed_value {value; _} | Lambda_group_barrier {value; _} -> strip_crossings value
  | e -> e
