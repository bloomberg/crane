(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Core match patterns ({!Grammar.Pattern}). *)

include Grammar.Pattern

(** [binding_all constructor n] is [constructor] binding its [n] arguments,
    in order, to the branch's binders: [Constructor {constructor; fields =
    [Bound_variable n; ...; Bound_variable 1]}], the pattern of every branch
    extraction makes. *)
let binding_all constructor n = Constructor {constructor; fields = List.init n (fun i -> Bound_variable (n - i))}

(** Whether [p] is [binding_all c n] for some constructor [c]. *)
let binds_all n = function
  | Constructor {fields; _} ->
    List.length fields = n && List.for_all2 (fun i p -> p = Bound_variable (n - i)) (List.init n Fun.id) fields
  | Tuple _ | Bound_variable _ | Wildcard -> false
