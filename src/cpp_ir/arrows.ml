(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** How a callable takes its arguments ({!Grammar.Arrows}): its groups of
    parameters, one C++ call each, and its result.  A [Function] chain of
    {!Type.t} and an [Arrows.t] say the same thing; this module converts
    between them and compares callables up to grouping. *)

include Grammar.Arrows

(** [of_type t] is the grouping the function type [t] spells, one group per
    [Function] link of its chain, or [None] where [t] is not a function
    type. *)
let of_type : type p. p Type.t -> p t option = function
  | Function (dom, cod) ->
    let rec chain (t : p Type.t) groups =
      match t with
      | Function (d, c) -> chain c (d :: groups)
      | result -> {groups = List.rev groups; result}
    in
    Some (chain cod [dom])
  | _ -> None

(** [to_type a] is the function type spelling the grouping [a]. *)
let to_type (a : 'p t) : 'p Type.t = List.fold_right (fun dom cod -> Type.Function (dom, cod)) a.groups a.result

(** The number of arguments [a] takes before its result, over all groups. *)
let arity (a : 'p t) = List.fold_left (fun n g -> n + List.length g) 0 a.groups

(** [a] as one curried chain, its leaves curried too: the form two
    groupings of the same callable share. *)
let curried (a : 'p t) =
  let leaf t = Types.spell_arrows Through_tvar t in
  (List.map leaf (List.concat a.groups), leaf a.result)

(** Whether [a] and [b] are one callable grouped the same way or not: the
    same parameters and result once every group and every arrow inside a
    leaf is curried.  Aliases are compared as written; a caller that may
    meet one unfolds it first. *)
let same_function a b = curried a = curried b

(** Whether [a] and [b] are grouped alike: equal as written. *)
let equal (a : 'p t) (b : 'p t) = a = b
