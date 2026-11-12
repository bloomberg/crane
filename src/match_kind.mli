(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** How a match is lowered, decided from Core alone: the match's annotated
    type and its branches.  Every pass asking how a match comes out reads it
    from here -- the ownership plan, the recursion plan, the representation
    plan -- and lowering reads the kind the elaboration walk recorded for
    the match's occurrence ({!Core_elaborate.match_kind}). *)

(** How a record projection applies the field it reads: returned as it is,
    called, or called through a coercion around the field. *)
type application =
  | Read
  | Call
  | Coerced_call

(** What the one branch of a match on a record or class does with it:
    project one field, [field] counting the branch's binders from the
    first, or bind its fields and run any other body. *)
type record_body =
  | Projection of {field : int; application : application}
  | Destructure

type t =
  | Custom  (** The inductive's match is mapped to custom code. *)
  | Record of {typeclass : bool; body : record_body}
      (** One branch over a record, or over a class's dictionary
          ([typeclass]). *)
  | Variant  (** Any other match. *)

(** [classify ty branches] -- the kind of a match annotated [ty] with
    [branches]. *)
val classify : Miniml.ml_type -> Miniml.ml_branch array -> t

(** Whether the match takes a record apart rather than branching. *)
val is_record : t -> bool

(** Whether the match's branches are where its value is bound, generated in
    place rather than in a closure: a custom match's or a record's. *)
val bound_in_place : t -> bool
