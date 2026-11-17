(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A list with at least one element.  The type is private: a value is read
    by pattern ([{head = x; tail = []}] is a singleton) but built only by
    this module's functions, so emptiness is ruled out where the value is
    made rather than checked where it is used. *)

type 'a t = private {head : 'a; tail : 'a list}

(** [singleton x] is the list [[x]]. *)
val singleton : 'a -> 'a t

(** [of_list_exn l] is [l] as a nonempty list; for a caller whose [l] is
    nonempty by construction.  Raises [Invalid_argument] when [l] is
    empty. *)
val of_list_exn : 'a list -> 'a t

(** [to_list l] is the elements of [l], in order. *)
val to_list : 'a t -> 'a list

(** [map f l] applies [f] to each element of [l], in order. *)
val map : ('a -> 'b) -> 'a t -> 'b t

(** [iter f l] applies [f] to each element of [l], in order. *)
val iter : ('a -> unit) -> 'a t -> unit

(** [exists p l] holds when [p] holds of some element of [l]. *)
val exists : ('a -> bool) -> 'a t -> bool

(** [for_all p l] holds when [p] holds of every element of [l]. *)
val for_all : ('a -> bool) -> 'a t -> bool
