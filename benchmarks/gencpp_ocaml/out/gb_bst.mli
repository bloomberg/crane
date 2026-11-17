
val length : 'a1 list -> int

val add : int -> int -> int

val mul : int -> int -> int

module Nat :
 sig
  val sub : int -> int -> int

  val divmod : int -> int -> int -> int -> int * int

  val modulo : int -> int -> int
 end

val seq : int -> int -> int list

val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1

module GbBst :
 sig
  val next : int -> int

  val randoms : int -> int -> int list

  type tree =
  | Leaf
  | Node of tree * int * tree

  val insert : int -> tree -> tree

  val tsum : tree -> int

  val tmap : (int -> int) -> tree -> tree

  val to_list : tree -> int list -> int list

  val bst : int -> int -> int
 end
