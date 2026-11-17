
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

val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1

module GbClo :
 sig
  val compose : (int -> int) -> (int -> int) -> int -> int

  val build : int -> (int -> int) list

  val closures : int -> int -> int
 end
