
val negb : bool -> bool

val app : 'a1 list -> 'a1 list -> 'a1 list

val add : int -> int -> int

val mul : int -> int -> int

module Nat :
 sig
  val sub : int -> int -> int

  val divmod : int -> int -> int -> int -> int * int

  val modulo : int -> int -> int
 end

val map : ('a1 -> 'a2) -> 'a1 list -> 'a2 list

val seq : int -> int -> int list

val rev : 'a1 list -> 'a1 list

val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1

val fold_right : ('a2 -> 'a1 -> 'a1) -> 'a1 -> 'a2 list -> 'a1

val filter : ('a1 -> bool) -> 'a1 list -> 'a1 list

module GbLists :
 sig
  val next : int -> int

  val randoms : int -> int -> int list

  val merge : int list -> int list -> int list

  val split : int list -> int list * int list

  val msort : int -> int list -> int list

  val checksum : int list -> int -> int

  val lists : int -> int -> int
 end
