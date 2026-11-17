
val add : int -> int -> int

val mul : int -> int -> int

module Nat :
 sig
  val sub : int -> int -> int

  val divmod : int -> int -> int -> int -> int * int

  val modulo : int -> int -> int
 end

val seq : int -> int -> int list

val hd : 'a1 -> 'a1 list -> 'a1

val tl : 'a1 list -> 'a1 list

val fold_left : ('a1 -> 'a2 -> 'a1) -> 'a2 list -> 'a1 -> 'a1

module GbInterp :
 sig
  val next : int -> int

  type expr =
  | Num of int
  | Var of int
  | Add of expr * expr
  | Mul of expr * expr
  | Let of expr * expr
  | If0 of expr * expr * expr

  val lookup : int list -> int -> int

  val eval : int list -> expr -> int

  val is_num : int -> expr -> bool

  val sadd : expr -> expr -> expr

  val smul : expr -> expr -> expr

  val simplify : expr -> expr

  type instr =
  | IPush of int
  | ILoad of int
  | IAdd
  | IMul
  | IBind
  | IUnbind

  val compile : expr -> instr list -> instr list

  val binop : (int -> int -> int) -> int list -> int list

  val run : int -> instr list -> int list -> int list -> int

  val gen : int -> int -> expr

  val round : int -> int -> int

  val interp : int -> int -> int
 end
