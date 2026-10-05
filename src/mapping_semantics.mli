(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** What a mapped Rocq type or operation means in C++, declared beside its
    mapping with [Crane Semantics], for the passes that compute with it or
    reason about it -- bounded evaluation, the reduction rewrite, local cell
    scalarization.

    A mapping's replacement text says how to spell an operation, not what it
    does: [(%a0 + %a1)] wraps at 64 bits only because of the type the
    arguments have, and nothing in it says so.  So meaning is declared, from a
    small fixed vocabulary, and a mapping without a declaration is opaque to
    every pass that asks, whatever its text looks like. *)

(** The bit width of an unsigned integer. *)
type width = W8 | W16 | W32 | W64

(** An operation on unsigned integers of one width, with the arithmetic of
    that width: sums and products wrap. *)
type unsigned_op =
  | Add
  | Mul
  | Sub_truncated  (** [a - b], or [0] when [b > a]: Rocq's [nat] subtraction *)
  | Div  (** [a / b], or [0] when [b = 0] *)
  | Mod  (** [a mod b], or [a] when [b = 0] *)
  | Eqb  (** to [bool] *)
  | Ltb  (** to [bool] *)
  | Leb  (** to [bool] *)
  | Max
  | Min

type t =
  | Unsigned_nat of width
      (** An inductive [O | S n] stored as an unsigned integer of [width]
          bits: [O] is [0] and [S] adds one, wrapping. *)
  | Unsigned of unsigned_op * width
  | Ref_new of int
      (** a fresh mutable cell holding the argument at this position *)
  | Ref_read of int  (** the value the cell at this position holds *)
  | Ref_write of int * int
      (** store the second position's value in the first position's cell *)
  | Vec_new  (** a fresh, empty growable array *)
  | Vec_push of int * int
      (** append the second position's value to the first position's array *)
  | Vec_reserve of int * int
      (** make room in the first position's array for as many more elements
          as the second position's unsigned count, if it can; the contents
          are unchanged *)
(** A position counts every argument the mapping's template can splice, as
    its [%aN] holes do -- an implicit argument included. *)

(** The meaning declared for [r], if any. *)
val find : Names.GlobRef.t -> t option

(** The one mapping declared with a meaning [p] accepts, if there is exactly
    one: for a pass that must spell an operation the program does not call. *)
val unique_declaration : (t -> bool) -> Names.GlobRef.t option

(** [Crane Semantics r := "words"]: parse [words] -- ["unsigned_nat 64"],
    ["unsigned add 64"], ["ref write 1 2"], ["vector push 0 1"] -- check it
    fits what [r] is, and record it. *)
val declare : Libnames.qualid -> string -> unit

(** The width the inductive is declared an unsigned integer at
    ({!Unsigned_nat}). *)
val nat_width : Names.inductive -> width option

(** [2^width - 1], the largest value of the width. *)
val max_value : width -> Z.t
