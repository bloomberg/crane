(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The three numberings a call to a polymorphic global moves between, as
    distinct types (docs/Type-Argument-Numbering-Refactor-Plan.md, section 1).

    - A {!Binder.t} is a binder of the callee's Rocq product spine, the place
      an argument of the application stands at.
    - A {!Var.t} is a variable of the callee's MiniML type scheme, owned by
      the scheme ({!Id.t}) it belongs to.
    - A template parameter of the C++ declaration is the third, and lives
      with the callable's ABI plan.

    None of them is an [int] to its clients, so an index of one cannot be
    used as an index of another; every crossing is a named function, the way
    {!Param_pos} separates a callee's parameter lists.  The module depends on
    nothing of the IR, so that {!Miniml} can name an instantiation. *)

(** The identity of one type scheme: the declaration it belongs to and how
    many variables it quantifies. *)
module Id : sig
  type t

  (** A scheme for [owner] quantifying [arity] variables, distinct from every
      other scheme minted in this run. *)
  val fresh : Names.GlobRef.t -> arity:int -> t

  val owner : t -> Names.GlobRef.t
  val arity : t -> int
  val equal : t -> t -> bool
  val pp : t -> Pp.t
end

(** A variable of one scheme. *)
module Var : sig
  type t

  val owner : t -> Id.t

  (** The variable's place in its scheme, from [1]: the body spells it
      [Tvar (_, ordinal v)]. *)
  val ordinal : t -> int

  (** The scheme's variable the body spells [Tvar (_, i)]; [None] out of
      range.  The one crossing from the body's numbering. *)
  val of_tvar : Id.t -> int -> t option

  (** Every variable of the scheme, in ordinal order. *)
  val all : Id.t -> t list

  val equal : t -> t -> bool
  val compare : t -> t -> int

  (** What [l] pairs with the variable, if anything. *)
  val assoc_opt : t -> (t * 'a) list -> 'a option

  val pp : t -> Pp.t
end

(** A binder of a declaration's Rocq product spine. *)
module Binder : sig
  type t

  (** The binder at [position], from [0], among the declaration's leading
      products in source order -- value, proof and type binders alike. *)
  val of_position : int -> t

  val position : t -> int
  val equal : t -> t -> bool
  val pp : t -> Pp.t
end

(** Identities of inference holes ({!Miniml.Thole}). *)
module Hole : sig
  (** A hole distinct from every other minted in this process. *)
  val fresh : unit -> int
end

(** What a use solved a scheme variable to.  [Identity] is a rigid self-call
    inside the declaration's own fixpoint: the variable stands for itself. *)
type 'ty solution =
  | Identity
  | Type of 'ty

(** What the source application said about a variable: nothing, or the
    argument written at the binder the variable comes from -- [observed] is
    [None] where that argument had no type extraction could read. *)
type 'ty source_evidence =
  | Not_written
  | Written of {
      binder : Binder.t;
      observed : 'ty option;
    }

type 'ty slot = {
  solution : 'ty solution;
  source : 'ty source_evidence;
}

(** One slot per variable of a scheme, indexed by {!Var.t}. *)
module Instantiation : sig
  type 'ty t

  (** [make id f] has the slot [f v] for every variable [v] of [id]. *)
  val make : Id.t -> (Var.t -> 'ty slot) -> 'ty t

  val scheme : 'ty t -> Id.t

  (** The slot of [v]; [Invalid_argument] for a variable of another scheme,
      which is a caller confusing two schemes, never a missing entry. *)
  val slot : 'ty t -> Var.t -> 'ty slot

  val map : ('a -> 'b) -> 'a t -> 'b t
  val map_slots : (Var.t -> 'a slot -> 'b slot) -> 'a t -> 'b t
  val fold : (Var.t -> 'ty slot -> 'acc -> 'acc) -> 'ty t -> 'acc -> 'acc
  val for_all : (Var.t -> 'ty slot -> bool) -> 'ty t -> bool
  val exists : (Var.t -> 'ty slot -> bool) -> 'ty t -> bool
end
