(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The fields each generated constructor struct stores behind the smart
    pointer, as planned before rendering ({!Emit.Files.plan_pointer_fields}) and
    accumulated over the units of an extraction (the [pointer_fields] of
    {!Driver.Accumulated_plan.t}); a unit's stages read them off its context
    ({!Unit_plan.Context.t.pointer_fields}). *)

(** A constructor field stored behind the smart pointer: a recursive one,
    which holds the inductive itself, or one [Crane BoxedFields] boxed for
    holding some other inductive. *)
type field = Recursive of int | Boxed of int

(** The 0-based index of the field. *)
val index : field -> int

(** A constructor struct's key: {!Base.Common.ctor_owner_key} of its inductive
    and the struct's capitalised name (e.g. ["Cons"]); the owner is part of
    it because a constructor name alone does not identify a struct -- two
    inductives may each have a [Cons], with different fields. *)
module Key : sig
  type t = string * string

  val compare : t -> t -> int
end

(** A pointer field as planned: its index, whether it holds the inductive
    itself, and whether the value is held in the slot itself -- a shared
    variant's [crane::shared_box], or a [crane::shared_or_t] only an
    instantiation decides ({!Pointer_slot}) -- rather than in a cell the
    slot points at, which a copy of the slot shares. *)
type planned = {
  index : int;
  recursive : bool;
  in_slot : bool;
}

(** The pointer fields of each constructor struct that has one, by key. *)
type t

(** No constructor struct with a pointer field. *)
val none : t

(** [add m planned] is [m] with the pointer fields of each constructor
    struct planned: the inductive, the constructor's struct name and each
    field ({!Core_to_cpp.Inductives.constructor_pointer_fields}). *)
val add : t -> (Names.GlobRef.t * string * planned list) list -> t

(** The pointer fields of the constructor struct [key], if it has any. *)
val find : t -> Key.t -> field list option

(** The indices of the pointer fields of the constructor struct [key] whose
    value lies in a cell the slot points at, not in the slot: a pointer to
    the value stays good when the slot is copied, as long as one copy
    lives. *)
val cells : t -> Key.t -> int list option
