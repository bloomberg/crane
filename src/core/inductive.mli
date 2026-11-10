(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Core's inductive types: how one is treated by the backend ({!Kind}) and
    how it relates to an inductive already extracted ({!Equivalence}). *)

module Kind : sig
  (** How an inductive type should be treated by the backend. [Inductive] is
      an ordinary (finite) inductive; [Coinductive] a lazily-unfolded one;
      [Record] a single-constructor inductive presented with named
      projections (the list gives its fields); and [Type_class] a record
      standing for a Rocq type class, whose fields are its methods.

      ['field] is a field's description ({!Miniml.record_field}): its type
      is a Core type, and this module comes before Core's types. *)
  type 'field t =
    | Coinductive
    | Inductive
    | Record of 'field list
    | Type_class of 'field list
end

module Equivalence : sig
  (** How an inductive relates to another already-extracted one, used to
      share definitions. [Distinct] means it is emitted on its own;
      [Equivalent_to kn] redirects it to the kernel name [kn] of an
      equivalent inductive; [Equivalent_in_renamed_module s] redirects to an
      inductive living in the module renamed [s]. *)
  type t =
    | Distinct
    | Equivalent_to of Names.KerName.t
    | Equivalent_in_renamed_module of string
end
