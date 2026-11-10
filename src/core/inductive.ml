(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Core's inductive types.  See [inductive.mli]. *)

module Kind = struct
  type 'field t =
    | Coinductive
    | Inductive
    | Record of 'field list
    | Type_class of 'field list
end

module Equivalence = struct
  type t =
    | Distinct
    | Equivalent_to of Names.KerName.t
    | Equivalent_in_renamed_module of string
end
