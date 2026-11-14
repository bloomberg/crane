(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** C++ types ({!Grammar.Type}), with the families only a type names. *)

include Grammar.Type
module Type_variable = Grammar.Type_variable
module Erased_kind = Grammar.Erased_kind
module Variant_storage = Grammar.Variant_storage
module Reference_kind = Grammar.Reference_kind
module Type_test = Grammar.Type_test

(** [positional_name i] is the name the type variable at index [i] of a
    declaration's parameter list is written under: [T<i>]
    ({!Core.Positional.name}). *)
let positional_name = Core.Positional.name

(** [positional_id i] is {!positional_name} as an identifier. *)
let positional_id = Core.Positional.id

(** Whether [t] is the type variable named [id], under either spelling a
    variable's head may have. *)
let is_variable_named id (t : _ t) =
  match t with
  | Variable (Named n) -> Names.Id.equal n id
  | Variable (Index (i, name)) ->
    (match name with Some n -> Names.Id.equal n id | None -> false) || Names.Id.equal (positional_id i) id
  | _ -> false
