(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** How a match is lowered.  See [match_kind.mli]. *)

open Miniml

type application =
  | Read
  | Call
  | Coerced_call

type record_body =
  | Projection of {field : int; application : application}
  | Destructure

type t =
  | Custom
  | Record of {typeclass : bool; body : record_body}
  | Variant

(* A custom match is decided first: a record whose match is mapped is
   matched by its template.  A projection's body is looked at through one
   coercion. *)
let classify ty branches =
  if Table.is_custom_match branches then Custom
  else
    match branches with
    | [|(ids, _, _, body)|] when Table.record_fields_of_type ty <> [] ->
      let n = List.length ids in
      let body =
        match (match body with MLmagic (_, b, _) -> b | b -> b) with
        | MLrel (i, _) when i <= n -> Projection {field = n - i; application = Read}
        | MLapp (MLrel (i, _), _) when i <= n -> Projection {field = n - i; application = Call}
        | MLapp (MLmagic (_, MLrel (i, _), _), _) when i <= n -> Projection {field = n - i; application = Coerced_call}
        | _ -> Destructure
      in
      Record {typeclass = Table.is_typeclass_type ty; body}
    | _ -> Variant

let is_record = function Record _ -> true | Custom | Variant -> false

let bound_in_place = function Custom | Record _ -> true | Variant -> false
