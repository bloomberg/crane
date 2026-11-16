(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** How a match is lowered.  See [match_kind.mli]. *)


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
   coercion; its [field] counts from the first binder, where [Core.Expr.Bound_variable i]
   counts from the last. *)
let classify ty branches =
  if Base.Table.is_custom_match branches then Custom
  else
    match branches with
    | [|{Core.Match.Branch.binders = ids; body = body; _}|] when Base.Table.record_fields_of_type ty <> [] ->
      let n = List.length ids in
      let body =
        match (match body with Core.Expr.Coerce {value = b; _} | Core.Expr.Boxed_value {value = b; _}
            | Core.Expr.Lambda_group_barrier {value = b; _} -> b | b -> b) with
        | Core.Expr.Bound_variable {index = i; _} when i <= n -> Projection {field = n - i; application = Read}
        | Core.Expr.Apply {callee = Core.Expr.Bound_variable {index = i; _}; _} when i <= n ->
          Projection {field = n - i; application = Call}
        | Core.Expr.Apply
          {callee =
            (Core.Expr.Coerce {value = Core.Expr.Bound_variable {index = i; _}; _}
              | Core.Expr.Boxed_value {value = Core.Expr.Bound_variable {index = i; _}; _}
              | Core.Expr.Lambda_group_barrier {value = Core.Expr.Bound_variable {index = i; _}; _}); _}
          when i <= n ->
          Projection {field = n - i; application = Coerced_call}
        | _ -> Destructure
      in
      Record {typeclass = Base.Table.is_typeclass_type ty; body}
    | _ -> Variant

let is_record = function Record _ -> true | Custom | Variant -> false

let bound_in_place = function Custom | Record _ -> true | Variant -> false
