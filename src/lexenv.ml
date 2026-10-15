(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

type role =
  | Value
  | Dictionary

type binder = {
  eb_id : Names.Id.t;
  eb_type : Miniml.ml_type;
  eb_role : role;
}

type t = binder list

let empty = []

let push bs env = bs @ env

let binder env i = if i <= 0 then None else List.nth_opt env (pred i)

let type_opt env i = Option.map (fun b -> b.eb_type) (binder env i)

let depth = List.length
