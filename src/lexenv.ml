(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The lexical environment of a Core body.  See [lexenv.mli]. *)

type role =
  | Value
  | Dictionary

type binder = {
  id : Names.Id.t;
  type_ : Core.Type.t;
  role : role;
}

type t = binder list

let empty = []

let push bs env = bs @ env

let binder env i = if i <= 0 then None else List.nth_opt env (pred i)

let type_opt env i = Option.map (fun b -> b.type_) (binder env i)

let depth = List.length
