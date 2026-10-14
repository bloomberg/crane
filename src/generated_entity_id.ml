(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

open Names

type role = Lifted_helper of Id.t

type t = { owner : Entity_id.t option; role : role }

let lifted_helper h =
  { owner = Option.map Entity_id.of_ref (Lifted.origin h);
    role = Lifted_helper (Lifted.binder h) }

let owner t = t.owner
let role t = t.role

let compare a b =
  let c = Option.compare Entity_id.compare a.owner b.owner in
  if c <> 0 then c
  else match (a.role, b.role) with Lifted_helper x, Lifted_helper y -> Id.compare x y

let equal a b = compare a b = 0

let pp t =
  let owner = match t.owner with Some e -> Entity_id.pp e | None -> Pp.str "<toplevel>" in
  match t.role with
  | Lifted_helper b -> Pp.(owner ++ str "/lifted:" ++ Id.print b)
