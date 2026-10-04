(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Identities for the helpers Crane lifts out of declaration bodies. See
    [lifted.mli]. *)

open Names

(** A helper's identity -- the declaration it was lifted out of, and the binder
    it was bound to there -- ordered so it can key the registry. *)
module Key = struct
  type t = GlobRef.t option * Id.t

  let compare (o1, b1) (o2, b2) =
    let c =
      match (o1, o2) with
      | None, None -> 0
      | None, Some _ -> -1
      | Some _, None -> 1
      | Some r1, Some r2 -> GlobRef.CanOrd.compare r1 r2
    in
    if c <> 0 then c else Id.compare b1 b2
end

module KeyMap = Map.Make (Key)

type t =
  { key : Key.t;  (** what the helper is *)
    name : Id.t  (** what it is spelled, derived from {!field:key} *) }

(** The two directions of the identity/spelling correspondence. Both are kept
    for the whole session: a helper must spell the same in the header and in
    the implementation, and an identity is canonical across units, so there is
    nothing to reset between them. *)
let by_key : t KeyMap.t ref = ref KeyMap.empty

let by_name : (Id.t, t) Hashtbl.t = Hashtbl.create 16

(** The spelling a helper would like, before uniqueness is imposed: the
    {!Generated_name.companion} of the enclosing declaration, whose name is
    the disambiguator that keeps two helpers bound to the same binder in
    different declarations apart.  A helper may land at namespace scope, where
    a leading underscore is reserved. *)
let preferred_name ~origin ~binder =
  let outer =
    match origin with
    | Some r -> Common.pp_global_name Common.Term r
    | None -> "anon"
  in
  Id.to_string
    (Generated_name.companion (Id.of_string outer) (Id.to_string binder))

(** [unique_name base] is [base], or [base] with the least counter appended
    that is not already some other helper's spelling. *)
let rec unique_name base n =
  let id = Id.of_string (if n = 0 then base else base ^ "_" ^ string_of_int n) in
  if Hashtbl.mem by_name id then unique_name base (n + 1) else id

let make ~origin ~binder =
  let key = (origin, binder) in
  match KeyMap.find_opt key !by_key with
  | Some t -> t
  | None ->
    let name = unique_name (preferred_name ~origin ~binder) 0 in
    let t = { key; name } in
    by_key := KeyMap.add key t !by_key;
    Hashtbl.replace by_name name t;
    t

let ref_of t = GlobRef.VarRef t.name

let of_ref = function
  | GlobRef.VarRef id -> Hashtbl.find_opt by_name id
  | _ -> None

let name t = t.name

let equal a b = Key.compare a.key b.key = 0
