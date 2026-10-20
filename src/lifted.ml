(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Identities for the helpers Crane lifts out of declaration bodies. See
    [lifted.mli]. *)

open Names

type site =
  | Let of Miniml.Occurrence.t
  | Fixpoint of Miniml.Occurrence.t * int

let same_site a b =
  match (a, b) with
  | Let o, Let o' -> Miniml.Occurrence.equal o o'
  | Fixpoint (o, m), Fixpoint (o', m') -> Miniml.Occurrence.equal o o' && Int.equal m m'
  | Let _, Fixpoint _ | Fixpoint _, Let _ -> false

type t =
  { origin : GlobRef.t option;
    binder : Id.t;
    site : site;  (** what the helper is, with {!field:origin} *)
    serial : int;
        (** the order it was made in among the helpers of this extraction,
            which orders two helpers of one origin bound to one name *)
    name : Id.t  (** what it is spelled, derived from the rest *) }

let compare_origin o o' =
  match (o, o') with
  | None, None -> 0
  | None, Some _ -> -1
  | Some _, None -> 1
  | Some r, Some r' -> GlobRef.CanOrd.compare r r'

let same_origin o o' = compare_origin o o' = 0

(** The helpers made in this extraction, newest first, and their spellings.
    A site is an occurrence in the terms this extraction made, so neither
    outlives it; within it a helper spells the same in the header and in the
    implementation, and in every unit. *)
let made : t list ref = State.cell State.Extraction []

let by_name : (Id.t, t) Hashtbl.t = State.table State.Extraction 16

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

let ref_of t = GlobRef.VarRef t.name

(** Decide [t]'s name in the unit being extracted, as it is made: a name
    decided later, when the helper is first printed, is missing from every
    environment snapshot taken in between -- its origin's among them -- so a
    file that generates the origin before printing the helper sees a
    different set of global names than one that generates it after.  The
    definition is written under {!name} and its calls under the decided name,
    so the two must agree. *)
let decide t =
  let decided = Common.pp_global_name Common.Term (ref_of t) in
  if not (String.equal decided (Id.to_string t.name)) then
    CErrors.anomaly
      Pp.(str "Crane: the helper " ++ Id.print t.name ++ str " would be called as "
          ++ str decided ++ str ".")

let make ~origin ~binder site =
  let t =
    match
      List.find_opt
        (fun t -> same_origin t.origin origin && Id.equal t.binder binder && same_site t.site site)
        !made
    with
    | Some t -> t
    | None ->
      let name = unique_name (preferred_name ~origin ~binder) 0 in
      let t = { origin; binder; site; serial = List.length !made; name } in
      made := t :: !made;
      Hashtbl.replace by_name name t;
      t
  in
  decide t;
  t

let of_ref = function
  | GlobRef.VarRef id -> Hashtbl.find_opt by_name id
  | _ -> None

let name t = t.name
let origin t = t.origin
let binder t = t.binder
let fixpoint t = match t.site with Fixpoint (o, m) -> Some (o, m) | Let _ -> None

let compare a b =
  let c = compare_origin a.origin b.origin in
  if c <> 0 then c
  else
    let c = Id.compare a.binder b.binder in
    if c <> 0 then c else Int.compare a.serial b.serial

let equal a b = compare a b = 0
