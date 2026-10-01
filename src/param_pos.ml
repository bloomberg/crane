(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

type orig
type subst
type 'k pos = int
type 'k params = Miniml.ml_type list

let collect ~expand ty =
  let rec go ty =
    match expand ty with
    | Miniml.Tarr (t, rest) -> (
      match Ml_type_util.resolve_tmeta t with
      | Miniml.Tdummy _ -> go rest
      | t -> t :: go rest )
    | _ -> []
  in
  go ty

let orig_params = collect
let subst_params = collect
let to_list l = l
let length = List.length
let nth l i = List.nth_opt l i
let positioned l = List.mapi (fun i t -> (i, t)) l
let of_regular ~leading i = leading + i
let regular_of ~leading p = if p >= leading then Some (p - leading) else None

let subst_of_orig ~erased orig o =
  match List.nth_opt orig o with
  | None -> None
  | Some t when erased t -> None
  | Some _ ->
    let rec dropped k = function
      | t :: rest when k < o -> (if erased t then 1 else 0) + dropped (k + 1) rest
      | _ -> 0
    in
    Some (o - dropped 0 orig)

let subst_at_declared o = o
let of_receiver p = p
let equal = Int.equal
