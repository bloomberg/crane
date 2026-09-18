(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

open Names
open Minicpp

let carrier_name = Id.of_string "_X"

let quantifies_erased_type ty =
  let rec go ty =
    match Ml_type_util.resolve_tmeta ty with
    | Miniml.Tunknown -> true
    | Miniml.Tglob (_, args, _) | Miniml.Tapp (_, args) -> List.exists go args
    | Miniml.Tarr (a, b) -> go a || go b
    | _ -> false
  in
  go ty

let carrier_type = named_tvar

let at_carrier x ty =
  map_cpp_type (function Topaque | Tany -> carrier_type x | t -> t) ty

let rec is_bare_box = function
  | Tconst t | Tref t -> is_bare_box t
  | Tany | Topaque -> true
  | _ -> false

let type_args_at_carrier x r =
  let kn =
    match r with
    | GlobRef.IndRef (kn, _) | GlobRef.ConstructRef ((kn, _), _) -> Some kn
    | _ -> None
  in
  match Option.bind kn Table.get_ind_num_param_vars_opt with
  | Some n when n > 0 -> Some (List.init n (fun _ -> carrier_type x))
  | _ -> None
