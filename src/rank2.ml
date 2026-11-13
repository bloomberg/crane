(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

open Names
open Cpp_ir.Type

let carrier_name = Generated_name.id "X"

let quantifies_erased_type ty =
  let rec go ty =
    match Ml_type_util.resolve_tmeta ty with
    | Miniml.Tunknown -> true
    | Miniml.Tglob (_, args, _) | Miniml.Tapp (_, args) -> List.exists go args
    | Miniml.Tarr (a, b) -> go a || go b
    | _ -> false
  in
  go ty

let carrier_type x : Cpp_ir.Lowered.Type.t = Cpp_ir.Build.named_variable x

let at_carrier x ty =
  Cpp_ir.Types.map (function Obligation Opaque_type | Any -> carrier_type x | t -> t) ty

let rec is_bare_box : Cpp_ir.Lowered.Type.t -> bool = function
  | Const t | Reference (_, t) -> is_bare_box t
  | Any | Obligation Opaque_type -> true
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
