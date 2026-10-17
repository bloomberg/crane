(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

open Miniml

type evidence =
  | Written
  | Argument_types
  | Argument_heads
  | Expected_result
  | Eta_parameter

type slot =
  | Known of ml_type * evidence
  | Unreadable
  | Unwritten

type t = {
  callee : Names.GlobRef.t;
  slots : (Scheme.Var.t * slot) list;
}

let erased = function
  | Tdummy _ -> true
  | _ -> false

let of_source = function
  | Scheme.Written {observed = Some ty; _} when not (erased ty) -> Known (ty, Written)
  | Scheme.Written _ -> Unreadable
  | Scheme.Not_written -> Unwritten

let of_use use =
  let slots =
    match Global_use.instantiation use with
    | None -> []
    | Some inst ->
      List.sort
        (fun (v, _) (w, _) -> Scheme.Var.compare v w)
        (Scheme.Instantiation.fold
           (fun v s acc -> (v, of_source s.Scheme.source) :: acc)
           inst [] )
  in
  {callee = Global_use.callee use; slots}

let callee t = t.callee
let vars t = List.map fst t.slots

let slot t v =
  match List.find_opt (fun (w, _) -> Scheme.Var.equal v w) t.slots with
  | Some (_, s) -> s
  | None -> Unwritten

let is_hole t v =
  match slot t v with
  | Known _ -> false
  | Unreadable | Unwritten -> true

let is_unwritten t v =
  match slot t v with
  | Unwritten -> true
  | Known _ | Unreadable -> false

let holes t = List.filter (is_hole t) (vars t)

(* The last variable known or written unreadably. *)
let last_spoken t =
  Mlutil.last_var
    (List.filter_map
       (fun (v, s) ->
         match s with
         | Known _ | Unreadable -> Some v
         | Unwritten -> None )
       t.slots )

let within t v =
  match last_spoken t with
  | Some last -> Scheme.Var.compare v last <= 0
  | None -> false

let interior_holes t = List.filter (fun v -> within t v && is_hole t v) (vars t)
let beyond_extent t = List.filter (fun v -> not (within t v)) (vars t)

let evidence_name = function
  | Written -> "written"
  | Argument_types -> "argument_types"
  | Argument_heads -> "argument_heads"
  | Expected_result -> "expected_result"
  | Eta_parameter -> "eta_parameter"

let answers e answer vs t =
  List.filter_map
    (fun v ->
      if not (is_hole t v) then None
      else
        match answer v with
        | Some ty when not (erased ty) -> Some (v, Known (ty, e))
        | _ -> None )
    vs

let with_answers e t found =
  List.iter
    (fun (v, _) ->
      Probe.hit
        ("RESOLVE_" ^ evidence_name e)
        (fun () ->
          Pp.string_of_ppcmds (Names.GlobRef.print t.callee)
          ^ " " ^ string_of_int (Scheme.Var.ordinal v) ) )
    found;
  { t with
    slots =
      List.map
        (fun (v, s) ->
          match List.find_opt (fun (w, _) -> Scheme.Var.equal v w) found with
          | Some (_, s') -> (v, s')
          | None -> (v, s) )
        t.slots }

let resolve e answer vs t = with_answers e t (answers e answer vs t)

let resolve_all e answer vs t =
  let holes = List.filter (is_hole t) vs in
  let found = answers e answer holes t in
  if List.length found = List.length holes then with_answers e t found else t

let resolved_from e t =
  List.exists
    (fun (_, s) ->
      match s with
      | Known (_, e') -> e' = e
      | Unreadable | Unwritten -> false )
    t.slots

let by_variable t =
  Mlutil.Var_types.through (last_spoken t) (fun v ->
      match slot t v with
      | Known (ty, _) -> ty
      | Unreadable | Unwritten -> Tdummy Ktype )
