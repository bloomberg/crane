(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

open Miniml

type binder_role =
  | Value
  | Erased of kill_reason

type binder_info = {
  binder : Scheme.Binder.t;
  role : binder_role;
  scheme_var : Scheme.Var.t option;
}

type raw_binder = {
  raw_erased : kill_reason option;
  raw_tvar : int option;
}

type t = {
  id : Scheme.Id.t;
  body : ml_type;
  layout : binder_info list;
}

let max_tvar t =
  let rec parse n = function
    | Tmeta {contents = Some t} -> parse n t
    | Tvar (Schematic, i) -> max i n
    | Tapp (i, l) -> List.fold_left parse (max i n) l
    | Tarr (a, b) -> parse (parse n a) b
    | Tglob (_, l, _) -> List.fold_left parse n l
    | _ -> n
  in
  parse 0 t

let make owner body raw =
  let id = Scheme.Id.fresh owner ~arity:(max_tvar body) in
  let layout =
    List.mapi
      (fun k {raw_erased; raw_tvar} ->
        { binder = Scheme.Binder.of_position k;
          role = (match raw_erased with Some r -> Erased r | None -> Value);
          scheme_var = Option.bind raw_tvar (Scheme.Var.of_tvar id) } )
      raw
  in
  let claimed = List.filter_map (fun b -> b.scheme_var) layout in
  if List.length (List.sort_uniq Scheme.Var.compare claimed) <> List.length claimed
  then invalid_arg "Ml_schema.make: two binders claim one variable";
  {id; body; layout}

let id s = s.id
let owner s = Scheme.Id.owner s.id
let body s = s.body
let arity s = Scheme.Id.arity s.id
let vars s = Scheme.Var.all s.id
let binders s = s.layout

let binder s b =
  List.find_opt (fun i -> Scheme.Binder.equal i.binder b) s.layout

let origin s v =
  List.find_opt
    (fun i ->
      match i.scheme_var with
      | Some v' -> Scheme.Var.equal v v'
      | None -> false )
    s.layout

let with_roles f s = {s with layout = List.map (fun i -> {i with role = f i}) s.layout}
let with_body body s = {s with body}

let validate s =
  let body_max = max_tvar s.body in
  let dense =
    if body_max <= arity s then []
    else [Printf.sprintf "body mentions Tvar %d past arity %d" body_max (arity s)]
  in
  let ordered =
    List.concat
      (List.mapi
         (fun k i ->
           if Scheme.Binder.position i.binder = k then []
           else [Printf.sprintf "binder %d out of source order" k] )
         s.layout )
  in
  let owned =
    List.filter_map
      (fun i ->
        match i.scheme_var with
        | Some v when not (Scheme.Id.equal (Scheme.Var.owner v) s.id) ->
          Some (Printf.sprintf "binder %d names another scheme's variable"
                  (Scheme.Binder.position i.binder))
        | _ -> None )
      s.layout
  in
  let claimed = List.filter_map (fun i -> i.scheme_var) s.layout in
  let unique =
    if List.length (List.sort_uniq Scheme.Var.compare claimed) = List.length claimed
    then []
    else ["two binders claim one variable"]
  in
  let originated =
    List.filter_map
      (fun v ->
        if Option.has_some (origin s v) then None
        else Some (Printf.sprintf "variable %d has no source binder" (Scheme.Var.ordinal v)) )
      (vars s)
  in
  dense @ ordered @ owned @ unique @ originated
