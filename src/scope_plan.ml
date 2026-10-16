(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

open Names

type scope = {
  module_ : ModPath.t;
  qualifier : string list;
}

let equal a b = ModPath.equal a.module_ b.module_ && List.equal String.equal a.qualifier b.qualifier
let qualifier s = String.concat "::" s.qualifier

type t = {
  scopes : (ModPath.t * scope) list;
  nested : ModPath.t list;
  templated : ModPath.t list;
  visibility : (ModPath.t * Common.visibility) list;
}

let empty = {scopes = []; nested = []; templated = []; visibility = []}

let equal_plans a b =
  List.equal (fun (mp, s) (mp', s') -> ModPath.equal mp mp' && equal s s') a.scopes b.scopes
  && List.equal ModPath.equal a.nested b.nested
  && List.equal ModPath.equal a.templated b.templated
  && List.equal
       (fun (mp, v) (mp', v') -> ModPath.equal mp mp' && Common.equal_visibility v v')
       a.visibility b.visibility

let installed : scope MPmap.t ref = State.cell State.Unit MPmap.empty
let installed_nested : MPset.t ref = State.cell State.Unit MPset.empty
let installed_templated : MPset.t ref = State.cell State.Unit MPset.empty
let installed_visibility : Common.visibility MPmap.t ref = State.cell State.Unit MPmap.empty

let set_of = List.fold_left (fun s mp -> MPset.add mp s) MPset.empty

let install t =
  installed := List.fold_left (fun m (mp, s) -> MPmap.add mp s m) MPmap.empty t.scopes;
  installed_nested := set_of t.nested;
  installed_templated := set_of t.templated;
  installed_visibility := List.fold_left (fun m (mp, v) -> MPmap.add mp v m) MPmap.empty t.visibility

let of_module mp = MPmap.find_opt mp !installed
let nested mp = MPset.mem mp !installed_nested
let templated mp = MPset.mem mp !installed_templated
let visibility mp = MPmap.find_opt mp !installed_visibility

let of_declaration r =
  let origin =
    match Lifted.of_ref r with
    | Some helper -> (
      match Lifted.origin helper with
      | Some o when Module_plan.is_namespace_scope_ref o -> None
      | origin -> origin )
    | None -> Some r
  in
  Option.bind origin (fun o -> of_module (Table.modpath_of_r o))
