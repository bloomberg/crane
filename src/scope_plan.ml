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
  local_inductives : (ModPath.t * GlobRef.t list) list;
  frames : (ModPath.t * ModPath.t list) list;
}

let empty = {scopes = []; nested = []; templated = []; visibility = []; local_inductives = []; frames = []}

let equal_plans a b =
  List.equal (fun (mp, s) (mp', s') -> ModPath.equal mp mp' && equal s s') a.scopes b.scopes
  && List.equal ModPath.equal a.nested b.nested
  && List.equal ModPath.equal a.templated b.templated
  && List.equal
       (fun (mp, v) (mp', v') -> ModPath.equal mp mp' && Common.equal_visibility v v')
       a.visibility b.visibility
  && List.equal
       (fun (mp, l) (mp', l') -> ModPath.equal mp mp' && List.equal GlobRef.UserOrd.equal l l')
       a.local_inductives b.local_inductives
  && List.equal
       (fun (mp, l) (mp', l') -> ModPath.equal mp mp' && List.equal ModPath.equal l l')
       a.frames b.frames

type bound = {
  scope_of : scope MPmap.t;
  nested_in : MPset.t;
  templated_in : MPset.t;
  visibility_of : Common.visibility MPmap.t;
  local_inductives_of : GlobRef.t list MPmap.t;
  frames_of : ModPath.t list MPmap.t;
}

let set_of = List.fold_left (fun s mp -> MPset.add mp s) MPset.empty
let map_of l = List.fold_left (fun m (mp, x) -> MPmap.add mp x m) MPmap.empty l

let bound_of t =
  { scope_of = map_of t.scopes;
    nested_in = set_of t.nested;
    templated_in = set_of t.templated;
    visibility_of = map_of t.visibility;
    local_inductives_of = map_of t.local_inductives;
    frames_of = map_of t.frames }

let none = bound_of empty

let of_module b mp = MPmap.find_opt mp b.scope_of
let nested b mp = MPset.mem mp b.nested_in
let templated b mp = MPset.mem mp b.templated_in
let visibility b mp = MPmap.find_opt mp b.visibility_of
let local_inductives b mp = MPmap.find_opt mp b.local_inductives_of
let frames b mp = MPmap.find_opt mp b.frames_of

let of_declaration layout b r =
  let origin =
    match Lifted.of_ref r with
    | Some helper -> (
      match Lifted.origin helper with
      | Some o when Module_plan.is_namespace_scope_ref layout o -> None
      | origin -> origin )
    | None -> Some r
  in
  Option.bind origin (fun o -> of_module b (Table.modpath_of_r o))
