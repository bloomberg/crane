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

let installed : scope MPmap.t ref = State.cell State.Unit MPmap.empty
let installed_nested : MPset.t ref = State.cell State.Unit MPset.empty
let installed_templated : MPset.t ref = State.cell State.Unit MPset.empty
let installed_visibility : Common.visibility MPmap.t ref = State.cell State.Unit MPmap.empty
let installed_local_inductives : GlobRef.t list MPmap.t ref = State.cell State.Unit MPmap.empty
let installed_frames : ModPath.t list MPmap.t ref = State.cell State.Unit MPmap.empty

let set_of = List.fold_left (fun s mp -> MPset.add mp s) MPset.empty

let install t =
  installed := List.fold_left (fun m (mp, s) -> MPmap.add mp s m) MPmap.empty t.scopes;
  installed_nested := set_of t.nested;
  installed_templated := set_of t.templated;
  installed_visibility := List.fold_left (fun m (mp, v) -> MPmap.add mp v m) MPmap.empty t.visibility;
  installed_local_inductives := List.fold_left (fun m (mp, l) -> MPmap.add mp l m) MPmap.empty t.local_inductives;
  installed_frames := List.fold_left (fun m (mp, l) -> MPmap.add mp l m) MPmap.empty t.frames

let of_module mp = MPmap.find_opt mp !installed
let nested mp = MPset.mem mp !installed_nested
let templated mp = MPset.mem mp !installed_templated
let visibility mp = MPmap.find_opt mp !installed_visibility
let local_inductives mp = MPmap.find_opt mp !installed_local_inductives
let frames mp = MPmap.find_opt mp !installed_frames

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
