(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

open Names

type wrapper_role = Own | Flattened | Bystander

type t = {
  global_scope_enums : GlobRef.t list;
  concept_names : (GlobRef.t * string) list;
  functor_app_sources : (ModPath.t * ModPath.t) list;
  eponymous_records : GlobRef.t list;
  namespace_scope_refs : GlobRef.t list;
  wrappers : (ModPath.t * string * wrapper_role option) list;
  global_scope_types : GlobRef.t list;
}

(* One table per fact.  Each lives as long as its current users rely on: most
   accumulate over an extraction, so that a separate extraction still knows
   the layout earlier units decided; the enums at global scope are replaced by
   each unit's; the refs lifted to namespace scope belong to one unit. *)
let table ?(scope = State.Extraction) name =
  let t = State.table scope 16 in
  Table.register_census name (fun () -> Hashtbl.length t);
  t

let enums : (GlobRef.t, unit) Hashtbl.t = table "global_scope_enum_table"
let concepts : (GlobRef.t, string) Hashtbl.t = table "concept_name_table"
let app_sources : (ModPath.t, ModPath.t) Hashtbl.t = table "functor_app_sources"
let eponymous : (GlobRef.t, unit) Hashtbl.t = table "global_eponymous_record_registry"
let eponymous_by_modpath : (ModPath.t, GlobRef.t) Hashtbl.t =
  table "eponymous_record_by_modpath"
let namespace_scope : (GlobRef.t, unit) Hashtbl.t =
  table ~scope:State.Unit "namespace_scope_refs"
let wrapper_table : (ModPath.t, string * wrapper_role) Hashtbl.t = table "wrapper_table"
let global_types : (GlobRef.t, unit) Hashtbl.t = table "global_scope_type_table"

let install f =
  Hashtbl.reset enums;
  List.iter (fun r -> Hashtbl.replace enums r ()) f.global_scope_enums;
  List.iter (fun (r, name) -> Hashtbl.replace concepts r name) f.concept_names;
  List.iter (fun (mp, src) -> Hashtbl.replace app_sources mp src) f.functor_app_sources;
  List.iter
    (fun r ->
      Hashtbl.replace eponymous r ();
      match r with
      | GlobRef.IndRef (ind, _) ->
        Hashtbl.replace eponymous_by_modpath (MutInd.modpath ind) r
      | _ -> () )
    f.eponymous_records;
  List.iter (fun r -> Hashtbl.replace namespace_scope r ()) f.namespace_scope_refs;
  List.iter
    (fun (mp, name, role) ->
      (* A role not given keeps the one already recorded. *)
      let role =
        match (role, Hashtbl.find_opt wrapper_table mp) with
        | Some r, _ -> r
        | None, Some (_, r) -> r
        | None, None -> Own
      in
      Hashtbl.replace wrapper_table mp (name, role) )
    f.wrappers;
  List.iter (fun r -> Hashtbl.replace global_types r ()) f.global_scope_types

let is_global_scope_enum r = Hashtbl.mem enums r
let concept_name r = Hashtbl.find_opt concepts r
let functor_app_source mp = Hashtbl.find_opt app_sources mp
let is_eponymous_record r = Hashtbl.mem eponymous r
let eponymous_record_containing = function
  | GlobRef.ConstRef kn -> Hashtbl.find_opt eponymous_by_modpath (Constant.modpath kn)
  | _ -> None
let is_namespace_scope_ref r = Hashtbl.mem namespace_scope r
let wrapper mp = Hashtbl.find_opt wrapper_table mp
let wrapper_struct mp = Option.map fst (wrapper mp)
let wrapper_role mp = Option.map snd (wrapper mp)
let is_global_scope_type r = Hashtbl.mem global_types r
