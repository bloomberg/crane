(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

open Names

type wrapper_role = Own | Flattened | Bystander

type t = {
  global_scope_enums : GlobRef.t list;
  concept_names : (GlobRef.t * string) list;
  modtype_concept_names : (ModPath.t * string) list;
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

(* {!table}, keyed by global references at their user identity: what a name
   is known to be, under the name it was written. *)
let ref_table ?(scope = State.Extraction) name =
  let t = Ref.User.Tbl.create 16 in
  State.on_reset scope (fun () -> Ref.User.Tbl.reset t);
  Table.register_census name (fun () -> Ref.User.Tbl.length t);
  t

let enums : unit Ref.User.Tbl.t = ref_table "global_scope_enum_table"
let concepts : string Ref.User.Tbl.t = ref_table "concept_name_table"
let modtype_concepts : (ModPath.t, string) Hashtbl.t = table "modtype_concept_name_table"
let app_sources : (ModPath.t, ModPath.t) Hashtbl.t = table "functor_app_sources"
let eponymous : unit Ref.User.Tbl.t = ref_table "global_eponymous_record_registry"
let eponymous_by_modpath : (ModPath.t, GlobRef.t) Hashtbl.t =
  table "eponymous_record_by_modpath"
let namespace_scope : unit Ref.User.Tbl.t =
  ref_table ~scope:State.Unit "namespace_scope_refs"
let wrapper_table : (ModPath.t, string * wrapper_role) Hashtbl.t = table "wrapper_table"
let global_types : unit Ref.User.Tbl.t = ref_table "global_scope_type_table"

let empty =
  { global_scope_enums = [];
    concept_names = [];
    modtype_concept_names = [];
    functor_app_sources = [];
    eponymous_records = [];
    namespace_scope_refs = [];
    wrappers = [];
    global_scope_types = [] }

let equal a b =
  let refs = List.equal GlobRef.UserOrd.equal in
  let pairs eq_k eq_v = List.equal (fun (k, v) (k', v') -> eq_k k k' && eq_v v v') in
  refs a.global_scope_enums b.global_scope_enums
  && pairs GlobRef.UserOrd.equal String.equal a.concept_names b.concept_names
  && pairs ModPath.equal String.equal a.modtype_concept_names b.modtype_concept_names
  && pairs ModPath.equal ModPath.equal a.functor_app_sources b.functor_app_sources
  && refs a.eponymous_records b.eponymous_records
  && refs a.namespace_scope_refs b.namespace_scope_refs
  && List.equal
       (fun (mp, n, r) (mp', n', r') -> ModPath.equal mp mp' && String.equal n n' && r = r')
       a.wrappers b.wrappers
  && refs a.global_scope_types b.global_scope_types

let install f =
  Ref.User.Tbl.reset enums;
  List.iter (fun r -> Ref.User.Tbl.replace enums r ()) f.global_scope_enums;
  List.iter (fun (r, name) -> Ref.User.Tbl.replace concepts r name) f.concept_names;
  List.iter (fun (mp, name) -> Hashtbl.replace modtype_concepts mp name) f.modtype_concept_names;
  List.iter (fun (mp, src) -> Hashtbl.replace app_sources mp src) f.functor_app_sources;
  List.iter
    (fun r ->
      Ref.User.Tbl.replace eponymous r ();
      match r with
      | GlobRef.IndRef (ind, _) ->
        Hashtbl.replace eponymous_by_modpath (MutInd.modpath ind) r
      | _ -> () )
    f.eponymous_records;
  List.iter (fun r -> Ref.User.Tbl.replace namespace_scope r ()) f.namespace_scope_refs;
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
  List.iter (fun r -> Ref.User.Tbl.replace global_types r ()) f.global_scope_types

let is_global_scope_enum r = Ref.User.Tbl.mem enums r
let concept_name r = Ref.User.Tbl.find_opt concepts r
let modtype_concept_name mp = Hashtbl.find_opt modtype_concepts mp
let functor_app_source mp = Hashtbl.find_opt app_sources mp
let is_eponymous_record r = Ref.User.Tbl.mem eponymous r
let eponymous_record_containing = function
  | GlobRef.ConstRef kn -> Hashtbl.find_opt eponymous_by_modpath (Constant.modpath kn)
  | _ -> None
let is_namespace_scope_ref r = Ref.User.Tbl.mem namespace_scope r
let wrapper mp = Hashtbl.find_opt wrapper_table mp
let wrapper_struct mp = Option.map fst (wrapper mp)
let wrapper_role mp = Option.map snd (wrapper mp)
let is_global_scope_type r = Ref.User.Tbl.mem global_types r

(* The last of [l]'s answers for each key, which is the one installing [l]
   leaves. *)
let last_answers equal_key l =
  List.filteri
    (fun i (k, _) -> not (List.exists (fun (k', _) -> equal_key k k') (List.filteri (fun j _ -> j > i) l)))
    l

let installed f =
  let mp_equal = ModPath.equal and ref_equal = GlobRef.UserOrd.equal in
  List.for_all is_global_scope_enum f.global_scope_enums
  && List.for_all
       (fun (r, name) -> concept_name r = Some name)
       (last_answers ref_equal f.concept_names)
  && List.for_all
       (fun (mp, name) -> modtype_concept_name mp = Some name)
       (last_answers mp_equal f.modtype_concept_names)
  && List.for_all
       (fun (mp, src) -> Option.equal ModPath.equal (functor_app_source mp) (Some src))
       (last_answers mp_equal f.functor_app_sources)
  && List.for_all is_eponymous_record f.eponymous_records
  && List.for_all is_namespace_scope_ref f.namespace_scope_refs
  && List.for_all
       (fun (mp, (name, role)) ->
         match wrapper mp with
         | Some (name', role') -> String.equal name name' && Option.cata (( = ) role') true role
         | None -> false )
       (last_answers mp_equal (List.map (fun (mp, name, role) -> (mp, (name, role))) f.wrappers))
  && List.for_all is_global_scope_type f.global_scope_types
