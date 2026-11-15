(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The module plan and the layout its facts are folded into.  See
    [module_plan.mli]. *)

open Names

type wrapper_role = Own | Flattened | Bystander
type eponymous_record = {record : GlobRef.t; type_params : int}

type concept_scope = {functor_ : ModPath.t; args : ModPath.t list}

type t = {
  global_scope_enums : GlobRef.t list;
  concept_names : (GlobRef.t * string) list;
  modtype_concept_names : (ModPath.t * string) list;
  functor_app_sources : (ModPath.t * ModPath.t) list;
  eponymous_records : eponymous_record list;
  namespace_scope_refs : GlobRef.t list;
  wrappers : (ModPath.t * string * wrapper_role option) list;
  global_scope_types : GlobRef.t list;
  concept_prerequisites : Label.t list;
}

let empty =
  { global_scope_enums = [];
    concept_names = [];
    modtype_concept_names = [];
    functor_app_sources = [];
    eponymous_records = [];
    namespace_scope_refs = [];
    wrappers = [];
    global_scope_types = [];
    concept_prerequisites = [] }

let equal a b =
  let refs = List.equal GlobRef.UserOrd.equal in
  let pairs eq_k eq_v = List.equal (fun (k, v) (k', v') -> eq_k k k' && eq_v v v') in
  refs a.global_scope_enums b.global_scope_enums
  && pairs GlobRef.UserOrd.equal String.equal a.concept_names b.concept_names
  && pairs ModPath.equal String.equal a.modtype_concept_names b.modtype_concept_names
  && pairs ModPath.equal ModPath.equal a.functor_app_sources b.functor_app_sources
  && List.equal
       (fun e e' -> GlobRef.UserOrd.equal e.record e'.record && Int.equal e.type_params e'.type_params)
       a.eponymous_records b.eponymous_records
  && refs a.namespace_scope_refs b.namespace_scope_refs
  && List.equal
       (fun (mp, n, r) (mp', n', r') -> ModPath.equal mp mp' && String.equal n n' && r = r')
       a.wrappers b.wrappers
  && refs a.global_scope_types b.global_scope_types
  && List.equal Label.equal a.concept_prerequisites b.concept_prerequisites

type layout = {
  enums : Ref.User.Set.t;
  concepts : string Ref.User.Map.t;
  modtype_concepts : string MPmap.t;
  app_sources : ModPath.t MPmap.t;
  eponymous : Ref.User.Set.t;
  eponymous_by_modpath : eponymous_record MPmap.t;
  namespace_scope : Ref.User.Set.t;
  wrapper_table : (string * wrapper_role) MPmap.t;
  global_types : Ref.User.Set.t;
  prerequisites : Label.Set.t;
}

let no_layout =
  { enums = Ref.User.Set.empty;
    concepts = Ref.User.Map.empty;
    modtype_concepts = MPmap.empty;
    app_sources = MPmap.empty;
    eponymous = Ref.User.Set.empty;
    eponymous_by_modpath = MPmap.empty;
    namespace_scope = Ref.User.Set.empty;
    wrapper_table = MPmap.empty;
    global_types = Ref.User.Set.empty;
    prerequisites = Label.Set.empty }

let extend l f =
  let refs s rs = List.fold_left (fun s r -> Ref.User.Set.add r s) s rs in
  let pairs add m kvs = List.fold_left (fun m (k, v) -> add k v m) m kvs in
  let eponymous_by_modpath =
    List.fold_left
      (fun m e ->
        match e.record with GlobRef.IndRef (ind, _) -> MPmap.add (MutInd.modpath ind) e m | _ -> m )
      l.eponymous_by_modpath f.eponymous_records
  in
  let wrapper_table =
    List.fold_left
      (fun m (mp, name, role) ->
        (* A role not given keeps the one already recorded. *)
        let role =
          match (role, MPmap.find_opt mp m) with
          | Some r, _ -> r
          | None, Some (_, r) -> r
          | None, None -> Own
        in
        MPmap.add mp (name, role) m )
      l.wrapper_table f.wrappers
  in
  { enums = refs Ref.User.Set.empty f.global_scope_enums;
    concepts = pairs Ref.User.Map.add l.concepts f.concept_names;
    modtype_concepts = pairs MPmap.add l.modtype_concepts f.modtype_concept_names;
    app_sources = pairs MPmap.add l.app_sources f.functor_app_sources;
    eponymous = refs l.eponymous (List.map (fun e -> e.record) f.eponymous_records);
    eponymous_by_modpath;
    namespace_scope = refs l.namespace_scope f.namespace_scope_refs;
    wrapper_table;
    global_types = refs l.global_types f.global_scope_types;
    prerequisites = List.fold_left (fun s l -> Label.Set.add l s) l.prerequisites f.concept_prerequisites }

let for_next_unit l = {l with namespace_scope = Ref.User.Set.empty; prerequisites = Label.Set.empty}

(* The layout read, for the extent {!with_layout} binds it for. *)
let current = ref no_layout

let with_layout l f = State.bind current l f

let () =
  List.iter
    (fun (name, size) -> Table.register_census name (fun () -> size !current))
    [ ("global_scope_enum_table", fun l -> Ref.User.Set.cardinal l.enums);
      ("concept_name_table", fun l -> Ref.User.Map.cardinal l.concepts);
      ("modtype_concept_name_table", fun l -> MPmap.cardinal l.modtype_concepts);
      ("functor_app_sources", fun l -> MPmap.cardinal l.app_sources);
      ("global_eponymous_record_registry", fun l -> Ref.User.Set.cardinal l.eponymous);
      ("eponymous_record_by_modpath", fun l -> MPmap.cardinal l.eponymous_by_modpath);
      ("namespace_scope_refs", fun l -> Ref.User.Set.cardinal l.namespace_scope);
      ("wrapper_table", fun l -> MPmap.cardinal l.wrapper_table);
      ("global_scope_type_table", fun l -> Ref.User.Set.cardinal l.global_types);
      ("concept_prerequisite_table", fun l -> Label.Set.cardinal l.prerequisites) ]

let is_global_scope_enum r = Ref.User.Set.mem r !current.enums
let concept_name r = Ref.User.Map.find_opt r !current.concepts
let modtype_concept_name mp = MPmap.find_opt mp !current.modtype_concepts
let functor_app_source mp = MPmap.find_opt mp !current.app_sources
let is_eponymous_record r = Ref.User.Set.mem r !current.eponymous
let eponymous_record_containing = function
  | GlobRef.ConstRef kn -> MPmap.find_opt (Constant.modpath kn) !current.eponymous_by_modpath
  | _ -> None
let is_namespace_scope_ref r = Ref.User.Set.mem r !current.namespace_scope
let wrapper mp = MPmap.find_opt mp !current.wrapper_table
let wrapper_struct mp = Option.map fst (wrapper mp)
let wrapper_role mp = Option.map snd (wrapper mp)
let is_global_scope_type r = Ref.User.Set.mem r !current.global_types
let is_concept_prerequisite l = Label.Set.mem l !current.prerequisites
