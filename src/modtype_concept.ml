(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

open Names
open Miniml
open Minicpp

type concept_type =
  | Member of {member : GlobRef.t; enum : bool; arguments : concept_type list}
  | Parameter of cpp_type
  | Foreign of string * concept_type list
  | Global of GlobRef.t * concept_type list
  | Namespaced of GlobRef.t * GlobRef.t * cpp_expr list * concept_type list
  | Shared_pointer of concept_type
  | Variant of variant_storage * concept_type list
  | Function of concept_type list * concept_type
  | Plain of cpp_type

type requirement =
  | Inductive_member of {member : GlobRef.t; enum : bool; arity : int}
  | Type_member of {member : GlobRef.t; arity : int}
  | Instance_member of {value : GlobRef.t; class_ : GlobRef.t; arguments : concept_type list}
  | Nullary_member of {value : GlobRef.t; result : concept_type}
  | Function_member of {value : GlobRef.t; parameters : concept_type list; result : concept_type}
  | Submodule of {label : Label.t; module_type : ModPath.t}

type constraint_ =
  | Named of ModPath.t
  | Requirements of signature

and signature = {
  signature : ModPath.t;
  parameters : ModPath.t list;
  items : item list;
}

and item =
  | Requirement of requirement
  | Nested of ModPath.t * constraint_

type t =
  | Alias of {base : ModPath.t; refinements : (Id.t list * cpp_type) list}
  | Constraint of constraint_

let rec is_under base mp =
  ModPath.equal mp base || match mp with MPdot (parent, _) -> is_under base parent | _ -> false

let rec base_mp = function MPdot (parent, _) -> base_mp parent | mp -> mp

(* A parameter of a functor declaring a module type is an argument of its
   concept, named as itself. *)
let is_functor_param_ref r =
  let b = base_mp (Table.modpath_of_r r) in
  List.exists
    (fun (_, (_, params)) -> List.exists (ModPath.equal b) params)
    !Cpp_state.functor_concept_scopes

(* Whether [r] is a member of [M], the module the concept of the signature
   at [signature] constrains: declared in it, or reached through a functor
   parameter that is not one of the concept's own. *)
let is_member_ref signature r =
  let rmp = Table.modpath_of_r r in
  is_under signature rmp
  || match base_mp rmp with MPbound _ -> not (is_functor_param_ref r) | _ -> false

let rec concept_type signature ty =
  let args = List.map (concept_type signature) in
  match ty with
  | Tglob (r, tys, _) when (not (Table.is_custom r)) && is_member_ref signature r ->
    Member {member = r; enum = Cpp_names.is_enum_cached r; arguments = args tys}
  | Tglob (r, [], _) when (not (Table.is_custom r)) && is_functor_param_ref r -> Parameter ty
  | Tglob (r, tys, _) -> (
    match Table.find_custom_opt r with
    | Some custom -> Foreign (Foreign_template.custom_template_with_args custom (List.length tys), args tys)
    | None -> Global (r, args tys) )
  | Tshared_ptr ty -> Shared_pointer (concept_type signature ty)
  | Tvariant (storage, tys) -> Variant (storage, args tys)
  | Tnamespace (r, Tglob (r', tys, e)) when not (is_member_ref signature r) -> Namespaced (r, r', e, args tys)
  | Tnamespace (r, ty') when is_member_ref signature r -> concept_type signature ty'
  | Tfun (dom, cod) -> Function (args dom, concept_type signature cod)
  | ty -> Plain ty

let rec arrows = function
  | Tarr (arg, rest) ->
    let args, ret = arrows rest in
    (arg :: args, ret)
  | ret -> ([], ret)

let convert t = Translation_types.convert_ml_type_to_cpp_type (Common.empty_env ()) [] t

let requirements signature = function
  | Sval (r, _, _) when Table.is_inline_custom r -> []
  | Stype (r, _, _) when Table.is_inline_custom r -> []
  (* A record's projection is a data member of the record's struct, which
     [typename M::pt] already requires: a module emits no static function for
     it, and the functor body reads the field off the value. *)
  | Sval (r, _, _) when Table.is_projection r -> []
  | Sind (kn, ind) ->
    (* A parameterised inductive is a class template, which only an
       instantiation names: any one will do. *)
    Array.to_list
      (Array.mapi
         (fun i p ->
           let r = GlobRef.IndRef (kn, i) in
           Inductive_member {member = r; enum = Cpp_names.is_enum_cached r; arity = List.length p.ip_vars} )
         ind.ind_packets )
  | Sval (_, _, t) when Ml_type_util.has_tvar t -> []
  | Sval (r, _, t) -> (
    let args, ret = arrows t in
    let result = convert ret in
    match ret with
    (* A parameter whose type is a type class names an instance, which Crane
       emits as a nested struct satisfying the class's concept: a concept
       name is not a type, so the member type is asked for and
       constrained. *)
    | Tglob (cls, cls_args, _) when args = [] && Table.is_typeclass cls ->
      [ Instance_member
          { value = r;
            class_ = cls;
            arguments = List.map (fun a -> concept_type signature (convert a)) cls_args } ]
    | _ when args = [] -> [Nullary_member {value = r; result = concept_type signature result}]
    | _ ->
      let parameters = List.map (fun a -> concept_type signature (convert a)) args in
      [Function_member {value = r; parameters; result = concept_type signature result}] )
  | Stype (r, vl, _) -> [Type_member {member = r; arity = List.length vl}]

let rec constraint_of ~params = function
  | MTident kn -> Named kn
  | MTfunsig (mbid, _, mt) -> constraint_of ~params:(MPbound mbid :: params) mt
  | MTsig (mp, sign) ->
    let item (label, specif) =
      match specif with
      | Spec s -> List.map (fun r -> Requirement r) (requirements mp s)
      | Smodule (MTident kn) -> [Requirement (Submodule {label; module_type = kn})]
      | Smodule _ -> []
      | Smodtype nested -> [Nested (MPdot (mp, label), constraint_of ~params:[] nested)]
    in
    Requirements {signature = mp; parameters = params; items = List.concat_map item sign}
  | MTwith (mt, _) -> constraint_of ~params:[] mt

let rec base_concept = function
  | MTident kn -> Some kn
  | MTwith (mt, _) -> base_concept mt
  | MTfunsig _ | MTsig _ -> None

(* The [with Definition] refinements of a module type over a named one,
   innermost first. *)
let refinements mt =
  let rec go acc = function
    | MTwith (inner, ML_With_type (idl, _, typ)) -> go ((idl, convert typ) :: acc) inner
    | MTwith (inner, ML_With_module _) -> go acc inner
    | _ -> acc
  in
  go [] mt

let generate ~params mt =
  match base_concept mt with
  | Some base -> Alias {base; refinements = refinements mt}
  | None -> Constraint (constraint_of ~params mt)

(* The global references printing a concept resolves by name, each with the
   signatures visible where it is resolved: a member of one of those is
   resolved inside it. *)
let rec type_refs note = function
  | Member {arguments; _} -> List.iter (type_refs note) arguments
  | Parameter ty | Plain ty -> cpp_type_refs note ty
  | Foreign (_, args) -> List.iter (type_refs note) args
  | Global (r, args) ->
    note r;
    List.iter (type_refs note) args
  | Namespaced (r, r', _, args) ->
    note r;
    note r';
    List.iter (type_refs note) args
  | Shared_pointer ty -> type_refs note ty
  | Variant (_, tys) -> List.iter (type_refs note) tys
  | Function (dom, cod) ->
    List.iter (type_refs note) dom;
    type_refs note cod

and cpp_type_refs note ty =
  ignore
    (exists_cpp_type
       (function
         | Tglob (r, _, _) | Tnamespace (r, _) ->
           note r;
           false
         | _ -> false )
       ty
      : bool )

let requirement_refs note = function
  | Inductive_member _ | Type_member _ | Submodule _ -> ()
  | Instance_member {arguments; _} -> List.iter (type_refs note) arguments
  | Nullary_member {result; _} -> type_refs note result
  | Function_member {parameters; result; _} ->
    List.iter (type_refs note) parameters;
    type_refs note result

let rec constraint_refs ~visible note = function
  | Named _ -> ()
  | Requirements {signature; items; _} ->
    let visible = signature :: visible in
    let note r = if not (List.exists (fun s -> is_under s (Table.modpath_of_r r)) visible) then note r in
    List.iter
      (function
        | Requirement req -> requirement_refs note req
        | Nested (_, c) -> constraint_refs ~visible note c )
      items

let names_member mp c =
  let names = ref false in
  let note r = if is_under mp (Table.modpath_of_r r) then names := true in
  ( match c with
  | Alias {refinements; _} -> List.iter (fun (_, ty) -> cpp_type_refs note ty) refinements
  | Constraint c -> constraint_refs ~visible:[] note c );
  !names
