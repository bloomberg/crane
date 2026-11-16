(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** The concept a module type becomes.  See [modtype_concept.mli]. *)

open Names

module Ir = Cpp_ir.Resolved

type concept_type =
  | Member of {member : GlobRef.t; enum : bool; arguments : concept_type list}
  | Parameter of Ir.Type.t
  | Foreign of {custom : GlobRef.t; pieces : Cpp_ir.Foreign.piece list; arguments : concept_type list}
  | Global of GlobRef.t * concept_type list
  | Namespaced of GlobRef.t * GlobRef.t * Ir.Expr.t list * concept_type list
  | Shared_pointer of concept_type
  | Variant of Cpp_ir.Type.Variant_storage.t * concept_type list
  | Function of concept_type list * concept_type
  | Plain of Ir.Type.t

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
  | Alias of {base : ModPath.t; refinements : (Id.t list * Ir.Type.t) list}
  | Constraint of constraint_

(* Whether [mp] is [base] or a module path inside it. *)
let rec is_under base mp =
  ModPath.equal mp base || match mp with MPdot (parent, _) -> is_under base parent | _ -> false

(* The global references printing a concept resolves by name, each with the
   signatures visible where it is resolved: a member of one of those is
   resolved inside it. *)
let rec type_refs note = function
  | Member {arguments; _} -> List.iter (type_refs note) arguments
  | Parameter ty | Plain ty -> cpp_type_refs note ty
  | Foreign {arguments; _} -> List.iter (type_refs note) arguments
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

and cpp_type_refs note (ty : Ir.Type.t) =
  ( match ty with
  | Entity_application (r, _, _) | Foreign {custom = r; _} | In_namespace (r, _) -> note r
  | _ -> () );
  Cpp_ir.Children.type_children (cpp_type_refs note) ty

(* {!type_refs} of the types one requirement writes. *)
let requirement_refs note = function
  | Inductive_member _ | Type_member _ | Submodule _ -> ()
  | Instance_member {arguments; _} -> List.iter (type_refs note) arguments
  | Nullary_member {result; _} -> type_refs note result
  | Function_member {parameters; result; _} ->
    List.iter (type_refs note) parameters;
    type_refs note result

(* {!type_refs} of a constraint's requirements, a reference to a member of a
   signature in [visible] or nested in it not noted. *)
let rec constraint_refs ~visible note = function
  | Named _ -> ()
  | Requirements {signature; items; _} ->
    let visible = signature :: visible in
    let note r = if not (List.exists (fun s -> is_under s (Base.Table.modpath_of_r r)) visible) then note r in
    List.iter
      (function
        | Requirement req -> requirement_refs note req
        | Nested (_, c) -> constraint_refs ~visible note c )
      items

let names_member mp c =
  let names = ref false in
  let note r = if is_under mp (Base.Table.modpath_of_r r) then names := true in
  ( match c with
  | Alias {refinements; _} -> List.iter (fun (_, ty) -> cpp_type_refs note ty) refinements
  | Constraint c -> constraint_refs ~visible:[] note c );
  !names
