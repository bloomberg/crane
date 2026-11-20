(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** Generating the concept a module type becomes.  See
    [modtype_concept_generation.mli]. *)

open Names
open Cpp_ast.Modtype_concept

(* A type translation writes for a concept, in CppIR: a concept is generated
   after its module type is settled, so every type it writes has a C++
   spelling. *)
let ir_type t = Cpp_passes.Pipeline.resolve_type ~what:"a type written outside every finished declaration" t
let ir_expr e = Cpp_passes.Pipeline.resolve_expr ~what:"a value in a module type's concept" e

(* The module path [mp] is rooted at: a file, or a bound functor parameter. *)
let rec base_mp = function MPdot (parent, _) -> base_mp parent | mp -> mp

(* A parameter of a functor declaring a module type is an argument of its
   concept, named as itself. *)
let is_functor_param_ref r =
  let b = base_mp (Base.Table.modpath_of_r r) in
  List.exists
    (fun (key, ({functor_; args} : Core_plan.Module_plan.concept_scope)) ->
      ModPath.equal key functor_ && List.exists (ModPath.equal b) args)
    !Unit_plan.Cpp_state.functor_concept_scopes

(* Whether [r] is a member of [M], the module the concept of the signature
   at [Core.Signature.t] constrains: declared in it, or reached through a functor
   parameter that is not one of the concept's own. *)
let is_member_ref signature r =
  let rmp = Base.Table.modpath_of_r r in
  is_under signature rmp
  || match base_mp rmp with MPbound _ -> not (is_functor_param_ref r) | _ -> false

(* The translated type [ty] as the requirements of the concept of the
   signature at [Core.Signature.t] spell it: [M]'s members, the functor's
   parameters and custom mappings told apart. *)
let rec concept_type cx signature (ty : Cpp_ir.Lowered.Type.t) =
  let args = List.map (concept_type cx signature) in
  match ty with
  | Entity_application (r, tys, _) when (not (Base.Table.is_custom r)) && is_member_ref signature r ->
    Member {member = r; enum = Unit_plan.Cpp_names.is_enum_cached (Lowering_state.unit_context cx) r; arguments = args tys}
  | Entity_application (r, [], _) when (not (Base.Table.is_custom r)) && is_functor_param_ref r -> Parameter (ir_type ty)
  | Entity_application (r, tys, _) -> (
    (* A typed-mapped type is written from its canonical type in the
       legacy spelling ({!Base.Mapping_plan.type_text}), so that its type
       arguments are spelled as the concept spells them: a member of [M]
       is [typename M::t]. *)
    if Base.Mapping_plan.is_type_head r then Base.Mapping_plan.note_instantiated r;
    match Base.Table.find_custom_opt r with
    | Some text ->
      let pieces = Cpp_passes.Erasure.type_pieces r text tys in
      (* A type argument the text names and the use does not supply is
         erased, as the seam writes one ({!Cpp_passes.Erasure.supply_template_args}). *)
      let arity =
        List.fold_left
          (fun n -> function Cpp_ir.Foreign.Type_argument i | Element (i, _) -> max n (i + 1) | _ -> n)
          0 pieces
      in
      let supplied = args tys in
      let erased = List.init (max 0 (arity - List.length supplied)) (fun _ -> Plain Any) in
      Foreign {custom = r; pieces; arguments = supplied @ erased}
    | None -> Global (r, args tys) )
  | Shared_pointer ty -> Shared_pointer (concept_type cx signature ty)
  | Variant (storage, tys) -> Variant (storage, args tys)
  | In_namespace (r, Entity_application (r', tys, e)) when not (is_member_ref signature r) ->
    Namespaced (r, r', List.map ir_expr e, args tys)
  | In_namespace (r, ty') when is_member_ref signature r -> concept_type cx signature ty'
  | Function (dom, cod) -> Function (args dom, concept_type cx signature cod)
  | ty -> Plain (ir_type ty)

(* The domains and codomain of a Core arrow type. *)
let rec arrows = function
  | Core.Type.Arrow {parameter = arg; result = rest} ->
    let args, ret = arrows rest in
    (arg :: args, ret)
  | ret -> ([], ret)

(* A Core type as translation converts it, outside any function. *)
let convert cx t = Types.cpp_ir_of_core_type cx (Base.Common.empty_env ()) [] t

(* The requirements one specification of the signature at [Core.Signature.t]
   asks of [M]; none for an inline custom, whose mapping stands in for the
   member. *)
let requirements cx signature = function
  | Core.Signature.Declaration.Value {entity = r; _} when Base.Table.is_inline_custom r -> []
  | Core.Signature.Declaration.Type {entity = r; _} when Base.Table.is_inline_custom r -> []
  (* A record's projection is a data member of the record's struct, which
     [typename M::pt] already requires: a module emits no static function for
     it, and the functor body reads the field off the value. *)
  | Core.Signature.Declaration.Value {entity = r; _} when Base.Table.is_projection r -> []
  | Core.Signature.Declaration.Inductive {entity = kn; definition = (ind : Core.Inductive.t)} ->
    (* A parameterised inductive is a class template, which only an
       instantiation names: any one will do. *)
    Array.to_list
      (Array.mapi
         (fun i (p : Core.Inductive.Packet.t) ->
           let r = GlobRef.IndRef (kn, i) in
           Inductive_member
             { member = r;
               enum = Unit_plan.Cpp_names.is_enum_cached (Lowering_state.unit_context cx) r;
               arity = List.length p.type_variables } )
         ind.packets )
  (* A polymorphic value is a member template, which a requires-expression
     cannot name without choosing its arguments: it asks nothing. *)
  | Core.Signature.Declaration.Value {type_ = t; _} when Base.Type_util.has_tvar t -> []
  | Core.Signature.Declaration.Value {entity = r; type_ = t; _} -> (
    let args, ret = arrows t in
    let result = convert cx ret in
    match ret with
    (* A parameter whose type is a type class names an instance, which Crane
       emits as a nested struct satisfying the class's concept: a concept
       name is not a type, so the member type is asked for and
       constrained. *)
    | Core.Type.Global_app {head = cls; type_arguments = cls_args; _} when args = [] && Base.Table.is_typeclass cls ->
      [ Instance_member
          { value = r;
            class_ = cls;
            arguments = List.map (fun a -> concept_type cx signature (convert cx a)) cls_args } ]
    | _ when args = [] -> [Nullary_member {value = r; result = concept_type cx signature result}]
    | _ ->
      let parameters = List.map (fun a -> concept_type cx signature (convert cx a)) args in
      [Function_member {value = r; parameters; result = concept_type cx signature result}] )
  | Core.Signature.Declaration.Type {entity = r; parameters = vl; _} ->
    [Type_member {member = r; arity = List.length vl}]

let rec constraint_of cx ~params = function
  | Core.Module.Type.Path kn -> Named kn
  | Core.Module.Type.Functor {parameter = mbid; result = mt; _} -> constraint_of cx ~params:(MPbound mbid :: params) mt
  | Core.Module.Type.Signature {path = mp; items = sign} ->
    let item (label, specif) =
      match specif with
      | Core.Module.Signature_item.Declaration s -> List.map (fun r -> Requirement r) (requirements cx mp s)
      | Core.Module.Signature_item.Module (Core.Module.Type.Path kn) ->
        [Requirement (Submodule {label; module_type = kn})]
      | Core.Module.Signature_item.Module _ -> []
      | Core.Module.Signature_item.Module_type nested -> [Nested (MPdot (mp, label), constraint_of cx
        ~params:[] nested)]
    in
    Requirements {signature = mp; parameters = params; items = List.concat_map item sign}
  | Core.Module.Type.Refined {base = mt; _} -> constraint_of cx ~params:[] mt

(* The named module type a module type refines, if it is one. *)
let rec base_concept = function
  | Core.Module.Type.Path kn -> Some kn
  | Core.Module.Type.Refined {base = mt; _} -> base_concept mt
  | Core.Module.Type.Functor _ | Core.Module.Type.Signature _ -> None

(* The [with Definition] refinements of a module type over a named one,
   innermost first. *)
let refinements cx mt =
  let rec go acc = function
    | Core.Module.Type.Refined {base = inner;
                                refinement = Core.Module.Refinement.Type_equation {path = idl; definition = typ; _}} ->
      go ((idl, ir_type (Cpp_passes.Erasure.instantiate_type (Lowering_state.unit_context cx) (convert cx typ))) ::
        acc) inner
    | Core.Module.Type.Refined {base = inner; refinement = Core.Module.Refinement.Module_equation _} -> go acc inner
    | _ -> acc
  in
  go [] mt

let generate cx ~params mt =
  match base_concept mt with
  | Some base -> Alias {base; refinements = refinements cx mt}
  | None -> Constraint (constraint_of cx ~params mt)
