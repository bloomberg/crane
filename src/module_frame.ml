(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

open Names
open Base.Common

type t = Cpp_state.module_frame = {
  eponymous_type : GlobRef.t option;
  eponymous_record : (GlobRef.t * Core.Record.Field.t list * Core.Inductive.Packet.t) option;
  method_candidates : Method_registry.method_candidate list;
  concept_collision : bool;
  promoted : Id.t list option;
}

let inductive_refs kn (ind : Core.Inductive.t) =
  List.init (Array.length ind.packets) (fun i -> (GlobRef.IndRef (kn, i), ind.packets.(i)))

(* Every eponymous packet is met in order and the last one wins, as the
   render's scan let it. *)
let eponymous ~name sel =
  let lowercase_module = String.lowercase_ascii name in
  List.fold_left
    (fun acc (_, se) ->
      match se with
      | Core.Module.Structure_item.Declaration (Core.Decl.Inductive {entity = kn; definition = ind}) ->
        List.fold_left
          (fun (ty, record) (r, p) ->
            if String.lowercase_ascii (pp_global_name Type r) <> lowercase_module then (ty, record)
            else
              match ind.kind with
              | Core.Inductive.Kind.Type_class _ -> (ty, record)
              | Core.Inductive.Kind.Record fields -> (ty, Some (r, fields, p))
              | _ -> (Some r, record) )
          acc (inductive_refs kn ind)
      | _ -> acc )
    (None, None) sel

(* The functions of [sel] and [enclosing] that become methods of [epon_ref],
   newest first.  One whose type names an alias of the module or an
   inductive declared after [epon_ref] is left a function: neither is
   visible from inside the inductive's struct. *)
let method_candidates epon_ref sel ~enclosing =
  let epon_modpath = Base.Table.modpath_of_r epon_ref in
  let same_module r = ModPath.equal (Base.Table.modpath_of_r r) epon_modpath in
  let module_type_aliases =
    Method_registry.collect_module_type_aliases
      ~extract_decl:(fun (_, se) -> match se with Core.Module.Structure_item.Declaration d -> Some d | _ -> None)
      epon_modpath sel
  in
  let forward_inductives =
    snd
      (List.fold_left
         (fun acc (_, se) ->
           match se with
           | Core.Module.Structure_item.Declaration (Core.Decl.Inductive {entity = kn; definition = ind}) ->
             List.fold_left
               (fun (seen, fwd) (r, _) ->
                 if globref_equal r epon_ref then (true, fwd)
                 else if seen then (seen, r :: fwd)
                 else (seen, fwd) )
               acc (inductive_refs kn ind)
           | _ -> acc )
         (false, []) sel )
  in
  let excluded_refs = module_type_aliases @ forward_inductives in
  let rec refs_excluded = function
    | Core.Type.Global_app {head = r; type_arguments = args; _} ->
      List.exists (globref_equal r) excluded_refs || List.exists refs_excluded args
    | Core.Type.Arrow {parameter = t1; result = t2} -> refs_excluded t1 || refs_excluded t2
    | Core.Type.Meta {contents = Some t} -> refs_excluded t
    | _ -> false
  in
  let candidates_of acc (_, se) =
    match se with
    | Core.Module.Structure_item.Declaration d ->
      List.fold_left
        (fun acc {Core.Recursion.Definition.entity = r; body = body; type_ = ty} ->
          if same_module r && not (refs_excluded ty) then
            match Cpp_state.planned_method_candidate epon_ref r body ty with
            | Some c -> c :: acc
            | None -> acc
          else acc )
        acc (Base.Core_util.term_defs d)
    | _ -> acc
  in
  let candidates = List.fold_left candidates_of (List.fold_left candidates_of [] sel) enclosing in
  (* The registry's scan decides what every call is written as, and the
     frame what the type's struct is given: a function of the module the
     scan made a method of the type and the frame does not is called as a
     method nothing declares. *)
  if Base.Probe.checking () then
    List.iter
      (fun (_, se) ->
        match se with
        | Core.Module.Structure_item.Declaration d ->
          List.iter
            (fun {Core.Recursion.Definition.entity = r; _} ->
              match Cpp_state.is_registered_method r with
              | Some (e, _)
                when same_module r && globref_equal e epon_ref
                     && not (List.exists (fun (r', _, _, _) -> globref_equal r r') candidates) ->
                Base.Probe.violation "method registry"
                  Pp.(
                    str "the registry's scan made " ++ GlobRef.print r ++ str " a method of " ++ GlobRef.print epon_ref
                    ++ str ", which its module's frame does not" )
              | _ -> () )
            (Base.Core_util.term_defs d)
        | _ -> () )
      sel;
  candidates

(* The names compared are the ones planned, not the ones a reference
   spells: those depend on where the reference is written from. *)
let concept_collision layout mp sel =
  let concept_name r =
    match Module_plan.concept_name layout r with Some name -> Some name | None -> Base.Common.decided_global_name r
  in
  List.exists
    (fun (_, se) ->
      match se with
      | Core.Module.Structure_item.Declaration
        (Core.Decl.Inductive
          {entity = kn; definition = ({Core.Inductive.kind = Core.Inductive.Kind.Type_class _; _} as ind)}) ->
        List.exists
          (fun (r, _) -> Option.equal String.equal (concept_name r) (Some (Base.Common.emitted_module_name mp)))
          (inductive_refs kn ind)
      | _ -> false )
    sel

(* Only a module outside every struct, with no submodule and no other
   inductive, is promoted: promoting one with nested types would put those
   types out of reach from outside it.  An enum is never promoted: its
   declaration is an [enum class], not members a struct can take over.  The
   promoted variables the payloads
   name are parameters too ({!Base.Table.ind_promoted_params}): the head spelled
   for the module is the one the inductive's struct is generated with. *)
let promoted scopes mp sel eponymous_type =
  let has_submodules = List.exists (function _, Core.Module.Structure_item.Module _ -> true | _ -> false) sel in
  let inductives =
    List.length
      (List.filter
        (function _, Core.Module.Structure_item.Declaration (Core.Decl.Inductive _) -> true | _ -> false) sel) in
  match eponymous_type with
  | Some epon when (not (Scope_plan.nested scopes mp)) && (not has_submodules) && inductives <= 1 ->
    List.find_map
      (fun (_, se) ->
        match se with
        | Core.Module.Structure_item.Declaration (Core.Decl.Inductive {entity = kn; definition = ind}) ->
          List.fold_left
            (fun found (r, p) ->
              if globref_equal r epon && not (Base.Table.is_enum_inductive r) then
                Some (Base.Table.ind_promoted_params kn @ fst (Base.Table.ind_param_vars ind p))
              else found )
            None (inductive_refs kn ind)
        | _ -> None )
      sel
  | _ -> None

let of_module (u : Unit_context.t) mp ~name sel ~enclosing =
  let eponymous_type, eponymous_record = eponymous ~name sel in
  let method_candidates =
    match (eponymous_type, eponymous_record) with
    | (Some r, _ | None, Some (r, _, _))
      when not (Base.Table.is_custom r || Base.Table.is_enum_inductive r) ->
      method_candidates r sel ~enclosing
    | _ -> []
  in
  { eponymous_type;
    eponymous_record;
    method_candidates;
    concept_collision = concept_collision u.modules mp sel;
    promoted = promoted u.scopes mp sel eponymous_type }

let equal a b =
  let ref_equal = Option.equal GlobRef.UserOrd.equal in
  ref_equal a.eponymous_type b.eponymous_type
  && ref_equal
       (Option.map (fun (r, _, _) -> r) a.eponymous_record)
       (Option.map (fun (r, _, _) -> r) b.eponymous_record)
  && List.equal
       (fun (r, _, _, i) (r', _, _, i') -> GlobRef.UserOrd.equal r r' && Int.equal i i')
       a.method_candidates b.method_candidates
  && Bool.equal a.concept_collision b.concept_collision
  && Option.equal (List.equal Id.equal) a.promoted b.promoted

let planned (plans : Cpp_state.plans) mp =
  match MPmap.find_opt mp plans.frames with
  | Some frame -> frame
  | None ->
    CErrors.anomaly
      Pp.(str "Crane: the module " ++ str (ModPath.to_string mp) ++ str " has no planned frame.")

let frames_around scopes mp =
  match Scope_plan.frames scopes mp with
  | Some frames -> frames
  | None ->
    CErrors.anomaly
      Pp.(str "Crane: the body of the module " ++ str (ModPath.to_string mp) ++ str " has no planned frames.")

let demoted_around plans scopes mp =
  List.filter_map
    (fun m ->
      let frame = planned plans m in
      if Option.has_some frame.promoted then None else frame.eponymous_type )
    (frames_around scopes mp)
