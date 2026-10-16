(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

open Names
open Miniml
open Common

type t = {
  eponymous_type : GlobRef.t option;
  eponymous_record : (GlobRef.t * record_field list * ml_ind_packet) option;
  method_candidates : Method_registry.method_candidate list;
  concept_collision : bool;
  promoted : Id.t list option;
}

let inductive_refs kn ind =
  List.init (Array.length ind.ind_packets) (fun i -> (GlobRef.IndRef (kn, i), ind.ind_packets.(i)))

(* Every eponymous packet is met in order and the last one wins, as the
   render's scan let it. *)
let eponymous ~name sel =
  let lowercase_module = String.lowercase_ascii name in
  List.fold_left
    (fun acc (_, se) ->
      match se with
      | SEdecl (Dind (kn, ind)) ->
        List.fold_left
          (fun (ty, record) (r, p) ->
            if String.lowercase_ascii (pp_global_name Type r) <> lowercase_module then (ty, record)
            else
              match ind.ind_kind with
              | TypeClass _ -> (ty, record)
              | Record fields -> (ty, Some (r, fields, p))
              | _ -> (Some r, record) )
          acc (inductive_refs kn ind)
      | _ -> acc )
    (None, None) sel

(* The functions of [sel] and [enclosing] that become methods of [epon_ref],
   newest first.  One whose type names an alias of the module or an
   inductive declared after [epon_ref] is left a function: neither is
   visible from inside the inductive's struct. *)
let method_candidates epon_ref sel ~enclosing =
  let epon_modpath = Table.modpath_of_r epon_ref in
  let same_module r = ModPath.equal (Table.modpath_of_r r) epon_modpath in
  let module_type_aliases =
    Method_registry.collect_module_type_aliases
      ~extract_decl:(fun (_, se) -> match se with SEdecl d -> Some d | _ -> None)
      epon_modpath sel
  in
  let forward_inductives =
    snd
      (List.fold_left
         (fun acc (_, se) ->
           match se with
           | SEdecl (Dind (kn, ind)) ->
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
    | Tglob (r, args, _) ->
      List.exists (globref_equal r) excluded_refs || List.exists refs_excluded args
    | Tarr (t1, t2) -> refs_excluded t1 || refs_excluded t2
    | Tmeta {contents = Some t} -> refs_excluded t
    | _ -> false
  in
  let candidates_of acc (_, se) =
    match se with
    | SEdecl d ->
      List.fold_left
        (fun acc {fd_ref = r; fd_body = body; fd_type = ty} ->
          if same_module r && not (refs_excluded ty) then
            match Cpp_state.planned_method_candidate epon_ref r body ty with
            | Some c -> c :: acc
            | None -> acc
          else acc )
        acc (Mlutil.term_defs d)
    | _ -> acc
  in
  List.fold_left candidates_of (List.fold_left candidates_of [] sel) enclosing

let concept_collision mp sel =
  let module_name = pp_module mp in
  List.exists
    (fun (_, se) ->
      match se with
      | SEdecl (Dind (kn, ind)) ->
        (match ind.ind_kind with TypeClass _ -> true | _ -> false)
        && List.exists
             (fun (r, _) -> String.equal (Cpp_names.concept_name_of_ref r) module_name)
             (inductive_refs kn ind)
      | _ -> false )
    sel

(* Only a module outside every struct, with no submodule and no other
   inductive, is promoted: promoting one with nested types would put those
   types out of reach from outside it.  The promoted variables the payloads
   name are parameters too ({!Table.ind_promoted_params}): the head spelled
   for the module is the one the inductive's struct is generated with. *)
let promoted mp sel eponymous_type =
  let has_submodules = List.exists (function _, SEmodule _ -> true | _ -> false) sel in
  let inductives = List.length (List.filter (function _, SEdecl (Dind _) -> true | _ -> false) sel) in
  match eponymous_type with
  | Some epon when (not (Scope_plan.nested mp)) && (not has_submodules) && inductives <= 1 ->
    List.find_map
      (fun (_, se) ->
        match se with
        | SEdecl (Dind (kn, ind)) ->
          List.fold_left
            (fun found (r, p) ->
              if globref_equal r epon then
                Some (Table.ind_promoted_params kn @ fst (Table.ind_param_vars ind p))
              else found )
            None (inductive_refs kn ind)
        | _ -> None )
      sel
  | _ -> None

let of_module mp ~name sel ~enclosing =
  let eponymous_type, eponymous_record = eponymous ~name sel in
  let method_candidates =
    match (eponymous_type, eponymous_record) with
    | (Some r, _ | None, Some (r, _, _))
      when not (Table.is_custom r || Table.is_enum_inductive r) ->
      method_candidates r sel ~enclosing
    | _ -> []
  in
  { eponymous_type;
    eponymous_record;
    method_candidates;
    concept_collision = concept_collision mp sel;
    promoted = promoted mp sel eponymous_type }
