(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(* Pre-computed C++ name resolution cache.
   See name_resolution.mli for documentation.

   IMPORTANT: This module must NOT call Common.pp_global or Common.pp_global_name
   during [create], because those functions have side effects on the Common.ml
   renaming tables. Calling them at cache-creation time (before normal rendering)
   would trigger premature renaming entries and produce different output. *)

open Names
open Minicpp
open Table

type resolved_type_name = {
  rtn_display : string;
  rtn_is_eponymous : bool;
  rtn_is_record : bool;
  rtn_is_enum : bool;
  rtn_is_local : bool;
  rtn_is_merged : bool;
  rtn_is_global_scope_enum : bool;
}

type resolved_term_name = {
  rtm_display : string;
  rtm_wrapper_qualified : bool;
}

type t = {
  type_names : (GlobRef.t, resolved_type_name) Hashtbl.t;
  eponymous_set : (GlobRef.t, unit) Hashtbl.t;
  global_scope_enum_set : (GlobRef.t, unit) Hashtbl.t;
  ind_kinds : (GlobRef.t, cpp_ind_kind) Hashtbl.t;
}

let resolve_type t r = Hashtbl.find_opt t.type_names r
let resolve_term _t _r = None  (* term names not pre-computed — see note above *)
let register_type t r name = Hashtbl.replace t.type_names r name
let register_term _t _r _name = ()
let is_eponymous t r = Hashtbl.mem t.eponymous_set r
let is_global_scope_enum t r = Hashtbl.mem t.global_scope_enum_set r
let get_ind_kind t r = Hashtbl.find_opt t.ind_kinds r
let register_ind_kind t r kind = Hashtbl.replace t.ind_kinds r kind

(* Classify an inductive type using only side-effect-free queries.
   We use the raw ip_typename from the packet and the ind_kind from miniml
   to compute classification flags without calling pp_global_name. *)
let classify_inductive
    ~eponymous_records ~global_scope_enums ~unmerged
    (kn : MutInd.t) (i : int) (ind : Miniml.ml_ind) : unit -> (GlobRef.t * resolved_type_name * cpp_ind_kind) =
  let ind_ref = GlobRef.IndRef (kn, i) in
  let p = ind.Miniml.ind_packets.(i) in
  let raw_name = Id.to_string p.Miniml.ip_typename in
  let is_eponymous = Hashtbl.mem eponymous_records ind_ref in
  let is_rec = match ind.Miniml.ind_kind with
    | Miniml.Record _ -> true
    | Miniml.TypeClass _ -> true  (* type classes are also records *)
    | _ -> false
  in
  let is_en = is_enum_inductive ind_ref in
  let is_merged = not (Hashtbl.mem unmerged (String.capitalize_ascii raw_name)) in
  let is_gse = Hashtbl.mem global_scope_enums ind_ref in
  let kind = match ind.Miniml.ind_kind with
    | Miniml.Standard | Miniml.Coinductive ->
      if is_en then IK_Enum
      else IK_Standard
    | Miniml.Record fields ->
      if is_eponymous then IK_Eponymous fields
      else IK_Record fields
    | Miniml.TypeClass fields -> IK_TypeClass fields
  in
  let rtn = {
    rtn_display = raw_name;  (* raw name — display rendering uses pp_global at render time *)
    rtn_is_eponymous = is_eponymous;
    rtn_is_record = is_rec;
    rtn_is_enum = is_en;
    rtn_is_local = false;
    rtn_is_merged = is_merged;
    rtn_is_global_scope_enum = is_gse;
  } in
  fun () -> (ind_ref, rtn, kind)

let create ~structure_analysis:_ ~wrapper_modules:_ ~collision_wrappers:_
    ~global_scope_enums ~eponymous_records ~unmerged s =
  let type_names = Hashtbl.create 256 in
  let eponymous_set = Hashtbl.copy eponymous_records in
  let global_scope_enum_set = Hashtbl.copy global_scope_enums in
  let ind_kinds = Hashtbl.create 64 in
  (* Pre-classify all inductive types using side-effect-free queries only.
     We do NOT call pp_global_name or pp_global here — those have side effects
     on Common.ml's renaming tables that would change the output. *)
  let rec scan_sel sel =
    List.iter (fun (_l, se) ->
      match se with
      | Miniml.SEdecl (Miniml.Dind (kn, ind)) ->
        Array.iteri (fun i _p ->
          let thunk = classify_inductive
            ~eponymous_records ~global_scope_enums ~unmerged kn i ind in
          let (ind_ref, rtn, kind) = thunk () in
          Hashtbl.replace type_names ind_ref rtn;
          Hashtbl.replace ind_kinds ind_ref kind
        ) ind.Miniml.ind_packets
      | Miniml.SEmodule m ->
        (match m.Miniml.ml_mod_expr with
         | Miniml.MEstruct (_mp, inner_sel) -> scan_sel inner_sel
         | _ -> ())
      | _ -> ()
    ) sel
  in
  List.iter (fun (_mp, sel) -> scan_sel sel) s;
  { type_names; eponymous_set; global_scope_enum_set; ind_kinds }
