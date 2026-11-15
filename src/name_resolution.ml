(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

(** A per-extraction cache of how each inductive type is rendered.  See
    [name_resolution.mli].

    IMPORTANT: This module must NOT call Common.pp_global or
    Common.pp_global_name during [create], because those functions have side
    effects on the Common.ml renaming tables. Calling them at cache-creation
    time (before normal rendering) would trigger premature renaming entries and
    produce different output. *)

open Names
open Table
module Kind = Cpp_ir.Inductive.Kind

(** Name resolution cache: the inductive kind of each scanned inductive,
    indexed by GlobRef. *)
type t = {ind_kinds : Kind.t Ref.User.Tbl.t}

(** Checks if a reference is an eponymous record type. Eponymous records flatten
    their single constructor into the parent namespace. *)
let is_eponymous _ r = Module_plan.is_eponymous_record r

(** Checks if a reference is a globally-scoped enum. Global-scope enums have
    their variants hoisted to the parent namespace. *)
let is_global_scope_enum _ r = Module_plan.is_global_scope_enum r

(** Retrieves the inductive kind classification for a type reference. Returns
    None if the reference is not an inductive type. *)
let get_ind_kind t r = Ref.User.Tbl.find_opt t.ind_kinds r

(** Classifies packet [i] of an inductive using side-effect-free queries. *)
let classify_inductive (kn : MutInd.t) (i : int) (ind : Core.Inductive.t) : Kind.t =
  let ind_ref = GlobRef.IndRef (kn, i) in
  match ind.Core.Inductive.kind with
  | Core.Inductive.Kind.Inductive | Core.Inductive.Kind.Coinductive ->
    if is_enum_inductive ind_ref then Enum else Sum
  | Core.Inductive.Kind.Record fields ->
    let projections = List.map (fun (f : Core.Record.Field.t) -> f.projection) fields in
    if Module_plan.is_eponymous_record ind_ref then Eponymous_record projections
    else Record projections
  | Core.Inductive.Kind.Type_class fields ->
    Type_class (List.map (fun (f : Core.Record.Field.t) -> f.projection) fields)

(** Creates a name resolution cache from a Core structure. Pre-computes type
    classifications for every inductive at top level or in a module structure,
    without side effects. *)
let create s =
  let ind_kinds = Ref.User.Tbl.create 64 in
  (* Pre-classify all inductive types using side-effect-free queries only. We do
     NOT call pp_global_name or pp_global here: those have side effects on
     Common.ml's renaming tables that would change the output. *)
  let rec scan_sel sel =
    List.iter
      (fun (_l, se) ->
        match se with
        | Core.Module.Structure_item.Declaration (Core.Decl.Inductive {entity = kn; definition = ind}) ->
          Array.iteri
            (fun i _p ->
              Ref.User.Tbl.replace ind_kinds (GlobRef.IndRef (kn, i)) (classify_inductive kn i ind) )
            ind.Core.Inductive.packets
        | Core.Module.Structure_item.Module m ->
          ( match m.Core.Module.expr with
          | Core.Module.Expr.Structure {path = _mp; items = inner_sel} -> scan_sel inner_sel
          | _ -> () )
        | _ -> () )
      sel
  in
  List.iter (fun (_mp, sel) -> scan_sel sel) s;
  {ind_kinds}
