(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)

open Names
open Minicpp

(** Every global reference a member names, in its signature or its body. *)
let field_refs (f : cpp_field) : GlobRef.Set.t =
  let acc = ref GlobRef.Set.empty in
  let note r = acc := GlobRef.Set.add r !acc in
  let ty t =
    ignore
      (map_cpp_type
         (fun t ->
           ( match t with
           | Tglob (r, _, _) | Tnamespace (r, _) -> note r
           | _ -> () );
           t )
         t );
    t
  in
  let rec ex e =
    ( match e with
    | CPPglob (r, _, _) | CPPnamespace (r, _) | CPPstructmk (r, _, _)
    | CPPget' (_, r) -> note r
    | CPPconcept_app (r1, r2, _) -> note r1; note r2
    | _ -> () );
    map_expr ex st ty e
  and st s = map_stmt ex st ty s in
  ignore (map_field ex st ty (f, VPublic, SNoTag));
  !acc

(** [split_struct ~group d] is [d] with the members that name a type of
    [group] left as declarations, paired with their definitions, to be written
    once every struct in [group] is complete.

    A mutually recursive group of inductives has no order in which each struct
    can be written whole: [Tree::leaf] takes a [List<Branch>] by value, which
    needs [Branch] complete, and [Branch::branch0] takes a [Tree] the same
    way.  A member that names no sibling is left where it is -- both because
    it does not have to move, and because moving it would take its return type
    out of the struct's scope, where a nested name like [variant_t] no longer
    resolves. *)
let rec split_struct ~(group : GlobRef.Set.t) (d : cpp_decl) :
    cpp_decl * cpp_decl list =
  match d with
  | Dtemplate (tps, cstr, inner) ->
    let inner, defs = split_struct ~group inner in
    (Dtemplate (tps, cstr, inner), defs)
  | Dnspace (r, decls) ->
    let decls, defs =
      List.fold_right
        (fun d (decls, defs) ->
          let d, ds = split_struct ~group d in
          (d :: decls, ds @ defs) )
        decls ([], [])
    in
    (Dnspace (r, decls), defs)
  | Dstruct ds ->
    let defs = ref [] in
    let fields =
      List.map
        (fun (f, vis, tag) ->
          match f with
          | (Fmethod _ | Fdestructor _)
            when GlobRef.Set.exists (fun r -> GlobRef.Set.mem r group) (field_refs f) ->
            defs :=
              Dmember_def
                {dm_owner = ds.ds_ref; dm_tparams = ds.ds_tparams; dm_field = f}
              :: !defs;
            (Fmember_decl f, vis, tag)
          | _ -> (f, vis, tag) )
        ds.ds_fields
    in
    (Dstruct {ds with ds_fields = fields}, List.rev !defs)
  | _ -> (d, [])

let split_group (decls : cpp_decl list) : cpp_decl list =
  let group =
    List.fold_left
      (fun acc d ->
        match decl_globref d with
        | Some r -> GlobRef.Set.add r acc
        | None -> acc )
      GlobRef.Set.empty decls
  in
  let structs, defs =
    List.fold_right
      (fun d (structs, defs) ->
        let d, ds = split_struct ~group d in
        (d :: structs, ds @ defs) )
      decls ([], [])
  in
  structs @ defs
